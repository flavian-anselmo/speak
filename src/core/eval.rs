use self::value::{Function, Value};
use super::{
    error::{Err, ErrorReason},
    lexer::{tokenize, Kind, Tok},
    log::{log_debug, log_err},
    parser::{parse, Node},
    runtime::{self, StackFrame, VTable},
};
use std::{collections::HashMap, env, fmt, fs, io::BufReader, sync::mpsc::channel};

pub mod r#type {
    #[derive(Debug, PartialEq, Eq, Clone)]
    pub enum Type {
        /// Floating point number: f64
        Number,

        /// Boolean type.
        Bool,

        /// String type.
        String,

        // Function type.
        Function,

        // Empty type.
        Empty,
    }

    // type aliases
    impl Type {
        pub fn string(&self) -> String {
            match self {
                Type::Number => "number".to_string(),
                Type::Bool => "bool".to_string(),
                Type::String => "string".to_string(),
                Type::Function => "function".to_string(),
                Type::Empty => "empty".to_string(),
            }
        }
    }
}

pub mod value {
    use super::r#type::Type;
    use crate::core::{
        parser::Node,
        runtime::{NativeFn, VTable, MAX_PRINT_LEN},
    };
    use std::fmt::Debug;

    /// Value represents any value in the Speak programming language.
    /// Each value corresponds to some primitive or object value created
    /// during the execution of a Speak program.
    #[derive(Debug, Clone)]
    pub enum Value {
        Number(f64),
        Bool(bool),
        String(String),

        /// This is the value of any variables referencing functions
        /// defined in a Speak program.
        Function(Function),

        /// This is a function whose implementation is written in rust and
        /// is part of the interpreter.
        NativeFunction(NativeFn),

        /// This is an internal representation of a lazy
        /// function evaluation used to implement tail call optimization.
        FunctionCallThunk {
            vt: VTable,
            func: Function,
        },

        Empty,
    }

    #[derive(Debug, Clone)]
    pub struct Function {
        // defn must be of variant `FunctionLiteral`.
        pub defn: Box<Node>,
    }

    impl Function {
        fn string(&self) -> String {
            let func_str = self.defn.string();
            if func_str.len() > MAX_PRINT_LEN {
                return format!("{}..", &func_str[..MAX_PRINT_LEN]);
            }

            return func_str;
        }
    }

    impl Value {
        pub fn value_type(&self) -> Type {
            match self {
                Value::Number(_) => Type::Number,
                Value::Bool(_) => Type::Bool,
                Value::String(_) => Type::String,
                Value::Function { .. }
                | Value::FunctionCallThunk { .. }
                | Value::NativeFunction(..) => Type::Function,
                Value::Empty => Type::Empty,
            }
        }

        pub fn equals(&self, value: Value) -> bool {
            match (self, value) {
                (Value::Number(a), Value::Number(b)) => a == &b,
                (Value::Bool(a), Value::Bool(b)) => a == &b,
                (Value::String(a), Value::String(b)) => a == &b,
                (Value::Empty, _) | (_, Value::Empty) => true,
                _ => false, // types here are incomparable
            }
        }

        pub fn string(&self) -> String {
            match self {
                Value::Number(value) => value.to_string(),
                Value::Bool(value) => value.to_string(),
                Value::String(value) => value.to_string(),
                Value::Function(func) => func.string(),
                Value::NativeFunction(func) => format!("Native Function ({})", func.0),
                Value::FunctionCallThunk { func, .. } => {
                    format!("Thunk of ({})", func.string())
                }
                Value::Empty => "()".to_string(),
            }
        }
    }
}

impl Node {
    pub fn eval(&mut self, stack: &mut StackFrame, allow_thunk: bool) -> Result<Value, Err> {
        match self {
            Node::NumberLiteral { value, .. } => Ok(Value::Number(*value)),
            Node::StringLiteral { value, .. } => Ok(Value::String(value.clone())), // Tidy: this is a copy
            Node::BoolLiteral { value, .. } => Ok(Value::Bool(value.clone())), // Tidy: this is a copy
            Node::EmptyIdentifier { .. } => Ok(Value::Empty),
            Node::Identifier { value, position } => {
                if let Some(val) = stack.get(&value) {
                    return Ok(val.clone());
                }
                Err(Err {
                    message: format!("{} is not defined [{}]", value, position.string()),
                    reason: ErrorReason::System,
                })
            }
            Node::UnaryExpression {
                operator,
                operand,
                position,
            } => {
                let mut_operand = |op: &mut Node| -> Result<Value, Err> {
                    match op {
                        Node::NumberLiteral { value, .. } => {
                            *value = -*value;
                            Ok(Value::Number(value.clone()))
                        }
                        Node::BoolLiteral { value, .. } => {
                            *value = !*value;
                            Ok(Value::Bool(value.clone()))
                        }
                        _ => unimplemented!("should not evalute to a identifier"),
                    }
                    // Ok(())
                };

                let cl_operand = operand.as_ref();
                match operator {
                    Kind::NegationOp => match cl_operand {
                        Node::NumberLiteral { .. } | Node::BoolLiteral { .. } => {
                            Ok(mut_operand(operand)?)
                        }

                        Node::Identifier { value, position } => {
                            if let Some(_val) = stack.get(value) {
                                return Ok(mut_operand(operand)?);
                            }
                            return Err(Err {
                                message: format!(
                                    "{} is not defined [{}]",
                                    value,
                                    position.string()
                                ),
                                reason: ErrorReason::System,
                            });
                        }
                        _ => {
                            return Err(Err {
                                message: format!(
                                    "invalid unary operand {}, at {}",
                                    operand.string(),
                                    position.string()
                                ),
                                reason: ErrorReason::Syntax,
                            })
                        }
                    },

                    _ => {
                        return Err(Err {
                            message: format!(
                                "invalid unary operator {}, at {}",
                                operator.string(),
                                position.string()
                            ),
                            reason: ErrorReason::Syntax,
                        });
                    }
                }
            }
            Node::BinaryExpression { .. } => eval_binary_expr_node(&self, stack, &allow_thunk),
            Node::FunctionCall {
                function,
                arguments,
                ..
            } => {
                let mut arg_results = Vec::new();
                for arg in arguments {
                    arg_results.push(arg.eval(stack, false)?);
                }

                let fn_value = &function.eval(stack, false)?;
                eval_speak_function(stack, fn_value, allow_thunk, &arg_results)
            }
            Node::FunctionLiteral { .. } => Ok(Value::Function(Function {
                defn: Box::new(self.clone()),
            })),
            // _Node::IfExprNode { .. } => {
            //     unimplemented!()
            // }
        }
    }
}

fn eval_binary_expr_node(
    node: &Node,
    stack: &mut StackFrame,
    _allow_thunk: &bool,
) -> Result<Value, Err> {
    if let Node::BinaryExpression {
        operator,
        left_operand,
        right_operand,
        position,
    } = node
    {
        let mut left_right = || -> Result<(Value, Value), Err> {
            Ok((
                to_value(left_operand, stack)?,
                to_value(right_operand, stack)?,
            ))
        };

        match operator {
            Kind::AssignOp => {
                match left_operand.as_ref() {
                    Node::Identifier { value, .. } => {
                        // right operand node must evaluate to a value
                        let right_value = to_value(right_operand, stack)?;
                        stack.set(value.clone(), right_value.clone());
                        return Ok(right_value);
                    }

                    Node::BinaryExpression {
                        operator: _l_operator,
                        left_operand: _l_left_operand,
                        right_operand: _l_right_operand,
                        position: _l_position,
                    } => {
                        unimplemented!() // method access
                    }

                    _ => {
                        let mut left_operand = left_operand.as_ref().clone();
                        return Err(Err {
                            message: format!(
                                "cannot assing value to non-identifier {}, at [{}]",
                                left_operand.eval(stack, false)?.string(),
                                left_operand.position().string()
                            ),
                            reason: ErrorReason::Runtime,
                        });
                    }
                }
            }

            Kind::AccessorOp => {
                todo!()
            }

            Kind::AddOp => {
                let (left_value, right_value) = left_right()?;
                match left_value {
                    Value::Number(left_num) => {
                        if let Value::Number(right_num) = right_value {
                            return Ok(Value::Number(left_num + right_num));
                        }
                    }

                    Value::String(left_str) => {
                        if let Value::String(right_str) = right_value {
                            return Ok(Value::String(format!("{}{}", left_str, right_str)));
                        }
                    }

                    Value::Bool(left_bool) => {
                        if let Value::Bool(right_bool) = right_value {
                            return Ok(Value::Bool(left_bool || right_bool));
                        }
                    }

                    _ => {
                        return Err(Err {
                            message: format!(
                                "values {} and {} do not support addition, at [{}]",
                                left_value.string(),
                                right_value.string(),
                                position.string()
                            ),
                            reason: ErrorReason::Syntax,
                        })
                    }
                }
            }

            Kind::SubtractOp => {
                let (left_value, right_value) = left_right()?;
                match left_value {
                    Value::Number(left_num) => {
                        if let Value::Number(right_num) = right_value {
                            return Ok(Value::Number(left_num - right_num));
                        }
                    }

                    _ => {
                        return Err(Err {
                            message: format!(
                                "values {} and {} do not support subtraction, at [{}]",
                                left_value.string(),
                                right_value.string(),
                                position.string()
                            )
                            .to_string(),
                            reason: ErrorReason::Syntax,
                        })
                    }
                }
            }

            Kind::MultiplyOp => {
                let (left_value, right_value) = left_right()?;
                match left_value {
                    Value::Number(left_num) => {
                        if let Value::Number(right_num) = right_value {
                            return Ok(Value::Number(left_num * right_num));
                        }
                    }

                    Value::Bool(left_bool) => {
                        if let Value::Bool(right_bool) = right_value {
                            return Ok(Value::Bool(left_bool && right_bool));
                        }
                    }

                    _ => {
                        return Err(Err {
                            message: format!(
                                "values {} and {} do not support multiplication, at [{}]",
                                left_value.string(),
                                right_value.string(),
                                position.string()
                            )
                            .to_string(),
                            reason: ErrorReason::Syntax,
                        })
                    }
                }
            }

            Kind::DivideOp => {
                let (left_value, right_value) = left_right()?;
                match left_value {
                    Value::Number(left_num) => {
                        if let Value::Number(right_num) = right_value {
                            if right_num == 0f64 {
                                return Err(Err {
                                    message: format!(
                                        "decision by zero error [{}]",
                                        right_operand.position().string()
                                    )
                                    .to_string(),
                                    reason: ErrorReason::Runtime,
                                });
                            }
                            return Ok(Value::Number(left_num / right_num));
                        }
                    }

                    _ => {
                        return Err(Err {
                            message: format!(
                                "values {} and {} do not support division, at [{}]",
                                left_value.string(),
                                right_value.string(),
                                position.string()
                            )
                            .to_string(),
                            reason: ErrorReason::Syntax,
                        })
                    }
                }
            }

            Kind::ModulusOp => {
                let (left_value, right_value) = left_right()?;
                match left_value {
                    Value::Number(left_num) => {
                        if let Value::Number(right_num) = right_value {
                            if right_num == 0f64 {
                                return Err(Err {
                                    message: format!(
                                        "decision by zero error in modulus [{}]",
                                        right_operand.position().string()
                                    )
                                    .to_string(),
                                    reason: ErrorReason::Runtime,
                                });
                            }
                            return Ok(Value::Number(left_num + right_num));
                        }
                    }

                    _ => {
                        return Err(Err {
                            message: format!(
                                "cannot take modulus of non-integer value {}, at [{}]",
                                right_value.string(),
                                left_operand.position().string()
                            )
                            .to_string(),
                            reason: ErrorReason::Syntax,
                        })
                    }
                }
            }

            Kind::LogicalAndOp => {
                let (left_value, right_value) = left_right()?;
                match left_value {
                    // the LogicalAndOp will perform a bitwise and; `&`.
                    Value::Number(left_num) => {
                        if is_intable(&left_num) {
                            if let Value::Number(right_num) = right_value {
                                if is_intable(&right_num) {
                                    return Ok(Value::Number(
                                        (left_num as i64 & right_num as i64) as f64,
                                    ));
                                }
                            }
                        }

                        return Err(Err {
                            message: format!(
                                "cannot take logical & of non-integer values {}, {} [{}]",
                                left_value.string(),
                                right_value.string(),
                                position.string()
                            )
                            .to_string(),
                            reason: ErrorReason::Runtime,
                        });
                    }

                    Value::Bool(left_bool) => {
                        if let Value::Bool(right_bool) = right_value {
                            return Ok(Value::Bool(left_bool && right_bool));
                        }
                    }

                    _ => {
                        return Err(Err {
                            message: format!(
                                "values {} and {} do not support bitwise or logical &, at [{}]",
                                left_value.string(),
                                right_value.string(),
                                position.string()
                            )
                            .to_string(),
                            reason: ErrorReason::Syntax,
                        })
                    }
                }
            }

            Kind::LogicalOrOp => {
                let (left_value, right_value) = left_right()?;
                match left_value {
                    // the LogicalOrOp will perform a bitwise or; `|`.
                    Value::Number(left_num) => {
                        if is_intable(&left_num) {
                            if let Value::Number(right_num) = right_value {
                                if is_intable(&right_num) {
                                    return Ok(Value::Number(
                                        (left_num as i64 | right_num as i64) as f64,
                                    ));
                                }
                            }
                        }

                        return Err(Err {
                            message: format!(
                                "cannot take logical | of non-integer values {}, {} [{}]",
                                left_value.string(),
                                right_value.string(),
                                position.string()
                            )
                            .to_string(),
                            reason: ErrorReason::Runtime,
                        });
                    }

                    Value::Bool(left_bool) => {
                        if let Value::Bool(right_bool) = right_value {
                            return Ok(Value::Bool(left_bool || right_bool));
                        }
                    }

                    _ => {
                        return Err(Err {
                            message: format!(
                                "values {} and {} do not support bitwise or logical |, at [{}]",
                                left_value.string(),
                                right_value.string(),
                                position.string()
                            )
                            .to_string(),
                            reason: ErrorReason::Syntax,
                        })
                    }
                }
            }

            Kind::GreaterThanOp => {
                let (left_value, right_value) = left_right()?;
                match left_value {
                    Value::Number(left_num) => {
                        if let Value::Number(right_num) = right_value {
                            return Ok(Value::Bool(left_num > right_num));
                        }
                    }

                    Value::String(left_str) => {
                        if let Value::String(right_str) = right_value {
                            return Ok(Value::Bool(left_str > right_str));
                        }
                    }

                    _ => {
                        return Err(Err {
                            reason: ErrorReason::Runtime,
                            message: format!(
                                "values {} and {} do not support comparison, at [{}]",
                                left_value.string(),
                                right_value.string(),
                                position.string()
                            ),
                        });
                    }
                }
            }

            Kind::LessThanOp => {
                let (left_value, right_value) = left_right()?;
                match left_value {
                    Value::Number(left_num) => {
                        if let Value::Number(right_num) = right_value {
                            return Ok(Value::Bool(left_num < right_num));
                        }
                    }

                    Value::String(left_str) => {
                        if let Value::String(right_str) = right_value {
                            return Ok(Value::Bool(left_str < right_str));
                        }
                    }

                    _ => {
                        return Err(Err {
                            reason: ErrorReason::Runtime,
                            message: format!(
                                "values {} and {} do not support comparison, at [{}]",
                                left_value.string(),
                                right_value.string(),
                                position.string()
                            ),
                        });
                    }
                }
            }

            Kind::EqualOp => {
                let (left_value, right_value) = left_right()?;
                return Ok(Value::Bool(left_value.equals(right_value)));
            }

            _ => log_err(
                &ErrorReason::Assert,
                &format!("unknown binary operator {}", operator.string()),
            ),
        }
    }

    return Err(Err {
        reason: ErrorReason::Assert,
        message: format!("node provided is not a BinaryExprNode",),
    });
}

// Calls into a Speak callback function synchronously.
fn eval_speak_function(
    stack: &mut StackFrame,
    fn_value: &Value,
    allow_thunk: bool,
    args: &[Value],
) -> Result<Value, Err> {
    match fn_value {
        Value::Function(func) => {
            let mut arg_vtable = HashMap::new();
            if let Node::FunctionLiteral { arguments, .. } = func.defn.as_ref() {
                for (i, (arg_ident, arg_type)) in arguments.iter().enumerate() {
                    if i < args.len() {
                        // assert the arg value types match
                        if args[i].value_type() != *arg_type {
                            return Err(Err {
                                message: format!(""),
                                reason: ErrorReason::Runtime,
                            });
                        }

                        arg_vtable.insert(arg_ident.clone(), args[i].clone());
                    }
                }

                let mut return_thunk = Value::FunctionCallThunk {
                    vt: VTable(arg_vtable),
                    func: func.clone(),
                };

                if allow_thunk {
                    return Ok(return_thunk);
                }
                return unwrap_thunk(stack, &mut return_thunk);
            }

            Err(Err {
                message: "".to_string(),
                reason: ErrorReason::System,
            })
        }

        // stack is used in the mod function only to load
        Value::NativeFunction(func) => func.1(stack, args),

        _ => Err(Err {
            message: format!(
                "attempted to call a non-function value {}",
                fn_value.string()
            ),
            reason: ErrorReason::Runtime,
        }),
    }
}

fn unwrap_thunk(stack: &mut StackFrame, thunk: &mut Value) -> Result<Value, Err> {
    let mut is_thunk = true;
    let mut v = Value::Empty;
    while is_thunk {
        if let Value::FunctionCallThunk { func, .. } = thunk {
            // get the function body and eval
            if let Node::FunctionLiteral { body, .. } = func.defn.as_mut() {
                v = body.eval(stack, true)?;
                if let Value::FunctionCallThunk { .. } = v {
                    is_thunk = true
                } else {
                    is_thunk = false
                }
            }
        }
    }

    Ok(v)
}

fn to_value<'a>(op: &Node, stack: &'a mut StackFrame) -> Result<Value, Err> {
    match op {
        Node::StringLiteral { value, .. } => Ok(Value::String(value.clone())),
        Node::NumberLiteral { value, .. } => Ok(Value::Number(value.clone())),
        Node::BoolLiteral { value, .. } => Ok(Value::Bool(value.clone())),
        Node::Identifier { value, .. } => {
            if let Some(val) = stack.get(value) {
                return Ok(val.clone());
            }
            return Err(Err {
                message: "value not found in stack".to_string(),
                reason: ErrorReason::Runtime,
            });
        }
        Node::EmptyIdentifier { .. } => Err(Err {
            message: format!("cannot assign an empty identifier a value"),
            reason: ErrorReason::Runtime,
        }),
        Node::FunctionLiteral { .. } => Ok(Value::Function(Function {
            defn: Box::new(op.clone()),
        })),
        _ => Err(Err {
            message: "cannot resolve to concrete value of node provided".to_string(),
            reason: ErrorReason::System,
        }),
    }
}

fn is_intable(num: &f64) -> bool {
    *num == num.trunc()
}
