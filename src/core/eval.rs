use self::value::{Function, Value};
use super::{
    error::{Err, ErrorReason},
    lexer::Kind,
    parser::Node,
    runtime::{StackFrame, VTable},
};
use std::collections::HashMap;

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

        Nil,
    }

    // type aliases
    impl Type {
        pub fn string(&self) -> String {
            match self {
                Type::Number => "number".to_string(),
                Type::Bool => "bool".to_string(),
                Type::String => "string".to_string(),
                Type::Function => "function".to_string(),
                Type::Empty => "()".to_string(),
                Type::Nil => "".to_string(),
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

        /// This is a convenience type that is not used by the programmer but
        /// helpful in returns from expressions that do not evaluate to values.
        _Nil,
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
                Value::_Nil => Type::Nil,
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
                Value::_Nil => "".to_string(),
            }
        }
    }
}

impl Node {
    pub fn eval(&mut self, stack: &mut StackFrame, allow_thunk: bool) -> Result<Value, Err> {
        match self {
            Node::NumberLiteral { value, .. } => Ok(Value::Number(*value)),
            Node::StringLiteral { value, .. } => Ok(Value::String(value.clone())),
            Node::BoolLiteral { value, .. } => Ok(Value::Bool(value.clone())),
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
                        _ => Err(Err {
                            message: format!(
                                "invalid unary operand {}, at {}",
                                op.string(),
                                position.string()
                            ),
                            reason: ErrorReason::Runtime,
                        }),
                    }
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
            Node::FunctionLiteral { signature, .. } => {
                // place the function literal on the current stack and return
                // empty value
                match signature.0.as_ref() {
                    Node::Identifier { value, .. } => {
                        stack.set(
                            value.clone(),
                            Value::Function(Function {
                                defn: Box::new(self.clone()),
                            }),
                        );

                        Ok(Value::Empty)
                    }
                    _ => Err(Err {
                        message: format!(
                            "expected identifier node but got {} at [{}]",
                            signature.0.string(),
                            signature.0.position().string()
                        ),
                        reason: ErrorReason::Assert,
                    }),
                }
            }
            Node::IfExpr { .. } => eval_if_expr_node(&self, stack, allow_thunk),
        }
    }
}

fn eval_if_expr_node(node: &Node, stack: &mut StackFrame, allow_thunk: bool) -> Result<Value, Err> {
    if let Node::IfExpr {
        condition,
        on_true,
        on_false,
        ..
    } = node
    {
        // assert that condition evaluates to boolean value
        let mut condition = condition.as_ref().clone();
        let val = condition.eval(stack, allow_thunk.clone())?;
        let mut ret = |val| {
            if val {
                match on_true {
                    Some(on_true) => {
                        let mut on_true = on_true.as_ref().clone();
                        return on_true.eval(stack, allow_thunk);
                    }
                    None => return Ok(Value::Empty),
                }
            }
            match on_false {
                Some(on_false) => {
                    let mut on_false = on_false.as_ref().clone();
                    return on_false.eval(stack, allow_thunk);
                }
                None => return Ok(Value::Empty),
            }
        };

        match val {
            Value::Bool(val) => return ret(val),
            Value::String(str) => return ret(str.is_empty()),
            _ => {
                return Err(Err {
                    message: format!(
                        "the codition, ({}) at [{}], does not evaluate to bool value",
                        condition.string(),
                        node.position().string()
                    ),
                    reason: ErrorReason::Runtime,
                });
            }
        }
    }

    return Err(Err {
        reason: ErrorReason::System,
        message: "".to_string(),
    });
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
                to_value(left_operand.as_ref().clone(), stack)?,
                to_value(right_operand.as_ref().clone(), stack)?,
            ))
        };

        match operator {
            Kind::AssignOp => {
                match left_operand.as_ref() {
                    Node::Identifier { value, .. } => {
                        // right operand node must evaluate to a value
                        let right_value = to_value(right_operand.as_ref().clone(), stack)?;
                        stack.set(value.clone(), right_value.clone());
                        return Ok(right_value);
                    }

                    Node::BinaryExpression {
                        operator: _l_operator,
                        left_operand: _l_left_operand,
                        right_operand: _l_right_operand,
                        position: _l_position,
                    } => {
                        if let Kind::AccessorOp = _l_operator {
                            unimplemented!() // method access
                        } else {
                            return Err(Err {
                                message: format!(
                                    "cannot assing value to non-identifier {}, at [{}]",
                                    _l_left_operand.string(),
                                    left_operand.position().string(),
                                ),
                                reason: ErrorReason::Runtime,
                            });
                        }
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
                unimplemented!() // method access
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
                            return Ok(Value::Number(left_num % right_num));
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

            _ => {
                return Err(Err {
                    reason: ErrorReason::Assert,
                    message: format!("unknown binary operator {}", operator.string()),
                })
            }
        }

        return Err(Err {
            reason: ErrorReason::Runtime,
            message: format!(
                "cannot perform op, {}, on ({}) and ({}), at [{}]",
                operator.string(),
                left_operand.string(),
                right_operand.string(),
                node.position().string()
            ),
        });
    }
    return Err(Err {
        reason: ErrorReason::Assert,
        message: format!("node provided is not a BinaryExprNode"),
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
            if let Node::FunctionLiteral { signature, .. } = func.defn.as_ref() {
                for (i, (arg_ident, arg_type)) in signature.1.iter().enumerate() {
                    if i < args.len() {
                        // assert the arg value types match
                        if args[i].value_type().string() != arg_type.string() {
                            return Err(Err {
                                message: format!(""),
                                reason: ErrorReason::Runtime,
                            });
                        }

                        if let Node::Identifier { value, .. } = arg_ident {
                            arg_vtable.insert(value.clone(), args[i].clone());
                        } else {
                            return Err(Err {
                                reason: ErrorReason::Assert,
                                message: format!(
                                    "could not resolve node ({}) as identifier",
                                    arg_ident.string()
                                ),
                            });
                        }
                    }
                }

                let mut return_thunk = Value::FunctionCallThunk {
                    vt: VTable(arg_vtable),
                    func: func.clone(),
                };

                if allow_thunk {
                    return Ok(return_thunk);
                }

                // assert that the return value is what was in the function signature
                let res = unwrap_thunk(stack, &mut return_thunk)?;

                match signature.2.as_ref() {
                    Node::Identifier { value, .. } => {
                        if res.value_type().string() != *value {
                            return Err(Err {
                                reason: ErrorReason::Runtime,
                                message: format!(
                                    "the return type expected ({}) but got ({})",
                                    value,
                                    res.value_type().string()
                                ),
                            });
                        }
                        return Ok(res);
                    }
                    _ => {
                        return Err(Err {
                            reason: ErrorReason::Assert,
                            message: format!(
                                "expected the return type to be an identifier node but got ({})",
                                signature.2.string(),
                            ),
                        })
                    }
                }
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
                "attempted to call a non-function value {} of type {}",
                fn_value.string(),
                fn_value.value_type().string()
            ),
            reason: ErrorReason::Runtime,
        }),
    }
}

// Expands out a recursive strusture of thunks into a flat for loop control structure
fn unwrap_thunk(stack: &mut StackFrame, thunk: &mut Value) -> Result<Value, Err> {
    let mut is_thunk = true;
    'UNWRAP: while is_thunk {
        match thunk {
            Value::FunctionCallThunk { func, .. } => {
                let defn = func.defn.as_mut();
                match defn {
                    Node::FunctionLiteral {
                        signature, body, ..
                    } => {
                        let mut val: Value;
                        for stmt in body {
                            val = stmt.eval(stack, true)?;
                            match val {
                                Value::FunctionCallThunk { .. } => {
                                    is_thunk = true;
                                    continue 'UNWRAP;
                                }

                                _ => {
                                    // if the return type is that of the signature, return
                                    if val.value_type().string() == signature.2.string() {
                                        return Ok(val);
                                    }
                                }
                            }
                        }
                    }
                    _ => {
                        return Err(Err {
                            message: format!(
                                "expected function literal node value but got {}",
                                defn.string()
                            ),
                            reason: ErrorReason::Assert,
                        });
                    }
                }
            }
            _ => {
                return Err(Err {
                    message: format!("expected thunk value but got {}", thunk.string()),
                    reason: ErrorReason::Assert,
                });
            }
        }
    }

    unimplemented!("this code is never called")
}

fn to_value(op: Node, stack: &mut StackFrame) -> Result<Value, Err> {
    let mut op = op;
    match op {
        Node::StringLiteral { value, .. } => Ok(Value::String(value)),
        Node::NumberLiteral { value, .. } => Ok(Value::Number(value)),
        Node::BoolLiteral { value, .. } => Ok(Value::Bool(value)),
        Node::Identifier { value, .. } => {
            if let Some(val) = stack.get(&value) {
                return Ok(val.clone());
            }
            return Err(Err {
                message: format!("value for identifier, {},  not found in stack", value),
                reason: ErrorReason::Runtime,
            });
        }
        Node::EmptyIdentifier { .. } => Err(Err {
            message: format!("cannot assign an empty identifier a value"),
            reason: ErrorReason::Runtime,
        }),
        Node::FunctionLiteral { .. } => Ok(Value::Function(Function { defn: Box::new(op) })),
        Node::BinaryExpression { .. } => op.eval(stack, false),
        Node::FunctionCall { .. } => op.eval(stack, false),
        _ => Err(Err {
            message: "cannot resolve to concrete value of node provided".to_string(),
            reason: ErrorReason::System,
        }),
    }
}

fn is_intable(num: &f64) -> bool {
    *num == num.trunc()
}

#[cfg(test)]
mod test {
    use crate::core::{
        eval::value::Value,
        lexer::Position,
        parser::Node,
        runtime::{load_builtins, Context},
    };

    #[test]
    fn test_eval_speak_function() {
        // new testing context
        let mut ctx_test = Context::new(&true);
        // load "println" to stack
        _ = load_builtins(&mut ctx_test);

        let ident_pos = Position { line: 1, column: 1 };
        let str_pos = Position { line: 1, column: 9 };
        let h_str = "Hello World!";

        // print "Hello World!" to stdout
        // `println "Hello World!"`
        {
            let mut node_fn_call = Node::FunctionCall {
                function: Box::new(Node::Identifier {
                    value: "println".to_string(),
                    position: ident_pos.clone(),
                }),
                arguments: vec![Node::StringLiteral {
                    value: h_str.to_string(),
                    position: str_pos.clone(),
                }],
                position: ident_pos.clone(),
            };

            let val = node_fn_call
                .eval(&mut ctx_test.frame, false)
                .expect("this should resolve to empty value");

            assert_eq!(val.string(), "()");
        }

        // write "Hello World!" to output
        // `sprint "Hello World!"`
        {
            let mut node_fn_call = Node::FunctionCall {
                function: Box::new(Node::Identifier {
                    value: "sprint".to_string(),
                    position: ident_pos.clone(),
                }),
                arguments: vec![Node::StringLiteral {
                    value: h_str.to_string(),
                    position: str_pos.clone(),
                }],
                position: ident_pos.clone(),
            };

            let val = node_fn_call
                .eval(&mut ctx_test.frame, false)
                .expect("this should resolve to a string value");

            if let Value::String(_val) = val {
                assert_eq!(_val, h_str);
            } else {
                panic!(
                    "did not resolve to Value::String, value id of type {}",
                    val.value_type().string()
                )
            }
        }
    }
}
