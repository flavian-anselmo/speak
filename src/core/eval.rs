use self::{
    r#type::Type,
    value::{Function, Value},
};
use super::{
    error::{Err, ErrorReason},
    lexer::{Kind, Position},
    log::log_interactive,
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

        /// Object type.
        Object(String),

        /// Array type.
        Array(Box<Type>),

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
                Type::Object(obj) => format!("object: {}", obj),
                Type::Array(t) => format!("[]{}", t.string()),
                Type::Function => "function".to_string(),
                Type::Empty => "()".to_string(),
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
    use std::{collections::HashMap, fmt::Debug};

    /// Value represents any value in the Speak programming language.
    /// Each value corresponds to some primitive or object value created
    /// during the execution of a Speak program.
    #[derive(Debug, Clone)]
    pub enum Value {
        Number(f64),
        Bool(bool),
        String(String),

        /// This is a composite value representing an object in the Speak language.
        Object {
            name: String,
            body: HashMap<String, (Type, Value)>,
        },

        Array(Type, Vec<Value>),

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
        pub defn: Node,
    }

    impl Function {
        fn string(&self) -> String {
            let func_str = self.defn.string();
            if func_str.len() > MAX_PRINT_LEN {
                return format!("{}..", &func_str[..MAX_PRINT_LEN]);
            }

            func_str
        }
    }

    impl Value {
        pub fn value_type(&self) -> Type {
            match self {
                Value::Number(_) => Type::Number,
                Value::Bool(_) => Type::Bool,
                Value::String(_) => Type::String,
                Value::Object { name, .. } => Type::Object(name.clone()),
                Value::Array(t, ..) => Type::Array(Box::new(t.clone())),
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
                // (Value::Empty, _) | (_, Value::Empty) => true,
                _ => false, // types here are incomparable
            }
        }

        pub fn string(&self) -> String {
            match self {
                Value::Number(value) => value.to_string(),
                Value::Bool(value) => value.to_string(),
                Value::String(value) => value.to_string(),
                Value::Object { name, body } => format!("Object ({name}): {:?}", body),
                Value::Array(t, value) => format!("Array ([]{}): {:?}", t.string(), value),
                Value::Function(func) => func.string(),
                Value::NativeFunction(func) => format!("Native Function ({})", func.0),
                Value::FunctionCallThunk { func, .. } => {
                    format!("Thunk of ({})", func.string())
                }
                Value::Empty => "".to_string(),
            }
        }
    }
}

impl Node {
    pub fn eval(&mut self, stack: &mut StackFrame, allow_thunk: bool) -> Result<Value, Err> {
        match self {
            Node::NumberLiteral { value, .. } => Ok(Value::Number(*value)),
            Node::StringLiteral { value, .. } => Ok(Value::String(value.clone())),
            Node::BoolLiteral { value, .. } => Ok(Value::Bool(*value)),
            Node::ArrayLiteral { value, .. } => {
                let value_type = match value.is_empty() {
                    true => Type::Empty,
                    false => value[0].eval(stack, false)?.value_type(),
                };
                Ok(Value::Array(value_type.clone(), {
                    let mut values = Vec::with_capacity(value.len());
                    for node in value {
                        let val = node.eval(stack, false)?;
                        if val.value_type() != value_type {
                            return Err(Err {
                                message: format!(
                                    "expected type ({}) but found ({}) at [{}]",
                                    value_type.string(),
                                    val.value_type().string(),
                                    node.position().string()
                                ),
                                reason: ErrorReason::Runtime,
                            });
                        }
                        values.push(val);
                    }
                    values
                }))
            }
            Node::ObjectLiteral { name, value, .. } => {
                let mut body = HashMap::new();
                for (field_name, val) in value {
                    // first node must be an identifier
                    let val = val.eval(stack, false)?;
                    body.insert(field_name.clone(), (val.value_type(), val));
                }

                Ok(Value::Object {
                    name: name.clone(),
                    body,
                })
            }
            Node::EmptyLiteral(..) | Node::EmptyIdentifier { .. } => Ok(Value::Empty),
            Node::Identifier { value, position } => {
                if let Some(val) = stack.get(value) {
                    return Ok(val.clone());
                }
                Err(Err {
                    message: format!("{value} is not defined [{}]", position.string()),
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
                            Ok(Value::Number(*value))
                        }
                        Node::BoolLiteral { value, .. } => {
                            *value = !*value;
                            Ok(Value::Bool(*value))
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
                                return mut_operand(operand);
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
                        _ => Err(Err {
                            message: format!(
                                "invalid unary operand {}, at {}",
                                operand.string(),
                                position.string()
                            ),
                            reason: ErrorReason::Syntax,
                        }),
                    },

                    _ => Err(Err {
                        message: format!(
                            "invalid unary operator {}, at {}",
                            operator.string(),
                            position.string()
                        ),
                        reason: ErrorReason::Syntax,
                    }),
                }
            }
            Node::BinaryExpression { .. } => eval_binary_expr_node(self, stack, &allow_thunk),
            Node::IndexingOp { operand, index, .. } => match operand.eval(stack, false)? {
                Value::Array(_, vals) => {
                    let idx = to_usize(&(to_number(index, stack)?), index.position())?;
                    match idx >= vals.len() {
                        true => Ok(Value::Empty), // index out of bounds return ()
                        false => Ok(vals[idx].clone()),
                    }
                }
                _ => Err(Err {
                    message: format!(
                        "could not parse {} as array value, at [{}]",
                        operand.string(),
                        operand.position().string()
                    ),
                    reason: ErrorReason::Runtime,
                }),
            },
            Node::SlicingOp {
                operand,
                start_inclusive,
                end_exclusive,
                ..
            } => match operand.eval(stack, false)? {
                Value::Array(t, mut vals) => match (start_inclusive, end_exclusive) {
                    (Some(x), None) => {
                        // array[start..]
                        Ok(Value::Array(
                            t,
                            vals.split_off(to_usize(&(to_number(x, stack)?), x.position())?),
                        ))
                    }
                    (None, Some(x)) => {
                        // array[..end]
                        _ = vals.split_off(to_usize(&(to_number(x, stack)?), x.position())?);
                        Ok(Value::Array(t, vals))
                    }
                    (Some(x), Some(y)) => {
                        // array[start:end]
                        _ = vals.split_off(to_usize(&(to_number(y, stack)?), y.position())?);
                        Ok(Value::Array(
                            t,
                            vals.split_off(to_usize(&(to_number(x, stack)?), x.position())?),
                        ))
                    }
                    (None, None) => Err(Err {
                        message: "slicing operation does not provied a start or an end index"
                            .to_string(),
                        reason: ErrorReason::Assert,
                    }),
                },
                _ => Err(Err {
                    message: format!(
                        "could not parse ({}) as array value, at [{}]",
                        operand.string(),
                        operand.position().string()
                    ),
                    reason: ErrorReason::Runtime,
                }),
            },

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

                let res = eval_speak_function(stack, fn_value, allow_thunk, &arg_results)?;

                Ok(res)
            }
            Node::FunctionLiteral { sign, .. } => {
                // place the function literal on the current stack and return no value
                match sign.0.as_ref() {
                    Node::Identifier { value, .. } => {
                        stack.set(
                            value.clone(),
                            Value::Function(Function { defn: self.clone() }),
                        );

                        Ok(Value::Empty)
                    }
                    _ => Err(Err {
                        message: format!(
                            "expected identifier node but got {} at [{}]",
                            sign.0.string(),
                            sign.0.position().string()
                        ),
                        reason: ErrorReason::Assert,
                    }),
                }
            }
            Node::IfExpr { .. } => eval_if_expr_node(self, stack, allow_thunk),
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
        let val = condition.eval(stack, allow_thunk)?;
        let mut ret = |val| {
            if val {
                return match on_true {
                    Some(on_true) => {
                        let mut on_true = on_true.as_ref().clone();
                        on_true.eval(stack, allow_thunk)
                    }
                    None => Ok(Value::Empty),
                };
            }
            match on_false {
                Some(on_false) => {
                    let mut on_false = on_false.as_ref().clone();
                    on_false.eval(stack, allow_thunk)
                }
                None => Ok(Value::Empty),
            }
        };

        return match val {
            Value::Bool(val) => ret(val),
            Value::String(str) => ret(str.is_empty()),
            _ => Err(Err {
                message: format!(
                    "the codition, ({}) at [{}], does not evaluate to bool value",
                    condition.string(),
                    node.position().string()
                ),
                reason: ErrorReason::Runtime,
            }),
        };
    }

    Err(Err {
        reason: ErrorReason::System,
        message: "".to_string(),
    })
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
                {
                    let mut l = left_operand.as_ref().clone();
                    l.eval(stack, false)?
                },
                {
                    let mut r = right_operand.as_ref().clone();
                    r.eval(stack, false)?
                },
            ))
        };

        if operator == &Kind::AssignOp {
            log_interactive(&format!(
                "HERE operator is {}, left_operand is {:?}\n",
                operator.string(),
                left_operand
            ));
        }

        match operator {
            Kind::AssignOp => {
                // log_interactive(format!("HERE {:?}", left_operand));
                match left_operand.as_ref() {
                    Node::Identifier { value, .. } => {
                        // right operand node must evaluate to a value
                        let mut r = right_operand.as_ref().clone();
                        let right_value = r.eval(stack, false)?;
                        stack.set(value.clone(), right_value.clone());
                        return Ok(right_value);
                    }

                    Node::IndexingOp { operand, index, .. } => {
                        log_interactive("HERE !!!!!\n");
                        let mut operand = operand.as_ref().clone();
                        match &mut operand.eval(stack, false)? {
                            Value::Array(_, vals) => {
                                let mut index = index.as_ref().clone();
                                let idx =
                                    to_usize(&(to_number(&mut index, stack)?), index.position())?;

                                // if index out of bounds, extend vec
                                if idx >= vals.len() {
                                    vals.resize(idx + 1, Value::Empty);
                                }

                                log_interactive("HERE !");

                                // right operand node must evaluate to a value
                                let mut r = right_operand.as_ref().clone();
                                let right_value = r.eval(stack, false)?;

                                vals[idx] = right_value.clone();

                                return Ok(right_value);
                            }
                            _ => {
                                return Err(Err {
                                    message: format!(
                                        "could not parse {} as array value, at [{}]",
                                        operand.string(),
                                        operand.position().string()
                                    ),
                                    reason: ErrorReason::Runtime,
                                })
                            }
                        }
                    }

                    Node::BinaryExpression {
                        operator: l_operator,
                        left_operand: l_left_operand,
                        right_operand: l_right_operand,
                        position: l_position,
                    } => {
                        if let Kind::AccessorOp = l_operator {
                            // left operand is stack name for object
                            let object = l_left_operand.as_ref().clone().eval(stack, false)?;
                            // right operand is the field value
                            let object_field = l_right_operand.string();

                            // mutate field value
                            match &mut object.clone() {
                                Value::Object { name, body } => {
                                    match body.contains_key(&object_field) {
                                        true => {
                                            let right_value = right_operand.as_ref().clone().eval(stack, false)?;
                                            body.insert(
                                                object_field,
                                                (right_value.value_type(), right_value),
                                            );

                                            stack.up(name.clone(), &object)?;
                                            return Ok(object);
                                        }
                                        false => {
                                            return Err(Err {
                                                reason: ErrorReason::Runtime,
                                                message: format!(
                                                "invalid property name {} of composite value {}, at [{}]",
                                                name,
                                                object.string(), l_position.string()
                                            ),
                                            })
                                        }
                                    }
                                }
                                _ => {
                                    return Err(Err {
                                        reason: ErrorReason::System,
                                        message: format!(
                                            "composite value {} unknown",
                                            object.string()
                                        ),
                                    })
                                }
                            }
                        } else {
                            return Err(Err {
                                message: format!(
                                    "cannot assing value to non-identifier {}, at [{}]",
                                    l_left_operand.string(),
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
                // left operand is stack name for object; right operand is the value
                let mut left_operand = left_operand.as_ref().clone();
                let object = left_operand.eval(stack, false)?;
                let object_field = right_operand.string();

                match &object {
                    Value::Object { name, body } => match body.contains_key(&object_field) {
                        true => {
                            let (_, val) =
                                body.get(&object_field).expect("check done, value exists");
                            return Ok(val.clone());
                        }
                        false => {
                            return Err(Err {
                                reason: ErrorReason::Runtime,
                                message: format!(
                                    "invalid property name {} of composite value {}",
                                    name,
                                    object.string(),
                                ),
                            })
                        }
                    },
                    _ => {
                        return Err(Err {
                            reason: ErrorReason::System,
                            message: format!("composite value {} unknown", object.string()),
                        })
                    }
                }
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
                            ),
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
                            ),
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
                                    ),
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
                            ),
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
                                    ),
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
                            ),
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
                            ),
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
                            ),
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
                            ),
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
                            ),
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
        message: format!(
            "node, ({}), provided at [{}] is not a BinaryExprNode",
            node.string(),
            node.position().string()
        ),
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
            match &func.defn {
                Node::FunctionLiteral { sign, .. } => {
                    let mut arg_vtable = HashMap::new();
                    for (i, (arg_ident, arg_type)) in sign.1.iter().enumerate() {
                        if i < args.len() {
                            // assert the arg value types match
                            if args[i].value_type().string() != arg_type.string() {
                                return Err(Err {
                                    message: format!(
                                        "expected arg type of ({}) but got ({}), for {} arg to ({})",
                                        arg_type.string(),
                                        args[i].value_type().string(),
                                        i +1, fn_value.string()
                                    ),
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
                    match sign.2.as_ref() {
                        Node::Identifier { .. } => Ok(res),
                        _ => Err(Err {
                            reason: ErrorReason::Assert,
                            message: format!(
                                "expected the return type to be an identifier node but got ({})",
                                sign.2.string(),
                            ),
                        }),
                    }
                }

                _ => Err(Err {
                    message: "".to_string(),
                    reason: ErrorReason::System,
                }),
            }
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

// Expands out a recursive structure of thunks into a flat for loop control structure
fn unwrap_thunk(stack: &mut StackFrame, thunk: &mut Value) -> Result<Value, Err> {
    let mut is_thunk = true;
    let mut stacks_added = 0;
    'UNWRAP: while is_thunk {
        match thunk {
            Value::FunctionCallThunk { func, vt, .. } => {
                stack.push_frame(vt.clone());
                stacks_added += 1;

                let defn = &mut func.defn;
                match defn {
                    Node::FunctionLiteral { sign, body, .. } => {
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
                                    if match val.value_type() {
                                        Type::Object(obj) => obj,
                                        _ => val.value_type().string(),
                                    } == sign.2.string()
                                    {
                                        // pop stacks that were added, to free memory
                                        for _ in 1..=stacks_added {
                                            stack.pop_frame()?;
                                        }

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

fn is_intable(num: &f64) -> bool {
    *num == num.trunc()
}

#[inline]
fn to_usize(num: &f64, pos: &Position) -> Result<usize, Err> {
    match is_intable(num) {
        true => Ok(*num as usize),
        false => Err(Err {
            message: format!(
                "value ({num}) cannot be used as index, at[{}]",
                pos.string(),
            ),
            reason: ErrorReason::Runtime,
        }),
    }
}

fn to_number(node: &mut Node, stack: &mut StackFrame) -> Result<f64, Err> {
    match node.eval(stack, false)? {
        Value::Number(idx) => Ok(idx),
        _ => Err(Err {
            reason: ErrorReason::Runtime,
            message: format!(
                "expected number, provided node is ({}) at [{}]",
                node.string(),
                node.position().string(),
            ),
        }),
    }
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

            assert_eq!(val.string(), "");
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
