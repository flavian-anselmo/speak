use super::{
    error::{Err, ErrorReason},
    eval::StackFrame,
    eval::{
        r#type::Type,
        value::{Function, _Numeric, _Value},
    },
    lexer::{Kind, Position, Tok},
};
use num_traits::Num;
use std::{
    cell::RefCell,
    fmt::Debug,
    ops::{Sub, SubAssign},
    rc::Rc,
    sync::mpsc::{Receiver, Sender},
};

#[derive(Debug, Clone, PartialEq)]
pub enum Operand {
    Value(_Value),
    Identifier(String),
}

impl Operand {
    fn string(&self) -> String {
        match self {
            Operand::Value(v) => v.string(),
            Operand::Identifier(s) => s.clone(),
        }
    }
}

/// Node represents an abstract syntax tree (AST) node in a Speak program.
#[derive(Debug, Clone, PartialEq)]
pub enum _Node {
    NumberLiteral {
        str_value: String,
        number_type: Option<Type>,
        position: Position,
    },
    StringLiteral {
        value: String,
        position: Position,
    },
    BoolLiteral {
        value: bool,
        position: Position,
    },
    EmptyIdentifier {
        position: Position,
    },
    Identifier {
        value: String,
        position: Position,
    },
    UnaryExpression {
        operator: Kind,
        operand: Operand,
        position: Position,
    },
    BinaryExpression {
        operator: Kind,
        leftOperand: Operand,
        rightOperand: Operand,
        position: Position,
    },
    FunctionCall {
        function: Box<_Node>,
        arguments: Vec<_Node>,
        position: Position,
    },
    FunctionLiteral {
        arguments: Vec<_Node>,
        body: Box<_Node>,
        position: Position,
    },
}

impl _Node {
    pub fn string(&self) -> String {
        match self {
            _Node::NumberLiteral { str_value, .. } => str_value.clone(),
            _Node::StringLiteral { value, .. } => value.clone(),
            _Node::BoolLiteral { value, .. } => value.to_string(),
            _Node::EmptyIdentifier { .. } => "".to_string(),
            _Node::Identifier { value, .. } => value.clone(),
            _Node::UnaryExpression {
                operator, operand, ..
            } => format!("Unary {} ({})", operator.string(), operand.string()),
            _Node::BinaryExpression {
                operator,
                leftOperand,
                rightOperand,
                ..
            } => format!(
                "Binary {} ({}, {})",
                operator.string(),
                leftOperand.string(),
                rightOperand.string()
            ),
            _Node::FunctionCall {
                function,
                arguments,
                ..
            } => {
                let mut args = String::new();
                for arg in arguments {
                    args.push_str(&arg.string());
                    args.push_str(", ");
                }
                format!("Call ({}) on ({})", function.string(), args)
            }
            _Node::FunctionLiteral {
                arguments,
                body,
                position,
            } => arguments
                .iter()
                .fold(format!("Function ({}):", position.string()), |acc, arg| {
                    format!("{}, {}", acc, arg.string())
                }),
        }
    }

    pub fn position(&self) -> &Position {
        match self {
            _Node::NumberLiteral { position, .. } => position,
            _Node::StringLiteral { position, .. } => position,
            _Node::BoolLiteral { position, .. } => position,
            _Node::EmptyIdentifier { position } => position,
            _Node::Identifier { position, .. } => position,
            _Node::UnaryExpression { position, .. } => position,
            _Node::BinaryExpression { position, .. } => position,
            _Node::FunctionCall { position, .. } => position,
            _Node::FunctionLiteral { position, .. } => position,
        }
    }

    pub fn eval(&mut self, stack: &mut StackFrame, allow_thunk: bool) -> Result<_Value, Err> {
        match self {
            _Node::NumberLiteral {
                str_value,
                number_type,
                ..
            } => {
                if let Some(t) = number_type {
                    return match t {
                        Type::Uint8 => {
                            Ok(_Value::Numeric(_Numeric::Uint8(eval_number_literal::<u8>(
                                &str_value,
                            )?)))
                        }
                        Type::Uint16 => Ok(_Value::Numeric(_Numeric::Uint16(
                            eval_number_literal::<u16>(&str_value)?,
                        ))),
                        Type::Uint32 => Ok(_Value::Numeric(_Numeric::Uint32(
                            eval_number_literal::<u32>(&str_value)?,
                        ))),
                        Type::Uint64 => Ok(_Value::Numeric(_Numeric::Uint64(
                            eval_number_literal::<u64>(&str_value)?,
                        ))),
                        Type::Int8 => Ok(_Value::Numeric(_Numeric::Int8(
                            eval_number_literal::<i8>(&str_value)?,
                        ))),
                        Type::Int16 => {
                            Ok(_Value::Numeric(_Numeric::Int16(
                                eval_number_literal::<i16>(&str_value)?,
                            )))
                        }
                        Type::Int32 => {
                            Ok(_Value::Numeric(_Numeric::Int32(
                                eval_number_literal::<i32>(&str_value)?,
                            )))
                        }
                        Type::Int64 => {
                            Ok(_Value::Numeric(_Numeric::Int64(
                                eval_number_literal::<i64>(&str_value)?,
                            )))
                        }
                        Type::Float32 => {
                            Ok(_Value::Numeric(_Numeric::Float32(eval_number_literal::<
                                f32,
                            >(
                                &str_value
                            )?)))
                        }
                        Type::Float64 => {
                            Ok(_Value::Numeric(_Numeric::Float64(eval_number_literal::<
                                f64,
                            >(
                                &str_value
                            )?)))
                        }
                        _ => {
                            return Err(Err {
                                message: "invalid number type".to_string(),
                                reason: ErrorReason::System,
                            })
                        }
                    };
                }
                Ok(_Value::Numeric(_Numeric::Float64(eval_number_literal::<
                    f64,
                >(
                    str_value.as_str()
                )?)))
            }
            _Node::StringLiteral { value, .. } => Ok(_Value::String(value.clone())), // Tidy: this is a copy
            _Node::BoolLiteral { value, .. } => Ok(_Value::Bool(value.clone())), // Tidy: this is a copy
            _Node::EmptyIdentifier { .. } => Ok(_Value::Empty),
            _Node::Identifier { value, position } => {
                if let Some(val) = stack.get(&value) {
                    return Ok(val.clone());
                }
                Err(Err {
                    message: format!("{} is not defined [{}]", value, position.string()),
                    reason: ErrorReason::System,
                })
            }
            _Node::UnaryExpression {
                operator,
                operand,
                position,
            } => {
                let mut_operand = |op: &mut Operand| -> Result<(), Err> {
                    match op {
                        Operand::Value(v) => match v {
                            _Value::Numeric(nt) => match nt {
                                _Numeric::Int8(v) => {
                                    *v = -*v;
                                    Ok(())
                                }
                                _Numeric::Int16(v) => {
                                    *v = -*v;
                                    Ok(())
                                }
                                _Numeric::Int32(v) => {
                                    *v = -*v;
                                    Ok(())
                                }
                                _Numeric::Int64(v) => {
                                    *v = -*v;
                                    Ok(())
                                }
                                _Numeric::Float32(v) => {
                                    *v = -*v;
                                    Ok(())
                                }
                                _Numeric::Float64(v) => {
                                    *v = -*v;
                                    Ok(())
                                }
                                _ => Err(Err {
                                    message: "invalid number type".to_string(),
                                    reason: ErrorReason::System,
                                }),
                            },
                            _Value::Bool(b) => {
                                *b = !*b;
                                Ok(())
                            }
                            _ => {
                                return Err(Err {
                                    message: format!(
                                        "invalid unary operator {} at {}",
                                        operator.string(),
                                        position.string()
                                    ),
                                    reason: ErrorReason::Syntax,
                                })
                            }
                        },

                        _ => unimplemented!("should not evalute to a identifier"),
                    }
                };

                match operator {
                    Kind::NegationOp => match operand.clone() {
                        Operand::Value(n) => {
                            mut_operand(operand)?;
                            Ok(n.clone())
                        }
                        Operand::Identifier(ident) => {
                            if let Some(val) = stack.get(&ident) {
                                mut_operand(operand)?;
                                return Ok(val.clone());
                            }
                            return Err(Err {
                                message: format!(
                                    "{} is not defined [{}]",
                                    ident,
                                    position.string()
                                ),
                                reason: ErrorReason::System,
                            });
                        }
                    },

                    _ => {
                        return Err(Err {
                            message: format!(
                                "invalid unary operator {} at {}",
                                operator.string(),
                                position.string()
                            ),
                            reason: ErrorReason::Syntax,
                        });
                    }
                }
            }
            _Node::BinaryExpression {
                operator,
                leftOperand,
                rightOperand,
                position,
            } => unimplemented!(),
            _Node::FunctionCall {
                function,
                arguments,
                position,
            } => {
                let mut arg_results = Vec::new();
                for arg in arguments {
                    arg_results.push(arg.eval(stack, false)?);
                }

                eval_speak_function(&function.eval(stack, false)?, allow_thunk, &arg_results)
            }
            _Node::FunctionLiteral {
                arguments,
                body,
                position,
            } => Ok(_Value::Function(Function {
                defn: Box::new(self.clone()),
            })),
        }
    }
}

// Calls into a Speak callback function synchronously.
fn eval_speak_function<'a>(
    fn_value: &_Value,
    allow_thunk: bool,
    args: &[_Value],
) -> Result<_Value, Err> {
    unimplemented!() // TODO: implement
}

/// the number evaluation requires inferring the type of the number thus a more generic
/// implementation is required.
pub fn eval_number_literal<T: num_traits::Num>(value: &str) -> Result<T, Err> {
    match T::from_str_radix(value, 10) {
        Ok(v) => Ok(v),
        Err(_err) => Err(Err {
            message: "error occured evaluating number literal".to_string(),
            reason: ErrorReason::System,
        }),
    }
}

#[test]
fn this_test() {
    let res = eval_number_literal::<f32>("0.234");
    assert!(Ok(0.234f32) == res);
}

pub fn parse<N>(
    tokens_chan: Receiver<Tok>,
    nodes_chan: Sender<N>,
    fatal_error: bool,
    debug_parser: bool,
) -> Result<(), Err> {
    unimplemented!()
}
