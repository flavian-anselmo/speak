use super::{
    error::{Err, ErrorReason},
    eval::StackFrame,
    eval::{
        r#type::Type,
        value::{Function, _Value},
    },
    lexer::{Kind, Position, Tok},
};
use std::{
    fmt::Debug,
    sync::mpsc::{Receiver, Sender},
};

#[derive(Debug, Clone)]
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
#[derive(Debug, Clone)]
pub enum _Node {
    NumberLiteral {
        value: f64,
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
            _Node::NumberLiteral { value, .. } => value.to_string(),
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
                body: _,
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
            _Node::NumberLiteral { value, .. } => Ok(_Value::Number(*value)),
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
                            _Value::Number(nt) => {
                                *nt = -*nt;
                                Ok(())
                            }
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

// Parses a stream of tokens into a stream of nodes. This implementation is a recursive descent parser.
pub fn parse(
    tokens_chan: Receiver<Tok>,
    nodes_chan: Sender<_Node>,
    fatal_error: bool,
    debug_parser: bool,
) -> Result<(), Err> {
    let tokens: Vec<Tok> = tokens_chan.iter().collect();
    let (mut idx, length) = (0, tokens.len());

    while idx < length {
        let (node, consumed) = parse_expression(&tokens[idx..], fatal_error)?;

        if debug_parser {
            println!("parse -> {}", node.string());
        }

        nodes_chan.send(node).expect("this will always be valid");

        idx += consumed;
    }

    Ok(())
}

fn get_op_priority(t: Tok) -> i8 {
    // higher number means higher priority
    match t.kind {
        Kind::AccessorOp => 50,

        Kind::ModulusOp => 40,

        Kind::MultiplyOp | Kind::DivideOp => 25,

        Kind::AddOp | Kind::SubtractOp => 20,

        Kind::GreaterThanOp | Kind::LessThanOp | Kind::EqualOp => 15,

        Kind::AssignOp => 0,

        _ => -1,
    }
}

fn isBinaryOp(t: Tok) -> bool {
    match t.kind {
        Kind::AccessorOp
        | Kind::ModulusOp
        | Kind::MultiplyOp
        | Kind::DivideOp
        | Kind::AddOp
        | Kind::SubtractOp
        | Kind::GreaterThanOp
        | Kind::LessThanOp
        | Kind::EqualOp
        | Kind::AssignOp => true,
        _ => false,
    }
}

fn parse_expression(tokens: &[Tok], fatal_error: bool) -> Result<(_Node, usize), Err> {
    unimplemented!()
}

fn parse_binary_expression(
    left_operand: _Node,
    operator: Tok,
    tokens: &[Tok],
    previous_priority: i8,
    fatal_error: bool,
) -> Result<(_Node, usize), Err> {
    unimplemented!()
}

fn parse_atom(tokens: &[Tok], fatal_error: bool) -> Result<(_Node, usize), Err> {
    guard_unexpected_input_end(tokens, 0)?;

    let (tok, idx) = (&tokens[0], 1);

    if tok.kind == Kind::NegationOp {
        let (operand, consumed) = parse_atom(&tokens[idx..], fatal_error)?;

        return Ok((
            _Node::UnaryExpression {
                operator: tok.kind.clone(),
                operand: to_operand(operand)?,
                position: tok.position.clone(),
            },
            consumed + 1,
        ));
    }

    guard_unexpected_input_end(tokens, 0)?;

    let mut atom: _Node;
    match tok.kind {
        Kind::NumberLiteral => {
            return Ok((
                _Node::NumberLiteral {
                    value: tok.num.clone().expect("this node has this value present"),
                    position: tok.position.clone(),
                },
                idx,
            ));
        }

        Kind::StringLiteral => {
            return Ok((
                _Node::StringLiteral {
                    value: tok.str.clone().expect("this node has this value present"),
                    position: tok.position.clone(),
                },
                idx,
            ));
        }

        Kind::TrueLiteral => {
            return Ok((
                _Node::BoolLiteral {
                    value: true,
                    position: tok.position.clone(),
                },
                idx,
            ));
        }

        Kind::FalseLiteral => {
            return Ok((
                _Node::BoolLiteral {
                    value: false,
                    position: tok.position.clone(),
                },
                idx,
            ));
        }

        Kind::Identifier => {
            unimplemented!()
        }

        Kind::EmptyIdentifier => {
            unimplemented!()
        }

        _ => {
            return Err(Err {
                message: format!("unexpected start of atom, found {}", tok.kind.string(),),
                reason: ErrorReason::Syntax,
            })
        }
    }

    Ok((atom, idx))
}

fn guard_unexpected_input_end(tokens: &[Tok], idx: usize) -> Result<(), Err> {
    if idx >= tokens.len() {
        if tokens.is_empty() {
            return Err(Err {
                message: format!(
                    "unexpected end of input at {}",
                    tokens[tokens.len() - 1].kind.string()
                ),
                reason: ErrorReason::Syntax,
            });
        }

        return Err(Err {
            message: "unexpected end of input".to_string(),
            reason: ErrorReason::Syntax,
        });
    }

    Ok(())
}

fn to_operand(n: _Node) -> Result<Operand, Err> {
    match n {
        _Node::BoolLiteral { value, .. } => Ok(Operand::Value(_Value::Bool(value))),

        _Node::Identifier { value, .. } => Ok(Operand::Identifier(value)),

        _Node::NumberLiteral { value, .. } => Ok(Operand::Value(_Value::Number(value))),

        _ => Err(Err {
            message: format!(
                "the node, {} at {}, is not an operand",
                n.string(),
                n.position().string()
            )
            .to_string(),
            reason: ErrorReason::System,
        }),
    }
}
