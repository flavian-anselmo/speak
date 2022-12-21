use crate::core::log::log_debug;

use super::{
    error::{Err, ErrorReason},
    eval::StackFrame,
    eval::{
        r#type::{self, Type},
        value::{Function, _Value},
    },
    lexer::{Kind, Position, Tok},
    log::{log_err, log_safe_err},
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
        arguments: Vec<(r#type::Type, _Node)>,
        body: Box<_Node>,
        position: Position,
    },

    IfExprNode {
        condition: Box<_Node>,
        clauses: (Option<Box<_Node>>, Option<Box<_Node>>), // (true, false)
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
                    format!("{}, {}", acc, arg.1.string())
                }),

            _Node::IfExprNode {
                condition, clauses, ..
            } => {
                let mut s = format!("If ({})", condition.string());
                if let Some(true_clause) = &clauses.0 {
                    s.push_str(&format!("? ({})", true_clause.string()));
                }
                if let Some(false_clause) = &clauses.1 {
                    s.push_str(&format!("! ({})", false_clause.string()));
                }
                s
            }
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
            _Node::IfExprNode { position, .. } => position,
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

            _Node::IfExprNode {
                condition,
                clauses,
                position,
            } => {
                unimplemented!()
            }
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

/// Parses a stream of tokens into AST [`_Node`]s.
/// This implementation is a recursive descent parser.
pub fn parse(
    tokens_chan: Receiver<Tok>,
    nodes_chan: Sender<_Node>,
    fatal_error: bool,
    debug_parser: bool,
) {
    let tokens: Vec<Tok> = tokens_chan.iter().collect();
    let (mut idx, length) = (0, tokens.len());

    while idx < length {
        match parse_expression(&tokens[idx..]) {
            Ok((node, consumed)) => {
                if debug_parser {
                    log_debug(&format!("parse -> {}", node.string()));
                }

                idx += consumed;
                nodes_chan.send(node).expect("this will always be valid");
            }
            Err(err) => {
                if fatal_error {
                    log_err(&err.reason, &err.message);
                    return;
                }
                log_safe_err(&err.reason, &err.message);
                return;
            }
        }
    }
}

fn get_op_priority(t: &Tok) -> i8 {
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

fn isBinaryOp(t: &Tok) -> bool {
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

fn parse_expression(tokens: &[Tok]) -> Result<(_Node, usize), Err> {
    let mut idx = 0;

    let consume_dangling_separator = || {
        if idx < tokens.len() && tokens[idx].kind == Kind::Separator {
            idx += 1;
        }
    };

    let (atom, consumed) = parse_atom(&tokens[idx..])?;
    idx += consumed;

    guard_unexpected_input_end(tokens, idx)?;

    let next_tok = &tokens[idx];

    match &next_tok.kind {
        Kind::Separator => Ok((atom, idx)), // consumed

        Kind::If => {
            let (if_expr, consumed) = parse_if_expression(&tokens[idx..])?;
            idx += consumed;
            Ok((if_expr, idx))
        }

        Kind::AddOp
        | Kind::SubtractOp
        | Kind::MultiplyOp
        | Kind::DivideOp
        | Kind::ModulusOp
        | Kind::LogicalAndOp
        | Kind::LogicalOrOp
        | Kind::GreaterThanOp
        | Kind::LessThanOp
        | Kind::EqualOp
        | Kind::AssignOp
        | Kind::AccessorOp => {
            let (bin_expr, consumed) = parse_binary_expression(atom, next_tok, &tokens[idx..], -1)?;
            idx += consumed;
            Ok((bin_expr, idx))
        }

        _ => Err(Err {
            message: format!(
                "unexpected token {} at {}, following an expression",
                next_tok.kind.string(),
                next_tok.position.string()
            ),
            reason: ErrorReason::Syntax,
        }),
    }
}

fn parse_binary_expression(
    left_operand: _Node,
    operator: &Tok,
    tokens: &[Tok],
    previous_priority: i8,
) -> Result<(_Node, usize), Err> {
    let (right_operand, mut idx) = parse_atom(&tokens[1..])?;

    let mut ops = vec![operator.clone()];
    let mut nodes = vec![left_operand, right_operand];

    // build up a list of binary operations, with tree nodes
    // where there are higher-precedence operations
    while tokens.len() > idx && isBinaryOp(&tokens[idx]) {
        if previous_priority >= get_op_priority(&tokens[idx]) {
            // Priority is lower than the previous op, so we're done
            break;
        } else if get_op_priority(&ops[ops.len() - 1]) >= get_op_priority(&tokens[idx]) {
            // Priority is lower than the previous op (but higher than parent),
            // so it's ok to be left-heavy in this tree
            ops.push(tokens[idx].clone());
            idx += 1;

            guard_unexpected_input_end(&tokens, idx)?;

            let (right_atom, consumed) = parse_atom(&tokens[idx..])?;
            nodes.push(right_atom);
            idx += consumed;
        } else {
            guard_unexpected_input_end(&tokens, idx + 1)?;

            // Priority is higher than the previous op, so we need to
            // make it right-heavy
            let (subtree, consumed) = parse_binary_expression(
                nodes[nodes.len() - 1].clone(),
                &tokens[idx],
                &tokens[idx + 1..],
                get_op_priority(&ops[ops.len() - 1]),
            )?;

            nodes.insert(nodes.len() - 1, subtree);
            idx += consumed + 1;
        }
    }

    // ops, nodes -> left-biased binary expression tree
    let mut tree = nodes.get(0).expect("this value is present").clone(); //nodes[0];
    let mut nodes = &nodes[1..];

    while ops.len() > 0 {
        tree = _Node::BinaryExpression {
            operator: ops[0].kind.clone(),
            leftOperand: to_operand(&tree)?,
            rightOperand: to_operand(&nodes[0])?,
            position: ops[0].position.clone(),
        };

        ops.remove(0);
        nodes = &nodes[1..];
    }

    Ok((tree, idx))
}

fn parse_atom(tokens: &[Tok]) -> Result<(_Node, usize), Err> {
    guard_unexpected_input_end(tokens, 0)?;
    let (tok, mut idx) = (&tokens[0], 1);

    if tok.kind == Kind::NegationOp {
        let (operand, consumed) = parse_atom(&tokens[idx..])?;

        return Ok((
            _Node::UnaryExpression {
                operator: tok.kind.clone(),
                operand: to_operand(&operand)?,
                position: tok.position.clone(),
            },
            consumed + 1,
        ));
    }

    guard_unexpected_input_end(tokens, idx)?;

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
            if tokens[idx].kind == Kind::Colon {
                // colon after identifier means the identifier is a function literal
                (atom, idx) = parse_function_literal(&tokens)?;
            } else {
                atom = _Node::Identifier {
                    value: tok.str.clone().expect("this node has this value present"),
                    position: tok.position.clone(),
                };
            }
        }

        Kind::EmptyIdentifier => {
            if tokens[idx].kind == Kind::Colon {
                // colon after identifier means the identifier is a function literal
                (atom, idx) = parse_function_literal(&tokens)?;
            } else {
                return Ok((
                    _Node::EmptyIdentifier {
                        position: tok.position.clone(),
                    },
                    idx,
                ));
            }
        }

        _ => {
            return Err(Err {
                message: format!("unexpected start of atom, found {}", tok.kind.string(),),
                reason: ErrorReason::Syntax,
            })
        }
    }

    // if previous token is identifier and next token is identifier, then this is a function call
    while idx < tokens.len()
        && tokens[idx - 1].kind == Kind::Identifier
        && tokens[idx].kind == Kind::Identifier
    {
        let (_atom, consumed) = parse_function_call(atom, &tokens[idx..])?;

        idx += consumed;
        atom = _atom;
        guard_unexpected_input_end(tokens, idx)?;
    }

    Ok((atom, idx))
}

fn parse_if_expression(tokens: &[Tok]) -> Result<(_Node, usize), Err> {
    let (tok, mut idx) = (&tokens[0], 1);
    // if n % 2 == 0 ? = n / 2 ! = 3 * n + 1

    // check either for first occurence of ? or !, whichever comes first
    while tokens[idx].kind != Kind::QuestionMark || tokens[idx].kind != Kind::Bang {
        idx += 1;
    }
    // let (condition, consumed) = parse_expression(&tokens[idx..])?;
    unimplemented!("parse_if_body")
}

fn parse_function_call(func: _Node, tokens: &[Tok]) -> Result<(_Node, usize), Err> {
    let idx = 1;
    guard_unexpected_input_end(tokens, idx)?;

    //   let mut args: Vec<_Node> = Vec::new();

    unimplemented!()
}

fn parse_function_literal(tokens: &[Tok]) -> Result<(_Node, usize), Err> {
    let (tok, mut idx) = (&tokens[0], 1);
    let mut arguments = Vec::new();
    guard_unexpected_input_end(tokens, idx)?;

    // fizzbuzz: n int -> string
    //  if n % 15 == 0 ? = "FizzBuzz"
    //  if n % 3 == 0 ? = "Fizz"
    //  if n % 5 == 0 ? = "Buzz"
    //  = sprint n

    match tok.kind {
        Kind::LeftParen => {
            //loop{}
        }
        Kind::Identifier => {
            //
            arguments.push(_Node::Identifier {
                value: tok.str.clone().expect("this node has this value present"),
                position: tok.position.clone(),
            });
        }
        Kind::EmptyIdentifier => {
            arguments.push(_Node::EmptyIdentifier {
                position: tok.position.clone(),
            });
        }

        _ => {
            return Err(Err {
                message: format!(
                    "unexpected token {} at {}, malformed arguements list",
                    tok.kind.string(),
                    tok.position.string()
                ),
                reason: ErrorReason::Syntax,
            })
        }
    }

    // guard_unexpected_input_end(tokens, idx)?;

    let (body, consumed) = parse_expression(&tokens[idx..])?;
    idx += consumed;

    Ok((
        _Node::FunctionLiteral {
            arguments: Vec::new(),
            body: Box::new(body),
            position: tok.position.clone(),
        },
        idx,
    ))
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

fn to_operand(n: &_Node) -> Result<Operand, Err> {
    match n {
        _Node::BoolLiteral { value, .. } => Ok(Operand::Value(_Value::Bool(value.clone()))),

        _Node::Identifier { value, .. } => Ok(Operand::Identifier(value.clone())),

        _Node::NumberLiteral { value, .. } => Ok(Operand::Value(_Value::Number(value.clone()))),

        _ => Err(Err {
            message: format!(
                "the node, {} at {}, is not an operand",
                n.string(),
                n.position().string()
            )
            .to_string(),
            reason: ErrorReason::Syntax,
        }),
    }
}
