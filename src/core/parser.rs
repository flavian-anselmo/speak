use super::{
    error::{Err, ErrorReason},
    eval::r#type,
    lexer::{Kind, Position, Tok},
    log::{log_err, log_safe_err},
};
use crate::core::log::log_debug;
use std::{
    fmt::Debug,
    sync::mpsc::{Receiver, Sender},
};

/// Node represents an abstract syntax tree (AST) node in a Speak program.
#[derive(Debug, Clone)]
pub enum Node {
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
        operand: Box<Node>,
        position: Position,
    },
    BinaryExpression {
        operator: Kind,
        left_operand: Box<Node>,
        right_operand: Box<Node>,
        position: Position,
    },
    FunctionCall {
        function: Box<Node>,
        arguments: Vec<Node>,
        position: Position,
    },
    FunctionLiteral {
        arguments: Vec<(String, r#type::Type)>, // (identifier, type)
        body: Box<Node>,
        position: Position,
    },
    // IfExprNode {
    //     condition: Box<_Node>,
    //     clauses: (Option<Box<_Node>>, Option<Box<_Node>>), // (true, false)
    //     position: Position,
    // },
}

impl Node {
    pub fn string(&self) -> String {
        match self {
            Node::NumberLiteral { value, .. } => value.to_string(),
            Node::StringLiteral { value, .. } => value.clone(),
            Node::BoolLiteral { value, .. } => value.to_string(),
            Node::EmptyIdentifier { .. } => "".to_string(),
            Node::Identifier { value, .. } => value.clone(),
            Node::UnaryExpression {
                operator, operand, ..
            } => format!("Unary {} ({})", operator.string(), operand.string()),
            Node::BinaryExpression {
                operator,
                left_operand,
                right_operand,
                ..
            } => format!(
                "Binary {} ({}, {})",
                operator.string(),
                left_operand.string(),
                right_operand.string()
            ),
            Node::FunctionCall {
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
            Node::FunctionLiteral {
                arguments,
                body: _,
                position,
            } => arguments
                .iter()
                .fold(format!("Function ({}):", position.string()), |acc, arg| {
                    format!("{}, {}", acc, arg.1.string())
                }),
            // _Node::IfExprNode {
            //     condition, clauses, ..
            // } => {
            //     let mut s = format!("If ({})", condition.string());
            //     if let Some(true_clause) = &clauses.0 {
            //         s.push_str(&format!("? ({})", true_clause.string()));
            //     }
            //     if let Some(false_clause) = &clauses.1 {
            //         s.push_str(&format!("! ({})", false_clause.string()));
            //     }
            //     s
            // }
        }
    }

    pub fn position(&self) -> &Position {
        match self {
            Node::NumberLiteral { position, .. } => position,
            Node::StringLiteral { position, .. } => position,
            Node::BoolLiteral { position, .. } => position,
            Node::EmptyIdentifier { position } => position,
            Node::Identifier { position, .. } => position,
            Node::UnaryExpression { position, .. } => position,
            Node::BinaryExpression { position, .. } => position,
            Node::FunctionCall { position, .. } => position,
            Node::FunctionLiteral { position, .. } => position,
            // _Node::IfExprNode { position, .. } => position,
        }
    }
}

/// Parses a stream of tokens into AST [`_Node`]s.
/// This implementation is a recursive descent parser.
pub fn parse(
    tokens_chan: Receiver<Tok>,
    nodes_chan: Sender<Node>,
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

fn is_binary_op(t: &Tok) -> bool {
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

fn parse_expression(tokens: &[Tok]) -> Result<(Node, usize), Err> {
    let mut idx = 0;
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
    left_operand: Node,
    operator: &Tok,
    tokens: &[Tok],
    previous_priority: i8,
) -> Result<(Node, usize), Err> {
    let (right_operand, mut idx) = parse_atom(&tokens[1..])?;

    let mut ops = vec![operator.clone()];
    let mut nodes = vec![left_operand, right_operand];

    // build up a list of binary operations, with tree nodes
    // where there are higher-precedence operations
    while tokens.len() > idx && is_binary_op(&tokens[idx]) {
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
        tree = Node::BinaryExpression {
            operator: ops[0].kind.clone(),
            left_operand: Box::new(tree),
            right_operand: Box::new(nodes[0].clone()),
            position: ops[0].position.clone(),
        };

        ops.remove(0);
        nodes = &nodes[1..];
    }

    Ok((tree, idx))
}

fn parse_atom(tokens: &[Tok]) -> Result<(Node, usize), Err> {
    guard_unexpected_input_end(tokens, 0)?;
    let (tok, mut idx) = (&tokens[0], 0);

    if tok.kind == Kind::NegationOp {
        let (operand, consumed) = parse_atom(&tokens[idx..])?;

        return Ok((
            Node::UnaryExpression {
                operator: tok.kind.clone(),
                operand: Box::new(operand),
                position: tok.position.clone(),
            },
            consumed,
        ));
    }

    guard_unexpected_input_end(tokens, idx)?;

    let mut atom: Node;
    match tok.kind {
        Kind::NumberLiteral => {
            return Ok((
                Node::NumberLiteral {
                    value: tok.num.clone().expect("this node has this value present"),
                    position: tok.position.clone(),
                },
                idx + 1,
            ));
        }

        Kind::StringLiteral => {
            return Ok((
                Node::StringLiteral {
                    value: tok.str.clone().expect("this node has this value present"),
                    position: tok.position.clone(),
                },
                idx + 1,
            ));
        }

        Kind::TrueLiteral => {
            return Ok((
                Node::BoolLiteral {
                    value: true,
                    position: tok.position.clone(),
                },
                idx + 1,
            ));
        }

        Kind::FalseLiteral => {
            return Ok((
                Node::BoolLiteral {
                    value: false,
                    position: tok.position.clone(),
                },
                idx + 1,
            ));
        }

        Kind::Identifier => {
            if tokens[idx].kind == Kind::Colon {
                // colon after identifier means the identifier is a function literal
                (atom, idx) = parse_function_literal(&tokens)?;
            } else {
                atom = Node::Identifier {
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
                    Node::EmptyIdentifier {
                        position: tok.position.clone(),
                    },
                    idx + 1,
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

    while idx < tokens.len() {
        match tokens[idx].kind {
            Kind::Identifier | Kind::StringLiteral | Kind::TrueLiteral | Kind::FalseLiteral => {
                let (_atom, consumed) = parse_function_call(&atom, &tokens[idx..])?;

                idx += consumed;
                atom = _atom;
                guard_unexpected_input_end(tokens, idx)?;
            }
            _ => {
                break;
            }
        }
    }

    Ok((atom, idx))
}

fn parse_if_expression(tokens: &[Tok]) -> Result<(Node, usize), Err> {
    let (_tok, mut idx) = (&tokens[0], 1);
    // if n % 2 == 0 ? = n / 2 ! = 3 * n + 1

    // check either for first occurence of ? or !, whichever comes first
    while tokens[idx].kind != Kind::QuestionMark || tokens[idx].kind != Kind::Bang {
        idx += 1;
    }
    // let (condition, consumed) = parse_expression(&tokens[idx..])?;
    unimplemented!("parse_if_body")
}

fn parse_function_call(func: &Node, tokens: &[Tok]) -> Result<(Node, usize), Err> {
    let mut idx = 0;
    // guard_unexpected_input_end(tokens, idx)?;

    // args should be on the same line, or be ')'
    let mut args = Vec::new();
    while func.position().line == tokens[idx].position.line || tokens[idx].kind != Kind::RightParen
    {
        // consume seperator

        let (expr, consumed) = parse_expression(&tokens[idx..])?;

        idx += consumed;
        args.push(expr);

        if let Err(_) = guard_unexpected_input_end(&tokens, idx) {
            break;
        }
    }

    Ok((
        Node::FunctionCall {
            function: Box::new(func.clone()),
            arguments: args,
            position: func.position().clone(),
        },
        idx,
    ))
}

fn parse_function_literal(tokens: &[Tok]) -> Result<(Node, usize), Err> {
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
            arguments.push(Node::Identifier {
                value: tok.str.clone().expect("this node has this value present"),
                position: tok.position.clone(),
            });
        }
        Kind::EmptyIdentifier => {
            arguments.push(Node::EmptyIdentifier {
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
        Node::FunctionLiteral {
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

#[cfg(test)]
mod test {
    use super::parse_expression;
    use crate::core::lexer::{Kind, Position, Tok};

    // "Hello World example"
    #[test]
    fn hello_world() {
        let tokens = [
            Tok {
                kind: Kind::Identifier,
                str: Some("println".to_string()),
                num: None,
                position: Position { line: 2, column: 1 },
            },
            Tok {
                kind: Kind::StringLiteral,
                str: Some("Hello World!".to_string()),
                num: None,
                position: Position { line: 2, column: 9 },
            },
        ];

        match parse_expression(&tokens) {
            Ok((node, i)) => {
                println!("Node: {:?}\npos:{}", node, i)
            }
            Err(err) => {
                panic!("{}", err.message)
            }
        }
    }
}
