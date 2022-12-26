use super::{
    error::{Err, ErrorReason},
    eval::r#type,
    lexer::{Kind, Position, Tok},
};
use crate::core::log::log_debug;
use std::fmt::Debug;

/// Node represents an abstract syntax tree (AST) node in a Speak program.
#[derive(Debug, Clone, PartialEq)]
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

    IfExpr {
        condition: Box<Node>, // Must be BooleanExprNode or eval to value
        on_true: Option<Box<Node>>,
        on_false: Option<Box<Node>>,
        position: Position,
    }, // IfExprNode {
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
            Node::IfExpr {
                condition,
                on_true,
                on_false,
                position,
            } => {
                let mut s = format!("If ({}): ({})", position.string(), condition.string());
                if let Some(true_clause) = &on_true {
                    s.push_str(&format!("? ({})", true_clause.string()));
                }
                if let Some(false_clause) = &on_false {
                    s.push_str(&format!("! ({})", false_clause.string()));
                }
                s
            }
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
            Node::IfExpr { position, .. } => position,
        }
    }
}

/// Parses a stream of tokens into AST [`_Node`]s.
/// This implementation is a recursive descent parser.
pub fn parse(tokens: &[Tok], nodes_chan: &mut Vec<Node>, debug_parser: bool) -> Result<(), Err> {
    let (mut idx, length) = (0, tokens.len());

    while idx < length {
        let (node, consumed) = parse_expression(&tokens[idx..], false)?;
        if debug_parser {
            log_debug(&format!("parse -> {}", node.string()));
        }

        idx += consumed;
        nodes_chan.push(node);
    }
    Ok(())
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

fn parse_expression(tokens: &[Tok], parsing_fn_args: bool) -> Result<(Node, usize), Err> {
    let (atom, consumed) = parse_atom(tokens, parsing_fn_args)?;
    if consumed == tokens.len() {
        return Ok((atom, consumed));
    }

    let mut idx = consumed;
    guard_unexpected_input_end(tokens, idx)?;
    let next_tok = &tokens[idx];
    idx += 1;

    match &next_tok.kind {
        Kind::RightParen => Ok((atom, idx - 1)), // consumed by caller

        Kind::Separator => Ok((atom, idx)), // consumed

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
            let (bin_expr, consumed) = parse_binary_expr(atom, next_tok, &tokens[idx..], -1)?;
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

fn parse_binary_expr(
    left_operand: Node,
    operator: &Tok,
    tokens: &[Tok],
    previous_priority: i8,
) -> Result<(Node, usize), Err> {
    let (right_operand, mut idx) = parse_atom(tokens, false)?;

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

            let (right_atom, consumed) = parse_atom(&tokens[idx..], false)?;
            nodes.push(right_atom);
            idx += consumed;
        } else {
            guard_unexpected_input_end(&tokens, idx + 1)?;

            // Priority is higher than the previous op, so we need to
            // make it right-heavy
            let pos = nodes.len() - 1;
            let (subtree, consumed) = parse_binary_expr(
                nodes[pos].clone(),
                &tokens[idx],
                &tokens[idx + 1..],
                get_op_priority(&ops[ops.len() - 1]),
            )?;

            nodes[pos] = subtree;
            idx += consumed + 1;
        }
    }

    // ops, nodes -> left-biased binary expression tree
    let mut tree = nodes[0].clone();
    let mut nodes = &nodes[1..];

    while ops.len() > 0 {
        tree = Node::BinaryExpression {
            operator: ops[0].kind.clone(),
            left_operand: Box::new(tree),
            right_operand: Box::new(nodes[0].clone()),
            position: ops[0].position.clone(),
        };

        ops = ops[1..].to_vec();
        nodes = &nodes[1..];
    }

    Ok((tree, idx))
}

fn parse_atom(tokens: &[Tok], parsing_fn_args: bool) -> Result<(Node, usize), Err> {
    guard_unexpected_input_end(tokens, 0)?;
    let (tok, mut idx) = (&tokens[0], 1);

    let mut atom: Node;
    match tok.kind {
        Kind::If => return parse_if_expr(tokens),

        Kind::LeftParen => return parse_capsulated_expr(tokens, idx),

        Kind::NegationOp => {
            let (operand, consumed) = parse_atom(&tokens[idx..], false)?;

            return Ok((
                Node::UnaryExpression {
                    operator: tok.kind.clone(),
                    operand: Box::new(operand),
                    position: tok.position.clone(),
                },
                consumed + 1,
            ));
        }

        Kind::NumberLiteral => {
            return Ok((
                Node::NumberLiteral {
                    value: tok.num.clone().expect("this node has this value present"),
                    position: tok.position.clone(),
                },
                idx,
            ));
        }

        Kind::StringLiteral => {
            return Ok((
                Node::StringLiteral {
                    value: tok.str.clone().expect("this node has this value present"),
                    position: tok.position.clone(),
                },
                idx,
            ));
        }

        Kind::TrueLiteral => {
            return Ok((
                Node::BoolLiteral {
                    value: true,
                    position: tok.position.clone(),
                },
                idx,
            ));
        }

        Kind::FalseLiteral => {
            return Ok((
                Node::BoolLiteral {
                    value: false,
                    position: tok.position.clone(),
                },
                idx,
            ));
        }

        Kind::Identifier => {
            guard_unexpected_input_end(tokens, idx)?;
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

    while !parsing_fn_args && idx < tokens.len() {
        match tokens[idx].kind {
            Kind::Identifier
            | Kind::StringLiteral
            | Kind::NumberLiteral
            | Kind::TrueLiteral
            | Kind::FalseLiteral
            | Kind::LeftParen => {
                let (_atom, consumed) = parse_function_call(&atom, &tokens[idx..])?;

                idx += consumed;
                atom = _atom;
            }
            _ => {
                break;
            }
        }
    }

    Ok((atom, idx))
}

fn parse_capsulated_expr(tokens: &[Tok], idx: usize) -> Result<(Node, usize), Err> {
    // grouped expression that evals to a single expression or a function literal node
    let (atom, consumed) = parse_expression(&tokens[idx..], false)?;
    let idx = idx + consumed;

    guard_unexpected_input_end(tokens, idx)?;
    if tokens[idx].kind != Kind::RightParen {
        return Err(Err {
            message: format!(
                "the expression expected ')' after [{}]",
                tokens[idx - 1].string()
            ),
            reason: ErrorReason::Syntax,
        });
    }
    return Ok((atom, idx + 1)); // +1 for the RightParen
}

fn parse_if_expr(tokens: &[Tok]) -> Result<(Node, usize), Err> {
    let (condition, mut idx) = parse_atom(tokens, false)?;

    let mut if_arms = [None::<Box<Node>>, None::<Box<Node>>];
    while idx < tokens.len()
        && (tokens[idx].kind == Kind::QuestionMark || tokens[idx].kind == Kind::Bang)
    {
        guard_unexpected_input_end(tokens, idx + 1)?;
        let (arm, consumed) = parse_atom(&tokens[idx + 1..], false)?;

        // arm assignment; not checking for overwrites
        if tokens[idx].kind == Kind::QuestionMark {
            if_arms[0] = Some(Box::new(arm));
        } else {
            if_arms[1] = Some(Box::new(arm))
        }

        idx += consumed;
    }

    let pos = condition.position();
    Ok((
        Node::IfExpr {
            condition: Box::new(condition.clone()),
            on_true: if_arms[0].clone(),
            on_false: if_arms[1].clone(),
            position: pos.clone(),
        },
        idx,
    ))
}

fn parse_function_call(func: &Node, tokens: &[Tok]) -> Result<(Node, usize), Err> {
    let mut idx = 0;
    guard_unexpected_input_end(tokens, idx)?;

    // args should be on the same line, or be ')'
    let mut args = Vec::new();
    while idx < tokens.len()
        && func.position().line == tokens[idx].position.line
        && tokens[idx].kind != Kind::RightParen
    {
        let (expr, consumed) = parse_expression(&tokens[idx..], true)?;

        idx += consumed;
        args.push(expr);
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

    guard_unexpected_input_end(tokens, idx)?;

    let (body, consumed) = parse_expression(&tokens[idx..], false)?;
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
    use crate::core::{
        lexer::{Kind, Position, Tok},
        parser::Node,
    };

    // "Hello World example"
    #[test]
    fn hello_world() {
        let ident_pos = Position { line: 2, column: 1 };
        let str_pos = Position { line: 2, column: 9 };
        let tokens = [
            Tok {
                kind: Kind::Identifier,
                str: Some("println".to_string()),
                num: None,
                position: ident_pos.clone(),
            },
            Tok {
                kind: Kind::StringLiteral,
                str: Some("Hello World!".to_string()),
                num: None,
                position: str_pos.clone(),
            },
        ];

        let (res, consumed) =
            parse_expression(&tokens, false).expect("this will return the FunctionCall node");
        assert_eq!(2, consumed, "the number of nodes consumed");

        assert_eq!(
            Node::FunctionCall {
                function: Box::new(Node::Identifier {
                    value: "println".to_string(),
                    position: ident_pos.clone()
                }),
                arguments: vec![Node::StringLiteral {
                    value: "Hello World!".to_string(),
                    position: str_pos
                }],
                position: ident_pos
            },
            res
        );
    }

    // Binary Expression
    #[test]
    fn binary_expr() {
        // 100 * 2 + 3
        let tokens = [
            Tok {
                kind: Kind::NumberLiteral,
                str: None,
                num: Some(100f64),
                position: Position { line: 1, column: 8 },
            },
            Tok {
                kind: Kind::MultiplyOp,
                str: None,
                num: None,
                position: Position {
                    line: 1,
                    column: 12,
                },
            },
            Tok {
                kind: Kind::NumberLiteral,
                str: None,
                num: Some(2f64),
                position: Position {
                    line: 1,
                    column: 14,
                },
            },
            Tok {
                kind: Kind::AddOp,
                str: None,
                num: None,
                position: Position {
                    line: 1,
                    column: 17,
                },
            },
            Tok {
                kind: Kind::NumberLiteral,
                str: None,
                num: Some(3f64),
                position: Position {
                    line: 1,
                    column: 19,
                },
            },
        ];

        let (res, consumed) =
            parse_expression(&tokens, false).expect("this will return the FunctionCall node");
        assert_eq!(5, consumed, "the number of nodes consumed");

        let expect = Node::BinaryExpression {
            operator: Kind::AddOp,
            left_operand: Box::new(Node::BinaryExpression {
                operator: Kind::MultiplyOp,
                left_operand: Box::new(Node::NumberLiteral {
                    value: 100.0,
                    position: Position { line: 1, column: 8 },
                }),
                right_operand: Box::new(Node::NumberLiteral {
                    value: 2.0,
                    position: Position {
                        line: 1,
                        column: 14,
                    },
                }),
                position: Position {
                    line: 1,
                    column: 12,
                },
            }),
            right_operand: Box::new(Node::NumberLiteral {
                value: 3.0,
                position: Position {
                    line: 1,
                    column: 19,
                },
            }),
            position: Position {
                line: 1,
                column: 17,
            },
        };
        assert_eq!(res, expect);
    }
}
