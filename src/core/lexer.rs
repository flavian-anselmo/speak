use std::{
    fs::File,
    io::{BufRead, BufReader},
    sync::mpsc::Sender,
};

use super::{
    error::{Err, ErrorReason},
    eval::Type,
    log::log_debug,
};

// Kind is the sum type of all possible types
// of tokens in a Speak program
#[derive(Debug, Clone)]
pub enum Kind {
    FunctionExpr,

    Identifier,
    EmptyIdentifier,

    TrueLiteral,
    FalseLiteral,
    NumberLiteral,
    StringLiteral,

    TypeName(Type),
    CommaSep,

    Bang,
    QuestionMark,

    FunctionArrow,

    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
}

impl Kind {
    fn string(&self) -> String {
        match self {
            Kind::FunctionExpr => "function expression".to_string(),

            Kind::Identifier => "identifier".to_string(),
            Kind::EmptyIdentifier => "'_'".to_string(),

            Kind::TrueLiteral => "true literal".to_string(),
            Kind::FalseLiteral => "false literal".to_string(),
            Kind::NumberLiteral => "number literal".to_string(),
            Kind::StringLiteral => "string literal".to_string(),

            Kind::TypeName(t) => t.string(),
            Kind::CommaSep => "','".to_string(),

            Kind::Bang => "'!'".to_string(),
            Kind::QuestionMark => "'?'".to_string(),

            Kind::FunctionArrow => "->".to_string(),

            Kind::LeftParen => "'('".to_string(),
            Kind::RightParen => "')'".to_string(),
            Kind::LeftBracket => "'['".to_string(),
            Kind::RightBracket => "']'".to_string(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Position {
    line: usize,
    column: usize,
}

impl Position {
    pub fn string(&self) -> String {
        format!("{}:{}", self.line, self.column)
    }
}

// Tok is the monomorphic struct representing all Speak program tokens
// in the lexer.
#[derive(Debug, Clone)]
pub struct Tok<Number> {
    kind: Kind,
    str: Option<String>,
    num: Option<Number>,
    position: Position,
}

impl<Number> Tok<Number> {
    fn string(&self) -> String {
        match self.kind {
            Kind::Identifier | Kind::StringLiteral | Kind::NumberLiteral => {
                format!(
                    "{} '{}' [{}]",
                    self.kind.string(),
                    self.str.clone().unwrap(), // safe to unwrap, types matched always have str
                    self.position.string()
                )
            }
            _ => format!("{} [{}]", self.kind.string(), self.position.string()),
        }
    }
}

// Tokenize takes an io.Reader and transforms it into a stream of Tok (tokens).
// assumption: the inputs are valid UTF-8 strings.
pub fn Tokenize<R: Sized, Number>(
    unbuffered: &mut BufReader<File>,
    tokens_chan: Sender<Tok<Number>>,
    fatal_err: bool,
    debug_lexer: bool,
) -> Result<(), Err> {
    // read a complete line while parsing
    let mut buf = String::new();
    let mut entry = String::new();
    let mut last_line_column = (0, 0);
    'NEXT_LINE_PARSER: for line in unbuffered.read_line(&mut buf) {
        // skip comments
        if buf.starts_with("//") {
            continue;
        }

        let mut buf_iter = buf.chars().into_iter().enumerate();
        'NEXT_COLUMN_PARSER: while let Some((column, c)) = buf_iter.next() {
            match c {
                '/' => {
                    let err = Err(Err {
                        reason: ErrorReason::Syntax,
                        message: format!("expected item after: {}", c),
                    });

                    // start of a comment, assert and skip rest of the line
                    match buf_iter.next() {
                        Some((_, c)) => {
                            if c != '/' {
                                return err;
                            }

                            continue 'NEXT_LINE_PARSER;
                        }
                        None => return err,
                    }
                }
                ' ' => {
                    if entry.starts_with(".(") {
                        entry.push(c);
                        continue;
                    }

                    commit_arbitrary(
                        entry.clone(),
                        &tokens_chan,
                        &debug_lexer,
                        line + 1,
                        column + 1,
                    );
                    entry.clear();
                }
                '"' => {
                    // start of a string literal, assert as literals
                    loop {
                        match buf_iter.next() {
                            Some((column, c)) => match c {
                                '"' => {
                                    // commit string literal
                                    commit(
                                        Tok {
                                            kind: Kind::StringLiteral,
                                            str: Some(entry.clone()),
                                            num: None,
                                            position: Position {
                                                line: line + 1,
                                                column: column + 1,
                                            },
                                        },
                                        &tokens_chan,
                                        &debug_lexer,
                                    );
                                    continue 'NEXT_COLUMN_PARSER;
                                }
                                _ => {
                                    entry.push(c);
                                }
                            },
                            None => {
                                return Err(Err {
                                    reason: ErrorReason::Syntax,
                                    message: format!("missing trailing symbol '\"'"),
                                })
                            }
                        }
                    }
                }
                ':' => {
                    commit(
                        Tok {
                            kind: Kind::CommaSep,
                            str: None,
                            num: None,
                            position: Position {
                                line: line + 1,
                                column: column + 1,
                            },
                        },
                        &tokens_chan,
                        &debug_lexer,
                    );
                }
                '_' => {
                    commit(
                        Tok {
                            kind: Kind::EmptyIdentifier,
                            str: None,
                            num: None,
                            position: Position {
                                line: line + 1,
                                column: column + 1,
                            },
                        },
                        &tokens_chan,
                        &debug_lexer,
                    );
                    entry.clear();
                }
                ',' => {
                    commit(
                        Tok {
                            kind: Kind::CommaSep,
                            str: None,
                            num: None,
                            position: Position {
                                line: line + 1,
                                column: column + 1,
                            },
                        },
                        &tokens_chan,
                        &debug_lexer,
                    );
                    entry.clear();
                }
                '!' => {
                    commit(
                        Tok {
                            kind: Kind::Bang,
                            str: None,
                            num: None,
                            position: Position {
                                line: line + 1,
                                column: column + 1,
                            },
                        },
                        &tokens_chan,
                        &debug_lexer,
                    );
                    entry.clear();
                }
                '?' => {
                    commit(
                        Tok {
                            kind: Kind::QuestionMark,
                            str: None,
                            num: None,
                            position: Position {
                                line: line + 1,
                                column: column + 1,
                            },
                        },
                        &tokens_chan,
                        &debug_lexer,
                    );
                    entry.clear();
                }
                _ => {
                    entry.push(c);
                    last_line_column.0 = line + 1;
                    last_line_column.1 = column + 1;
                }
            }
        }
    }

    commit_arbitrary(
        entry,
        &tokens_chan,
        &debug_lexer,
        last_line_column.0,
        last_line_column.1,
    );

    Ok(())
}

fn commit<Number>(tok: Tok<Number>, tokens_chan: &Sender<Tok<Number>>, debug_lexer: &bool) {
    if *debug_lexer {
        log_debug(&format!("lexer -> {}", tok.string()));
    }
    tokens_chan.send(tok).unwrap();
}

fn commit_arbitrary<Number>(
    entry: String,
    tokens_chan: &Sender<Tok<Number>>,
    debug_lexer: &bool,
    line: usize,
    column: usize,
) {
    // whitespace, nothing to parse
    if entry.is_empty() {
        return;
    }

    let type_token = |kind| {
        commit(
            Tok {
                kind,
                str: None,
                num: None,
                position: Position { line, column },
            },
            tokens_chan,
            debug_lexer,
        )
    };

    match entry.as_str() {
        "uint8" | "byte" => type_token(Kind::TypeName(Type::Uint8)),
        "uint16" => type_token(Kind::TypeName(Type::Uint16)),
        "uint32" => type_token(Kind::TypeName(Type::Uint32)),
        "uint64" | "uint" => type_token(Kind::TypeName(Type::Uint64)),
        "int8" => type_token(Kind::TypeName(Type::Int8)),
        "int16" => type_token(Kind::TypeName(Type::Int16)),
        "int32" | "int" | "rune" => type_token(Kind::TypeName(Type::Int32)),
        "int64" => type_token(Kind::TypeName(Type::Int64)),
        "float32" => type_token(Kind::TypeName(Type::Float32)),
        "float64" | "float" => type_token(Kind::TypeName(Type::Float64)),

        "bool" => type_token(Kind::TypeName(Type::Bool)),
        "string" => type_token(Kind::TypeName(Type::String)),

        "->" => type_token(Kind::FunctionArrow),

        "true" => commit(
            Tok {
                kind: Kind::TrueLiteral,
                str: None,
                num: None,
                position: Position { line, column },
            },
            tokens_chan,
            debug_lexer,
        ),
        "false" => commit(
            Tok {
                kind: Kind::FalseLiteral,
                str: None,
                num: None,
                position: Position { line, column },
            },
            tokens_chan,
            debug_lexer,
        ),
        "()" => commit(
            Tok {
                kind: Kind::TypeName(Type::Empty),
                str: None,
                num: None,
                position: Position { line, column },
            },
            tokens_chan,
            debug_lexer,
        ),

        _ => {
            if !entry.is_empty() && entry.parse::<f64>().is_ok() {
                commit(
                    Tok {
                        kind: Kind::NumberLiteral,
                        str: Some(entry.to_string()),
                        num: None,
                        position: Position {
                            line,
                            column: { column - entry.len() },
                        },
                    },
                    tokens_chan,
                    debug_lexer,
                );
            }

            commit(
                Tok {
                    kind: Kind::Identifier,
                    str: Some(entry.to_string()),
                    num: None,
                    position: Position {
                        line,
                        column: { column - entry.len() },
                    },
                },
                tokens_chan,
                debug_lexer,
            )
        }
    }
}
