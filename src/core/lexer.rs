use std::{
    fs::File,
    io::{BufRead, BufReader, Read},
    sync::mpsc::Sender,
};

use super::{
    error::Err,
    eval::{Numeric, Types},
    log::log_debug,
    parser::FunctionExp,
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

    TypeName(Types),
    CommaSep,

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
            Kind::EmptyIdentifier => "_".to_string(),

            Kind::TrueLiteral => "true".to_string(),
            Kind::FalseLiteral => "false".to_string(),

            Kind::TypeName(t) => t.string(),
            Kind::CommaSep => "separator".to_string(),

            Kind::FunctionArrow => "->".to_string(),

            Kind::LeftParen => "(".to_string(),
            Kind::RightParen => ")".to_string(),
            Kind::LeftBracket => "[".to_string(),
            Kind::RightBracket => "]".to_string(),
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
pub struct Tok {
    kind: Kind,
    str: Option<String>,
    num: Option<Numeric>,
    position: Position,
}

impl Tok {
    fn string(&self) -> String {
        match self.kind {
            // Kind::Identifier | Kind::StringLiteral | Kind::NumberLiteral => {
            //     format!(
            //         "{} '{}' [{}]",
            //         self.kind.string(),
            //         self.str.unwrap(), // safe to unwrap, types matched always have str
            //         self.position.string()
            //     )
            // }
            _ => format!("{} [{}]", self.kind.string(), self.position.string()),
        }
    }
}

// Tokenize takes an io.Reader and transforms it into a stream of Tok (tokens).
pub fn Tokenize<R: Sized>(
    unbuffered: &mut BufReader<File>,
    tokens_chan: Sender<Tok>,
    fatal_err: bool,
    debug_lexer: bool,
) -> Result<(), Err> {
    // assumption: the input is a valid UTF-8 string
    let mut last_char = ' ';

    // read a complete line while parsing
    let mut buf = String::new();
    for i in unbuffered.read_line(&mut buf) {
        // skip comments
        if buf.starts_with("//") {
            continue;
        }

        let mut entry = String::new();
        let mut str_literal = false;
        for (colNo, c) in buf.chars().enumerate() {
            // skip whitespace
            if c == ' ' {
                continue;
            }

            match c {
                ' ' => commit_arbitrary_entry(&entry, &tokens_chan, &debug_lexer, i + 1, colNo + 1),
                ':' => {
                    commit(
                        Tok {
                            kind: Kind::CommaSep,
                            str: None,
                            num: None,
                            position: Position {
                                line: i + 1,
                                column: colNo + 1,
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
                                line: i + 1,
                                column: colNo + 1,
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
                                line: i + 1,
                                column: colNo + 1,
                            },
                        },
                        &tokens_chan,
                        &debug_lexer,
                    );
                    entry.clear();
                }
                _ => {
                    entry.push(c);
                }
            }
        }
    }

    unimplemented!()
}

fn commit(tok: Tok, tokens_chan: &Sender<Tok>, debug_lexer: &bool) {
    if *debug_lexer {
        log_debug(&format!("lexer -> {}", tok.string()));
    }
    tokens_chan.send(tok).unwrap();
}

fn commit_arbitrary_entry(
    entry: &str,
    tokens_chan: &Sender<Tok>,
    debug_lexer: &bool,
    line: usize,
    column: usize,
) {
    // whitespace, nothing to parse
    if entry.is_empty() {
        return;
    }

    match entry {
        "bool" => commit(
            Tok {
                kind: Kind::TypeName(Types::Bool),
                str: None,
                num: None,
                position: Position { line, column },
            },
            tokens_chan,
            debug_lexer,
        ),
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
                kind: Kind::TypeName(Types::Empty),
                str: None,
                num: None,
                position: Position { line, column },
            },
            tokens_chan,
            debug_lexer,
        ),

        _ => {
            // TODO: check if it's a number
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
