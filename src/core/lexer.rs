use super::{
    error::{Err, ErrorReason},
    log::{log_debug, log_err, log_safe_err},
};
use std::{
    io::BufReader,
    sync::mpsc,
    sync::mpsc::{Receiver, Sender},
    thread,
};

// Kind is the sum type of all possible types
// of tokens in a Speak program
#[derive(Debug, Clone)]
pub enum Kind {
    DotOp,
    CommaOp,
    

    FuncExpr,
    StructExpr,
    IFaceExpr,
    ValueExpr,

    UnaryExpr,
    BinaryExpr,
    WhereExpr,
    WhereClause,

    Identifier,
    EmptyIdentifier,

    FunctionCall,

    NumberLiteral,
    StringLiteral,
    ObjectLiteral,
    ListLiteral,
    FunctionLiteral,

    TrueOp,
    FalseOp,

    // =
    ReturnOp,
    ArrowOp,

    // :
    KeyValueSeparator,
    DefineOp,
    MatchColon,

    CaseArrow,
    SubtractOp,

    // single char, unambiguous
    NegationOp,
    AddOp,
    MultiplyOp,
    DivideOp,
    ModulusOp,
    GreaterThanOp,
    LessThanOp,
    EqualOp,
    UnequalOp,

    LogicalAndOp,
    LogicalOrOp,
    LogicalXorOp,

    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
}

impl Kind {
    fn string(&self) -> String {
        match self {
            Kind::DotOp => "'.'".to_string(),
            Kind::CommaOp => "','".to_string(),

            Kind::UnaryExpr => "unary expression".to_string(),
            Kind::BinaryExpr => "binary expression".to_string(),

            Kind::TrueOp => "'?'".to_string(),
            Kind::FalseOp => "'!'".to_string(),

            Kind::ReturnOp => "'='".to_string(),
            Kind::ArrowOp => "'->'".to_string(),

            Kind::NegationOp => "'~'".to_string(),
            Kind::AddOp => "'+'".to_string(),
            Kind::SubtractOp => "'-'".to_string(),
            Kind::MultiplyOp => "'*'".to_string(),
            Kind::DivideOp => "'/'".to_string(),
            Kind::ModulusOp => "'%'".to_string(),
            Kind::GreaterThanOp => "'>'".to_string(),
            Kind::LessThanOp => "'<'".to_string(),
            Kind::EqualOp => "'=='".to_string(),
            Kind::UnequalOp => "'~='".to_string(),

            Kind::LogicalAndOp => "'&'".to_string(),
            Kind::LogicalOrOp => "'|'".to_string(),
            Kind::LogicalXorOp => "'^'".to_string(),

            Kind::LeftParen => "'('".to_string(),
            Kind::RightParen => "')'".to_string(),
            Kind::LeftBracket => "'['".to_string(),
            Kind::RightBracket => "']'".to_string(),
            _ => "unknown token".to_string(),
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
    // str and num are both present to implement Tok
    // as a monomorphic type for all tokens; will be zero
    // values often.
    str: Option<String>,
    num: Option<f64>,
    position: Position,
}

impl Tok {
    fn string(&self) -> String {
        match self.kind {
            Kind::Identifier | Kind::StringLiteral | Kind::NumberLiteral => {
                format!(
                    "{} '{}' [{}]",
                    self.kind.string(),
                    self.str.unwrap(), // safe to unwrap, types matched always have str
                    self.position.string()
                )
            }
            _ => format!("{} [{}]", self.kind.string(), self.position.string()),
        }
    }
}

// Tokenize takes an io.Reader and transforms it into a stream of Tok (tokens).
pub fn Tokenize<R: Sized>(
    unbuffered: BufReader<R>,
    tokens_chan: Sender<Tok>,
    fatal_err: bool,
    debug_lexer: bool,
) {
    // let mut buf: String;
    // let mut buf_str: String;

    // let mut str_buf_start_line: i64;
    // let mut str_buf_start_col: i64;

    // let snd_chan = tokens_chan.clone();
    let simple_commit = |tok: Tok| {
        if debug_lexer {
            log_debug(&format!("{}", tok.clone().string()))
        }
        tokens_chan.send(tok.clone()).unwrap();
        tok.clone()
    };

    let simple_commit_char = |kind, line, column| {
        simple_commit(Tok {
            kind,
            str: "".to_string(),
            num: 0f64,
            position: Position { line, column },
        })
    };

    // let (mut line_no, mut col_no) = (1usize, 1usize);

    let commit_clear = |buf, line_no, col_no| {
        if buf == "" {
            // no need to commit empty token
            return None;
        }

        match buf {
            "?" => Some(simple_commit_char(Kind::TrueOp, line_no, col_no)),
            "!" => Some(simple_commit_char(Kind::FalseOp, line_no, col_no)),
            _ => {
                if buf.clone().chars().nth(0).unwrap().is_ascii_digit() {
                    match buf.parse::<f64>() {
                        Ok(res) => Some(simple_commit(Tok {
                            kind: Kind::NumberLiteral,
                            str: "".to_string(),
                            num: res,
                            position: Position {
                                line: line_no.clone(),
                                column: col_no.clone() - buf.len(),
                            },
                        })),

                        Err(err) => {
                            let _err = Err {
                                reason: ErrorReason::Syntax,
                                message: err.to_string(),
                            };

                            if fatal_err {
                                log_err(&_err.reason, &_err.message)
                            } else {
                                log_safe_err(&_err.reason, &_err.message)
                            }

                            return None;
                        }
                    }
                } else {
                    Some(simple_commit(Tok {
                        kind: Kind::Identifier,
                        str: buf.clone().to_string(),
                        num: 0f64,
                        position: Position {
                            line: line_no,
                            column: col_no - buf.len(),
                        },
                    }))
                }
            }
        }
    };

    let commit = |tok, buf, line_no, col_no| {
        commit_clear(buf, line_no, col_no);
        simple_commit(tok);
    };

    let commit_char = |kind, buf, line_no, col_no| {
        commit(
            Tok {
                kind,
                str: "".to_string(),
                num: 0f64,
                position: Position {
                    line: line_no,
                    column: col_no,
                },
            },
            buf,
            line_no,
            col_no,
        )
    };

    let ensure_separator = |buf, line_no, col_no, l1_token| {
        let l2_token = commit_clear(buf, line_no, col_no);

        let mut token: Tok;
        if let Some(t) = l2_token {
            token = t;
        } else {
            token = l1_token;
        }

        match token.kind {
            Kind::CommaOp => None,
            _ => Some(commit_char(Kind::CommaOp, buf, line_no, col_no)),
        }
    };

    unimplemented!()
}
