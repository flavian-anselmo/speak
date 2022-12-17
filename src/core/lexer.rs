use super::{
    error::{Err, ErrorReason},
    eval::{r#type::Type, value::_Numeric},
    log::log_debug,
};
use num_traits::Num;
use regex::Regex;
use std::{
    io::{BufRead, BufReader},
    sync::mpsc::Sender,
};

lazy_static! {
    static ref IDENTIFIER_REGEX: Regex =
        Regex::new(r"^[A-Za-z_]\w*$").expect("regex pattern is valid");
}

// Kind is the sum type of all possible types
// of tokens in a Speak program
#[derive(Debug, Clone, PartialEq)]
pub enum Kind {
    // Expr,
    Identifier,
    EmptyIdentifier,
    Identation, // $ single tab character

    IfClause,
    IfExpr,
    WhereClause,
    WhereExpr,

    TrueLiteral,
    FalseLiteral,
    NumberLiteral,
    StringLiteral,

    NegationOp,
    AssignOp,
    AccessorOp,
    AddOp,
    SubtractOp,
    MultiplyOp,
    DivideOp,
    ModulusOp,
    LogicalAndOp,
    LogicalOrOp,
    LogicalXOrOp,
    GreaterThanOp,
    LessThanOp,
    EqualOp,

    Return,

    TypeName(Type),
    Comma,
    Colon,

    Bang,
    QuestionMark,

    ModuleAccessor,
    FunctionArrow,

    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
}

impl Kind {
    pub fn string(&self) -> String {
        match self {
            // Kind::Expr => "expression".to_string(),
            Kind::Identifier => "identifier".to_string(),
            Kind::EmptyIdentifier => "'_'".to_string(),
            Kind::Identation => "identation".to_string(),

            Kind::IfClause => "if clause".to_string(),
            Kind::IfExpr => "if expression".to_string(),
            Kind::WhereClause => "where clause".to_string(),
            Kind::WhereExpr => "where expression".to_string(),

            Kind::TrueLiteral => "true literal".to_string(),
            Kind::FalseLiteral => "false literal".to_string(),
            Kind::NumberLiteral => "number literal".to_string(),
            Kind::StringLiteral => "string literal".to_string(),

            Kind::TypeName(t) => t.string(),
            Kind::Comma => "','".to_string(),
            Kind::Colon => "':'".to_string(),

            Kind::Bang => "'!'".to_string(),
            Kind::QuestionMark => "'?'".to_string(),

            Kind::NegationOp => "'~'".to_string(),
            Kind::AssignOp => "is".to_string(),
            Kind::AccessorOp => "'.'".to_string(),
            Kind::AddOp => "'+'".to_string(),
            Kind::SubtractOp => "'-'".to_string(),
            Kind::MultiplyOp => "'*'".to_string(),
            Kind::DivideOp => "'/'".to_string(),
            Kind::ModulusOp => "'%'".to_string(),
            Kind::LogicalAndOp => "'&'".to_string(),
            Kind::LogicalOrOp => "'|'".to_string(),
            Kind::LogicalXOrOp => "'^'".to_string(),
            Kind::GreaterThanOp => "'>'".to_string(),
            Kind::LessThanOp => "'<'".to_string(),
            Kind::EqualOp => "'=='".to_string(),

            Kind::Return => "'='".to_string(),

            Kind::FunctionArrow => "->".to_string(),
            Kind::ModuleAccessor => "::".to_string(),

            Kind::LeftParen => "'('".to_string(),
            Kind::RightParen => "')'".to_string(),
            Kind::LeftBracket => "'['".to_string(),
            Kind::RightBracket => "']'".to_string(),
        }
    }
}

pub struct FnBody {
    pub body: Vec<Kind>,
}

#[derive(Debug, Clone, PartialEq)]
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
#[derive(Debug, Clone, PartialEq)]
pub struct Tok {
    kind: Kind,
    str: Option<String>,
    num: Option<_Numeric>,
    position: Position,
}

impl Tok {
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

// tokenize takes an io.Reader and transforms it into a stream of Tok (tokens).
// assumption: the inputs are valid UTF-8 strings.
pub fn tokenize(
    unbuffered: &mut BufReader<&[u8]>,
    tokens_chan: &Sender<Tok>,
    _fatal_err: bool,
    debug_lexer: bool,
) -> Result<(), Err> {
    // helper calculate column fn
    let col_fn = |col, len| {
        if len == 1 {
            return col;
        }
        return col - (len - 1);
    };

    // read a complete line while parsing
    let mut line = 1;
    for _line in unbuffered.lines() {
        if _line.is_err() {
            break;
        }
        let buf = _line.unwrap();

        // skip line comments
        if buf.starts_with("//") || buf.is_empty() {
            line += 1;
            continue;
        }

        // if starts with an identation, log the identation to the token stream
        let mut buf_iter = buf.chars().into_iter().enumerate().peekable();
        let mut count = 0;
        loop {
            // identation is 3 spaces
            if let Some((i, c)) = buf_iter.peek() {
                if *c == ' ' {
                    if count == 2 {
                        commit(
                            Tok {
                                kind: Kind::Identation,
                                str: None,
                                num: None,
                                position: Position {
                                    line,
                                    column: col_fn(*i + 1, 3),
                                },
                            },
                            tokens_chan,
                            &debug_lexer,
                        )?;
                        // reset the count
                        count = 0;
                    }

                    count += 1;
                    buf_iter.next(); //advance iterator to net item.
                    continue;
                }
                break;
            }
        }

        //   let mut comment = false;
        let mut entry = String::new();
        let mut last_line_column = (0, 0);
        while let Some((column, c)) = buf_iter.next() {
            let token_commit = |kind| {
                commit(
                    Tok {
                        kind,
                        str: None,
                        num: None,
                        position: Position {
                            line,
                            column: column + 1,
                        },
                    },
                    tokens_chan,
                    &debug_lexer,
                )
            };

            match c {
                '/' => {
                    if let Some((_, '/')) = buf_iter.next() {
                        break;
                    }

                    return Err(Err {
                        reason: ErrorReason::Syntax,
                        message: format!("expected item after: {}", c),
                    });
                }
                ' ' => {
                    // if there is previous entry, commit it as arbitrary
                    if entry.len() > 0 {
                        commit_arbitrary(
                            entry.clone(),
                            tokens_chan,
                            &debug_lexer,
                            line,
                            col_fn(column, entry.len()),
                        )?;
                        entry.clear();
                    }
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
                                                line,
                                                column: col_fn(column, entry.len()),
                                            },
                                        },
                                        tokens_chan,
                                        &debug_lexer,
                                    )?;
                                    entry.clear();
                                    break;
                                }
                                _ => {
                                    entry.push(c);
                                    last_line_column.0 = line;
                                    last_line_column.1 = column + 1;
                                }
                            },
                            None => {
                                return Err(Err {
                                    reason: ErrorReason::Syntax,
                                    message: format!("missing trailing symbol '\"'"),
                                })
                            }
                        };
                    }
                }
                ':' => {
                    // if there is previous entry, commit it as identifier
                    if entry.len() > 0 {
                        commit_arbitrary(
                            entry.clone(),
                            tokens_chan,
                            &debug_lexer,
                            line,
                            col_fn(column, entry.len()),
                        )?;
                        entry.clear();
                    }

                    // lookahead for another ':', mkaing up ::; module accessor
                    if let Some((_, c)) = buf_iter.peek() {
                        if *c == ':' {
                            token_commit(Kind::ModuleAccessor)?;
                            buf_iter.next();
                            continue;
                        }
                    }
                    token_commit(Kind::Colon)?;
                }
                '_' => {
                    token_commit(Kind::EmptyIdentifier)?;
                }
                ',' => {
                    // if there is previous entry, commit it as identifier
                    if entry.len() > 0 {
                        commit_arbitrary(
                            entry.clone(),
                            tokens_chan,
                            &debug_lexer,
                            line,
                            col_fn(column, entry.len()),
                        )?;
                        entry.clear();
                    }

                    token_commit(Kind::Comma)?;
                }
                '!' => {
                    token_commit(Kind::Bang)?;
                }
                '?' => {
                    token_commit(Kind::QuestionMark)?;
                }
                '=' => {
                    token_commit(Kind::Return)?;
                }
                // '{' => {
                //     // start of function expression
                // }
                // '(' => {
                //     // start of expression
                // }
                _ => {
                    entry.push(c);
                    last_line_column.0 = line;
                    last_line_column.1 = column + 1;
                }
            }
        }

        // commit last entry if present
        if entry.len() > 0 {
            commit_arbitrary(
                entry.clone(),
                tokens_chan,
                &debug_lexer,
                last_line_column.0,
                col_fn(last_line_column.1, entry.len()),
            )?;
        }

        line += 1;
    }

    Ok(())
}

fn commit(tok: Tok, tokens_chan: &Sender<Tok>, debug_lexer: &bool) -> Result<(), Err> {
    if *debug_lexer {
        log_debug(&format!("lexer -> {}", tok.string()));
    }
    tokens_chan.send(tok)?;
    Ok(())
}

fn commit_arbitrary(
    entry: String,
    tokens_chan: &Sender<Tok>,
    debug_lexer: &bool,
    line: usize,
    column: usize,
) -> Result<(), Err> {
    // whitespace, nothing to parse
    if entry.is_empty() {
        return Ok(());
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
        "uint8" | "byte" | "uint16" | "uint32" | "uint64" | "uint" | "int8" | "int16" | "int32"
        | "int" | "rune" | "int64" | "float32" | "float64" | "float" => {
            type_token(Kind::TypeName(number_type_to_enum(&entry)))
        }

        "bool" => type_token(Kind::TypeName(Type::Bool)),

        "string" => type_token(Kind::TypeName(Type::String)),

        "->" => type_token(Kind::FunctionArrow),

        "true" => type_token(Kind::TrueLiteral),

        "false" => type_token(Kind::FalseLiteral),

        "()" => type_token(Kind::TypeName(Type::Empty)),

        _ => {
            // check if entry string is numerical
            if <f64>::from_str_radix(&entry.clone(), 10).is_ok() {
                return commit(
                    Tok {
                        kind: Kind::NumberLiteral,
                        str: Some(entry.to_string()),
                        num: None,
                        position: Position { line, column },
                    },
                    tokens_chan,
                    debug_lexer,
                );
            }

            // identifiers should not start with a number: a-z, A-Z, or _
            if !IDENTIFIER_REGEX.is_match(entry.as_str()) {
                return Err(Err {
                    reason: ErrorReason::Syntax,
                    message: format!("invalid identifier: {}", entry),
                });
            }

            commit(
                Tok {
                    kind: Kind::Identifier,
                    str: Some(entry.to_string()),
                    num: None,
                    position: Position { line, column },
                },
                tokens_chan,
                debug_lexer,
            )
        }
    }
}

/// takes a type identifier for a number and returns the corresponding type
pub fn number_type_to_enum(name: &str) -> Type {
    match name {
        "uint8" | "byte" => Type::Uint8,
        "uint16" => Type::Uint16,
        "uint32" => Type::Uint32,
        "uint64" | "uint" => Type::Uint64,
        "int8" => Type::Int8,
        "int16" => Type::Int16,
        "int32" | "int" | "rune" => Type::Int32,
        "int64" => Type::Int64,
        "float32" => Type::Float32,
        "float64" | "float" => Type::Float64,
        _ => panic!("invalid number type"),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::{
        env,
        fs::{self},
        sync::mpsc::{channel, TryRecvError},
    };
    #[test]
    fn test_commit_arbitrary() {
        let (tx, rx) = channel::<Tok>();

        commit_arbitrary("uint8".to_string(), &tx, &false, 1, 1).expect("commit does not fail");
        assert_eq!(
            rx.recv().unwrap(),
            Tok {
                kind: Kind::TypeName(Type::Uint8),
                str: None,
                num: None,
                position: Position { line: 1, column: 1 }
            }
        );

        commit_arbitrary("->".to_string(), &tx, &false, 1, 1).expect("commit does not fail");
        assert_eq!(
            rx.recv().unwrap(),
            Tok {
                kind: Kind::FunctionArrow,
                str: None,
                num: None,
                position: Position { line: 1, column: 1 }
            }
        );

        commit_arbitrary("123.23".to_string(), &tx, &false, 1, 1).expect("commit does not fail");
        assert_eq!(
            rx.recv().unwrap(),
            Tok {
                kind: Kind::NumberLiteral,
                str: Some("123.23".to_string()),
                num: None,
                position: Position { line: 1, column: 1 }
            }
        );

        // test random identifier
        commit_arbitrary("_abc".to_string(), &tx, &false, 1, 1).expect("commit does not fail");
        assert_eq!(
            rx.recv().unwrap(),
            Tok {
                kind: Kind::Identifier,
                str: Some("_abc".to_string()),
                num: None,
                position: Position { line: 1, column: 1 }
            }
        );

        assert_eq!(
            commit_arbitrary("123abc".to_string(), &tx, &false, 1, 1).unwrap_err(),
            Err {
                reason: ErrorReason::Syntax,
                message: "invalid identifier: 123abc".to_string()
            }
        );
    }

    #[test]
    fn test_tokenize() {
        let (tx, rx) = channel::<Tok>();
        let mut buf_reader: BufReader<&[u8]>;

        // comments are ignored
        {
            buf_reader = BufReader::new("// this is a comment".as_bytes());
            match tokenize(&mut buf_reader, &tx, true, true) {
                Ok(_) => (),
                Err(e) => panic!("error: {}", e.message),
            }
            assert_eq!(
                rx.try_recv().expect_err("recv chan must fail"),
                TryRecvError::Empty
            );

            buf_reader = BufReader::new(
                "   // this is a spaced comment with an identation of 3 space char".as_bytes(),
            );
            match tokenize(&mut buf_reader, &tx, true, true) {
                Ok(_) => (),
                Err(e) => panic!("error: {}", e.message),
            }

            assert_eq!(
                rx.try_recv()
                    .expect("recv chan must be an identation token"),
                Tok {
                    kind: Kind::Identation,
                    str: None,
                    num: None,
                    position: Position { line: 1, column: 1 },
                },
            );
            assert_eq!(
                rx.try_recv().expect_err("recv chan must fail"),
                TryRecvError::Empty
            );
        }

        // single char tokens
        {
            buf_reader = BufReader::new(",".as_bytes());
            match tokenize(&mut buf_reader, &tx, true, true) {
                Ok(_) => (),
                Err(e) => panic!("error: {}", e.message),
            }
            assert_eq!(
                rx.try_recv().expect("recv chan does not fail"),
                Tok {
                    kind: Kind::Comma,
                    str: None,
                    num: None,
                    position: Position { line: 1, column: 1 }
                }
            );

            buf_reader = BufReader::new(":".as_bytes());
            match tokenize(&mut buf_reader, &tx, true, true) {
                Ok(_) => (),
                Err(e) => panic!("error: {}", e.message),
            }
            assert_eq!(
                rx.try_recv().expect("recv chan does not fail"),
                Tok {
                    kind: Kind::Colon,
                    str: None,
                    num: None,
                    position: Position { line: 1, column: 1 }
                }
            );
        }

        // tokenise an identifier and a string literal
        {
            buf_reader = BufReader::new("// This is module declaration.\nmod \"fmt\"".as_bytes());
            if let Err(err) = tokenize(&mut buf_reader, &tx, true, true) {
                panic!("error: {}", err.message);
            }

            assert_eq!(
                rx.try_recv().expect("recv chan does not fail"),
                Tok {
                    kind: Kind::Identifier,
                    str: Some("mod".to_string()),
                    num: None,
                    position: Position { line: 2, column: 1 }
                }
            );

            assert_eq!(
                rx.try_recv().expect("recv chan does not fail"),
                Tok {
                    kind: Kind::StringLiteral,
                    str: Some("fmt".to_string()),
                    num: None,
                    position: Position { line: 2, column: 6 }
                }
            );
        }

        // tokenize a function signature
        {
            buf_reader = BufReader::new("sum: a, b int -> int".as_bytes());
            match tokenize(&mut buf_reader, &tx, true, true) {
                Ok(_) => (),
                Err(e) => panic!("error: {}", e.message),
            }

            assert_eq!(
                rx.try_recv().expect("recv chan does not fail"),
                Tok {
                    kind: Kind::Identifier,
                    str: Some("sum".to_string()),
                    num: None,
                    position: Position { line: 1, column: 1 }
                }
            );

            assert_eq!(
                rx.try_recv().expect("recv chan does not fail"),
                Tok {
                    kind: Kind::Colon,
                    str: None,
                    num: None,
                    position: Position { line: 1, column: 4 }
                }
            );

            assert_eq!(
                rx.try_recv().expect("recv chan does not fail"),
                Tok {
                    kind: Kind::Identifier,
                    str: Some("a".to_string()),
                    num: None,
                    position: Position { line: 1, column: 6 }
                }
            );

            assert_eq!(
                rx.try_recv().expect("recv chan does not fail"),
                Tok {
                    kind: Kind::Comma,
                    str: None,
                    num: None,
                    position: Position { line: 1, column: 7 }
                }
            );

            assert_eq!(
                rx.try_recv().expect("recv chan does not fail"),
                Tok {
                    kind: Kind::Identifier,
                    str: Some("b".to_string()),
                    num: None,
                    position: Position { line: 1, column: 9 }
                }
            );

            assert_eq!(
                rx.try_recv().expect("recv chan does not fail"),
                Tok {
                    kind: Kind::TypeName(Type::Int32),
                    str: None,
                    num: None,
                    position: Position {
                        line: 1,
                        column: 11
                    }
                }
            );

            assert_eq!(
                rx.try_recv().expect("recv chan does not fail"),
                Tok {
                    kind: Kind::FunctionArrow,
                    str: None,
                    num: None,
                    position: Position {
                        line: 1,
                        column: 15
                    }
                }
            );

            assert_eq!(
                rx.try_recv().expect("recv chan does not fail"),
                Tok {
                    kind: Kind::TypeName(Type::Int32),
                    str: None,
                    num: None,
                    position: Position {
                        line: 1,
                        column: 18
                    }
                }
            );
        }
    }

    #[test]
    fn test_speak_files() {
        let cwd = env::current_dir().expect("this should not fail");
        let (tx, rx) = channel::<Tok>();
        let mut buf_reader: BufReader<&[u8]>;

        // hello_world.spk
        {
            let data = fs::read(cwd.clone().join("samples/hello_world.spk"))
                .expect("this should not fail");
            buf_reader = BufReader::new(&data);

            if let Err(err) = tokenize(&mut buf_reader, &tx, true, true) {
                panic!("error: {}", err.message);
            }

            assert_eq!(
                rx.try_recv().unwrap(),
                Tok {
                    kind: Kind::Identifier,
                    str: Some("mod".to_string()),
                    num: None,
                    position: Position { line: 2, column: 1 }
                }
            );

            assert_eq!(
                rx.try_recv().unwrap(),
                Tok {
                    kind: Kind::StringLiteral,
                    str: Some("fmt".to_string()),
                    num: None,
                    position: Position { line: 2, column: 6 }
                }
            );

            // assert_eq!(
            //     rx.try_recv()
            // )

            println!("Done")
        }
    }
}
