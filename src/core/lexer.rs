use super::{
    error::{Err, ErrorReason},
    eval::r#type::Type,
    log::log_debug,
};
use regex::Regex;
use std::io::{BufRead, BufReader};

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

    If,

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
    GreaterThanOp,
    LessThanOp,
    EqualOp,

    TypeName(Type),
    Separator,
    Colon,

    Bang,
    QuestionMark,

    ModuleAccessor,
    FunctionArrow,

    LeftParen,
    RightParen,
    // LeftBracket,
    // RightBracket,
}

impl Kind {
    pub fn string(&self) -> String {
        match self {
            // Kind::Expr => "expression".to_string(),
            Kind::Identifier => "identifier".to_string(),
            Kind::EmptyIdentifier => "'_'".to_string(),

            Kind::If => "if".to_string(),

            Kind::TrueLiteral => "true literal".to_string(),
            Kind::FalseLiteral => "false literal".to_string(),
            Kind::NumberLiteral => "number literal".to_string(),
            Kind::StringLiteral => "string literal".to_string(),

            Kind::TypeName(t) => t.string(),
            Kind::Separator => "','".to_string(),
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
            Kind::GreaterThanOp => "'>'".to_string(),
            Kind::LessThanOp => "'<'".to_string(),
            Kind::EqualOp => "'='".to_string(),

            Kind::FunctionArrow => "->".to_string(),
            Kind::ModuleAccessor => "::".to_string(),

            Kind::LeftParen => "'('".to_string(),
            Kind::RightParen => "')'".to_string(),
            // Kind::LeftBracket => "'['".to_string(),
            // Kind::RightBracket => "']'".to_string(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Position {
    pub line: usize,
    pub column: usize,
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
    pub kind: Kind,
    pub str: Option<String>,
    pub num: Option<f64>,
    pub position: Position,
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
    tokens: &mut Vec<Tok>,
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
        //let mut count = 0;

        //   let mut comment = false;
        let mut entry = String::new();
        let mut last_line_column = (0, 0);
        while let Some((column, c)) = buf_iter.next() {
            let token_commit = |kind, tokens| {
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
                    tokens,
                    &debug_lexer,
                )
            };

            match c {
                ' ' => {
                    // if there is previous entry, commit it as arbitrary
                    if entry.len() > 0 {
                        commit_arbitrary(
                            entry.clone(),
                            tokens,
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
                                                column: col_fn(column, entry.len()) - 1,
                                            },
                                        },
                                        tokens,
                                        &debug_lexer,
                                    );
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
                            tokens,
                            &debug_lexer,
                            line,
                            col_fn(column, entry.len()),
                        )?;
                        entry.clear();
                    }

                    // lookahead for another ':', mkaing up ::; module accessor
                    if let Some((_, c)) = buf_iter.peek() {
                        if *c == ':' {
                            token_commit(Kind::ModuleAccessor, tokens);
                            buf_iter.next();
                            continue;
                        }
                    }
                    token_commit(Kind::Colon, tokens);
                }
                '_' => {
                    token_commit(Kind::EmptyIdentifier, tokens);
                }
                ',' => {
                    // if there is previous entry, commit it as identifier
                    if entry.len() > 0 {
                        commit_arbitrary(
                            entry.clone(),
                            tokens,
                            &debug_lexer,
                            line,
                            col_fn(column, entry.len()),
                        )?;
                        entry.clear();
                    }

                    token_commit(Kind::Separator, tokens);
                }
                '.' => {
                    // if there is a previous entry let's try resolve as [Identifier][AccessorOp][Identifier]
                    if entry.len() > 0 && IDENTIFIER_REGEX.is_match(&entry) {
                        commit_arbitrary(
                            entry.clone(),
                            tokens,
                            &debug_lexer,
                            line,
                            col_fn(column, entry.len()),
                        )?;

                        entry.clear();
                        token_commit(Kind::AccessorOp, tokens);
                        continue;
                    }

                    // should later resolve as [Number][.][Number]
                    entry.push(c);
                    last_line_column.0 = line;
                    last_line_column.1 = column + 1;
                }
                '!' => {
                    token_commit(Kind::Bang, tokens);
                }
                '?' => {
                    token_commit(Kind::QuestionMark, tokens);
                }
                '=' => {
                    token_commit(Kind::EqualOp, tokens);
                }
                '(' => {
                    token_commit(Kind::LeftParen, tokens);
                }
                ')' => {
                    token_commit(Kind::RightParen, tokens);
                }
                '~' => {
                    token_commit(Kind::NegationOp, tokens);
                }
                '-' => {
                    if let Some((_, '>')) = buf_iter.peek() {
                        entry.push(c);
                        continue;
                    }
                    token_commit(Kind::SubtractOp, tokens);
                }
                '+' => {
                    token_commit(Kind::AddOp, tokens);
                }
                '*' => {
                    token_commit(Kind::MultiplyOp, tokens);
                }
                '/' => {
                    if let Some((_, '/')) = buf_iter.peek() {
                        buf_iter.next(); // advance iterator to next item
                        break;
                    }

                    // commit as divideOp
                    token_commit(Kind::DivideOp, tokens);
                }
                '%' => {
                    token_commit(Kind::ModulusOp, tokens);
                }
                '&' => {
                    token_commit(Kind::LogicalAndOp, tokens);
                }
                '|' => {
                    token_commit(Kind::LogicalOrOp, tokens);
                }
                '>' => {
                    // if the previous entry has '-', this is a function arrow
                    if entry == "-" {
                        commit_arbitrary(
                            entry.clone() + ">",
                            tokens,
                            &debug_lexer,
                            line,
                            col_fn(column, entry.len()),
                        )?;

                        entry.clear();
                        continue;
                    }

                    token_commit(Kind::GreaterThanOp, tokens);
                }
                '<' => {
                    token_commit(Kind::LessThanOp, tokens);
                }
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
                tokens,
                &debug_lexer,
                last_line_column.0,
                col_fn(last_line_column.1, entry.len()),
            )?;
        }

        line += 1;
    }

    Ok(())
}

fn commit(tok: Tok, tokens: &mut Vec<Tok>, debug_lexer: &bool) {
    if *debug_lexer {
        log_debug(&format!("lexer -> {}", tok.string()));
    }
    tokens.push(tok);
}

fn commit_arbitrary(
    entry: String,
    tokens: &mut Vec<Tok>,
    debug_lexer: &bool,
    line: usize,
    column: usize,
) -> Result<(), Err> {
    // whitespace, nothing to parse
    if entry.is_empty() {
        return Ok(());
    }

    let commit_token = |kind, tokens| {
        commit(
            Tok {
                kind,
                str: None,
                num: None,
                position: Position { line, column },
            },
            tokens,
            debug_lexer,
        )
    };

    match entry.as_str() {
        "number" => Ok(commit_token(Kind::TypeName(Type::Number), tokens)),

        "bool" => Ok(commit_token(Kind::TypeName(Type::Bool), tokens)),

        "string" => Ok(commit_token(Kind::TypeName(Type::String), tokens)),

        "->" => Ok(commit_token(Kind::FunctionArrow, tokens)),

        "true" => Ok(commit_token(Kind::TrueLiteral, tokens)),

        "false" => Ok(commit_token(Kind::FalseLiteral, tokens)),

        "()" => Ok(commit_token(Kind::TypeName(Type::Empty), tokens)),

        "if" => Ok(commit_token(Kind::If, tokens)),

        "is" => Ok(commit_token(Kind::AssignOp, tokens)),

        _ => {
            // check if entry string is numerical
            if let Ok(num) = entry.parse::<f64>() {
                return Ok(commit(
                    Tok {
                        kind: Kind::NumberLiteral,
                        str: None,
                        num: Some(num),
                        position: Position { line, column },
                    },
                    tokens,
                    debug_lexer,
                ));
            }

            // identifiers should start with a number: a-z, A-Z, or _
            if !IDENTIFIER_REGEX.is_match(entry.as_str()) {
                return Err(Err {
                    reason: ErrorReason::Syntax,
                    message: format!("invalid identifier: {}", entry),
                });
            }

            Ok(commit(
                Tok {
                    kind: Kind::Identifier,
                    str: Some(entry.to_string()),
                    num: None,
                    position: Position { line, column },
                },
                tokens,
                debug_lexer,
            ))
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::{env, fs};
    #[test]
    fn test_commit_arbitrary() {
        // let (tx, rx) = channel::<Tok>();
        let mut tokens = Vec::new();

        tokens.clear();
        commit_arbitrary("number".to_string(), &mut tokens, &false, 1, 1)
            .expect("commit does not fail");

        assert_eq!(
            tokens[0],
            Tok {
                kind: Kind::TypeName(Type::Number),
                str: None,
                num: None,
                position: Position { line: 1, column: 1 }
            }
        );

        tokens.clear();
        commit_arbitrary("->".to_string(), &mut tokens, &false, 1, 1)
            .expect("commit does not fail");
        assert_eq!(
            tokens[0],
            Tok {
                kind: Kind::FunctionArrow,
                str: None,
                num: None,
                position: Position { line: 1, column: 1 }
            }
        );

        tokens.clear();
        commit_arbitrary("123.23".to_string(), &mut tokens, &false, 1, 1)
            .expect("commit does not fail");
        assert_eq!(
            tokens[0],
            Tok {
                kind: Kind::NumberLiteral,
                str: None,
                num: Some(123.23),
                position: Position { line: 1, column: 1 }
            }
        );

        // test random identifier
        tokens.clear();
        commit_arbitrary("_abc".to_string(), &mut tokens, &false, 1, 1)
            .expect("commit does not fail");
        assert_eq!(
            tokens[0],
            Tok {
                kind: Kind::Identifier,
                str: Some("_abc".to_string()),
                num: None,
                position: Position { line: 1, column: 1 }
            }
        );

        assert_eq!(
            commit_arbitrary("123abc".to_string(), &mut tokens, &false, 1, 1).unwrap_err(),
            Err {
                reason: ErrorReason::Syntax,
                message: "invalid identifier: 123abc".to_string()
            }
        );
    }

    #[test]
    fn test_tokenize() {
        let mut tokens = Vec::new();
        let mut buf_reader: BufReader<&[u8]>;

        // comments are ignored
        {
            buf_reader = BufReader::new("// this is a comment".as_bytes());
            match tokenize(&mut buf_reader, &mut tokens, true) {
                Ok(_) => (),
                Err(e) => panic!("error: {}", e.message),
            }
            assert_eq!(tokens.len(), 0);

            buf_reader = BufReader::new(
                "   // this is a spaced comment with an identation of 3 space char".as_bytes(),
            );
            match tokenize(&mut buf_reader, &mut tokens, true) {
                Ok(_) => (),
                Err(e) => panic!("error: {}", e.message),
            }

            assert_eq!(tokens.len(), 0);
        }

        // single char tokens
        {
            tokens.clear();
            buf_reader = BufReader::new(",".as_bytes());
            match tokenize(&mut buf_reader, &mut tokens, true) {
                Ok(_) => (),
                Err(e) => panic!("error: {}", e.message),
            }
            assert_eq!(
                tokens[0],
                Tok {
                    kind: Kind::Separator,
                    str: None,
                    num: None,
                    position: Position { line: 1, column: 1 }
                }
            );

            tokens.clear();
            buf_reader = BufReader::new(":".as_bytes());
            match tokenize(&mut buf_reader, &mut tokens, true) {
                Ok(_) => (),
                Err(e) => panic!("error: {}", e.message),
            }
            assert_eq!(
                tokens[0],
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
            tokens.clear();
            buf_reader = BufReader::new("// This is module declaration.\nmod \"fmt\"".as_bytes());
            if let Err(err) = tokenize(&mut buf_reader, &mut tokens, true) {
                panic!("error: {}", err.message);
            }

            assert_eq!(
                tokens[0],
                Tok {
                    kind: Kind::Identifier,
                    str: Some("mod".to_string()),
                    num: None,
                    position: Position { line: 2, column: 1 }
                }
            );

            assert_eq!(
                tokens[1],
                Tok {
                    kind: Kind::StringLiteral,
                    str: Some("fmt".to_string()),
                    num: None,
                    position: Position { line: 2, column: 5 }
                }
            );
        }

        // tokenize a function signature
        {
            tokens.clear();
            buf_reader = BufReader::new("sum: a, b number -> number".as_bytes());
            match tokenize(&mut buf_reader, &mut tokens, true) {
                Ok(_) => (),
                Err(e) => panic!("error: {}", e.message),
            }

            assert_eq!(
                tokens[0],
                Tok {
                    kind: Kind::Identifier,
                    str: Some("sum".to_string()),
                    num: None,
                    position: Position { line: 1, column: 1 }
                }
            );

            assert_eq!(
                tokens[1],
                Tok {
                    kind: Kind::Colon,
                    str: None,
                    num: None,
                    position: Position { line: 1, column: 4 }
                }
            );

            assert_eq!(
                tokens[2],
                Tok {
                    kind: Kind::Identifier,
                    str: Some("a".to_string()),
                    num: None,
                    position: Position { line: 1, column: 6 }
                }
            );

            assert_eq!(
                tokens[3],
                Tok {
                    kind: Kind::Separator,
                    str: None,
                    num: None,
                    position: Position { line: 1, column: 7 }
                }
            );

            assert_eq!(
                tokens[4],
                Tok {
                    kind: Kind::Identifier,
                    str: Some("b".to_string()),
                    num: None,
                    position: Position { line: 1, column: 9 }
                }
            );

            assert_eq!(
                tokens[5],
                Tok {
                    kind: Kind::TypeName(Type::Number),
                    str: None,
                    num: None,
                    position: Position {
                        line: 1,
                        column: 11
                    }
                }
            );

            assert_eq!(
                tokens[6],
                Tok {
                    kind: Kind::FunctionArrow,
                    str: None,
                    num: None,
                    position: Position {
                        line: 1,
                        column: 18
                    }
                }
            );

            assert_eq!(
                tokens[7],
                Tok {
                    kind: Kind::TypeName(Type::Number),
                    str: None,
                    num: None,
                    position: Position {
                        line: 1,
                        column: 21
                    }
                }
            );
        }
    }

    #[test]
    fn test_speak_files() {
        let cwd = env::current_dir().expect("there must be a wd");
        let mut tokens = Vec::new();
        let mut buf_reader: BufReader<&[u8]>;

        // hello_world.spk
        {
            let data = fs::read(cwd.clone().join("samples/hello_world.spk"))
                .expect("will resolve to the hello_world.spk file");
            buf_reader = BufReader::new(&data);

            if let Err(err) = tokenize(&mut buf_reader, &mut tokens, true) {
                panic!("error: {}", err.message);
            }

            assert_eq!(
                tokens[0],
                Tok {
                    kind: Kind::Identifier,
                    str: Some("println".to_string()),
                    num: None,
                    position: Position { line: 2, column: 1 }
                }
            );

            assert_eq!(
                tokens[1],
                Tok {
                    kind: Kind::StringLiteral,
                    str: Some("Hello World!".to_string()),
                    num: None,
                    position: Position { line: 2, column: 9 }
                }
            );
        }
    }
}
