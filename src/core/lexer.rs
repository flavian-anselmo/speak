use super::{
    error::{Err, ErrorReason},
    eval::r#type::Type,
    log::log_debug,
};
use regex::Regex;
use std::io::{BufRead, BufReader};

lazy_static! {
    static ref IDENTIFIER_REGEX: Regex =
        Regex::new(r"^[a-zA-Z_][a-zA-Z0-9_]*$").expect("regex identifier pattern is valid");
    static ref NUMBER_REGEX: Regex =
        Regex::new(r"^[+-]?\d+(_\d+)*(\.\d+)?$").expect("regex number pattern is valid");
}

// Kind is the sum type of all possible types
// of tokens in a Speak program
#[derive(Debug, Clone, PartialEq)]
pub enum Kind {
    Identifier,
    EmptyIdentifier,

    If,

    TrueLiteral,
    FalseLiteral,
    NumberLiteral,
    StringLiteral,
    EmptyLiteral,

    NegationOp,
    AssignOp,
    AccessorOp,
    EllipsisOp,
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
    LeftBrace,
    RightBrace,
    LeftBracket,
    RightBracket,
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
            Kind::EmptyLiteral => "()".to_string(),

            Kind::TypeName(t) => t.string(),
            Kind::Separator => "','".to_string(),
            Kind::Colon => "':'".to_string(),

            Kind::Bang => "'!'".to_string(),
            Kind::QuestionMark => "'?'".to_string(),

            Kind::NegationOp => "'~'".to_string(),
            Kind::AssignOp => "is".to_string(),
            Kind::AccessorOp => "'.'".to_string(),
            Kind::EllipsisOp => "..".to_string(),
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
            Kind::LeftBrace => "'{'".to_string(),
            Kind::RightBrace => "'}'".to_string(),
            Kind::LeftBracket => "'['".to_string(),
            Kind::RightBracket => "']'".to_string(),
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
    pub fn string(&self) -> String {
        match self.kind {
            Kind::Identifier | Kind::StringLiteral => {
                format!(
                    "{} '{}' [{}]",
                    self.kind.string(),
                    self.str.clone().unwrap(), // safe to unwrap, types matched always have str
                    self.position.string()
                )
            }

            Kind::NumberLiteral => {
                format!(
                    "{} {} [{}]",
                    self.kind.string(),
                    self.num.unwrap(), // safe to unwrap, types matched always have num
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
    let col_fn = |col, len| if len == 1 { col } else { col - (len - 1) };

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

        let mut entry = String::new();
        let mut last_line_column = (0, 0);

        let mut buf_iter = buf.chars().into_iter().enumerate().peekable();
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

            // if there is previous entry, commit it as arbitrary
            let mut commit_prev = || -> Result<bool, Err> {
                if !entry.is_empty() {
                    commit_arbitrary(
                        entry.clone(),
                        tokens,
                        &debug_lexer,
                        line,
                        col_fn(column, entry.len()),
                    )?;
                    entry.clear();
                    return Ok(true);
                }
                Ok(false)
            };

            match c {
                ' ' => {
                    commit_prev()?;
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
                                    message: r#"missing trailing symbol '"'"#.to_string(),
                                })
                            }
                        };
                    }
                }
                ':' => {
                    commit_prev()?;

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
                    if entry.is_empty() {
                        if let Some((_, _c)) = buf_iter.peek() {
                            if *_c == ' ' {
                                token_commit(Kind::EmptyIdentifier, tokens);
                                continue;
                            }
                        }
                    }

                    entry.push(c);
                    last_line_column.0 = line;
                    last_line_column.1 = column + 1;
                }
                ',' => {
                    commit_prev()?;
                    token_commit(Kind::Separator, tokens);
                }
                '.' => {
                    // if next token is `.`, tokenize `..` Ellipsis
                    if let Some((_, c)) = buf_iter.peek() {
                        if *c == '.' {
                            commit_prev()?;
                            token_commit(Kind::EllipsisOp, tokens);
                            buf_iter.next();
                            continue;
                        }
                    }

                    // if there is a previous entry let's try resolve as [Identifier][AccessorOp][Identifier]
                    if !entry.is_empty() && IDENTIFIER_REGEX.is_match(&entry) {
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
                    commit_prev()?;
                    token_commit(Kind::Bang, tokens);
                }
                '?' => {
                    commit_prev()?;
                    token_commit(Kind::QuestionMark, tokens);
                }
                '=' => {
                    commit_prev()?;
                    token_commit(Kind::EqualOp, tokens);
                }
                '(' => {
                    commit_prev()?;
                    if let Some((_, c)) = buf_iter.peek() {
                        if *c == ')' {
                            token_commit(Kind::EmptyLiteral, tokens);
                            buf_iter.next();
                            continue;
                        }
                    }

                    token_commit(Kind::LeftParen, tokens);
                }
                ')' => {
                    commit_prev()?;
                    token_commit(Kind::RightParen, tokens);
                }
                '{' => {
                    commit_prev()?;
                    token_commit(Kind::LeftBrace, tokens);
                }
                '}' => {
                    commit_prev()?;
                    token_commit(Kind::RightBrace, tokens);
                }
                '[' => {
                    commit_prev()?;
                    token_commit(Kind::LeftBracket, tokens);
                }
                ']' => {
                    commit_prev()?;
                    token_commit(Kind::RightBracket, tokens);
                }
                '~' => {
                    commit_prev()?;
                    token_commit(Kind::NegationOp, tokens);
                }
                '-' => {
                    commit_prev()?;

                    if let Some((_, '>')) = buf_iter.peek() {
                        // advance iterator and commit as arrow
                        buf_iter.next();
                        token_commit(Kind::FunctionArrow, tokens);
                        continue;
                    }
                    token_commit(Kind::SubtractOp, tokens);
                }
                '+' => {
                    commit_prev()?;
                    token_commit(Kind::AddOp, tokens);
                }
                '*' => {
                    commit_prev()?;
                    token_commit(Kind::MultiplyOp, tokens);
                }
                '/' => {
                    commit_prev()?;
                    if let Some((_, '/')) = buf_iter.peek() {
                        buf_iter.next(); // advance iterator to next item
                        break;
                    }

                    // commit as divideOp
                    token_commit(Kind::DivideOp, tokens);
                }
                '%' => {
                    commit_prev()?;
                    token_commit(Kind::ModulusOp, tokens);
                }
                '&' => {
                    commit_prev()?;
                    token_commit(Kind::LogicalAndOp, tokens);
                }
                '|' => {
                    commit_prev()?;
                    token_commit(Kind::LogicalOrOp, tokens);
                }
                '>' => {
                    commit_prev()?;
                    token_commit(Kind::GreaterThanOp, tokens);
                }
                '<' => {
                    commit_prev()?;
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
        if !entry.is_empty() {
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
        );
        Ok(())
    };

    match entry.as_str() {
        "number" => commit_token(Kind::TypeName(Type::Number), tokens),

        "bool" => commit_token(Kind::TypeName(Type::Bool), tokens),

        "string" => commit_token(Kind::TypeName(Type::String), tokens),

        "->" => commit_token(Kind::FunctionArrow, tokens),

        "true" => commit_token(Kind::TrueLiteral, tokens),

        "false" => commit_token(Kind::FalseLiteral, tokens),

        "if" => commit_token(Kind::If, tokens),

        "is" => commit_token(Kind::AssignOp, tokens),

        ".." => commit_token(Kind::EllipsisOp, tokens),

        _ => {
            // check if entry string is numerical
            if NUMBER_REGEX.is_match(entry.as_str()) {
                commit(
                    Tok {
                        kind: Kind::NumberLiteral,
                        str: None,
                        num: Some(
                            entry
                                .replace("_", "")
                                .parse::<f64>()
                                .expect("number is already checked by regex and should not fail"),
                        ),
                        position: Position { line, column },
                    },
                    tokens,
                    debug_lexer,
                );
                return Ok(());
            }

            // match as identifier
            match IDENTIFIER_REGEX.is_match(entry.as_str()) {
                true => {
                    commit(
                        Tok {
                            kind: Kind::Identifier,
                            str: Some(entry.to_string()),
                            num: None,
                            position: Position { line, column },
                        },
                        tokens,
                        debug_lexer,
                    );
                    Ok(())
                }
                false => Err(Err {
                    reason: ErrorReason::Syntax,
                    message: format!("invalid identifier: ({})", entry),
                }),
            }
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
                message: "invalid identifier: (123abc)".to_string()
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

        // tokenize function call on number, as identitier and numberliteral
        {
            tokens.clear();
            buf_reader = BufReader::new("sprint 10000-10".as_bytes());
            if let Err(err) = tokenize(&mut buf_reader, &mut tokens, true) {
                panic!("error: {}", err.message);
            }

            assert_eq!(
                tokens[0],
                Tok {
                    kind: Kind::Identifier,
                    str: Some("sprint".to_string()),
                    num: None,
                    position: Position { line: 1, column: 1 }
                }
            );

            assert_eq!(
                tokens[1],
                Tok {
                    kind: Kind::NumberLiteral,
                    str: None,
                    num: Some(10000.0),
                    position: Position { line: 1, column: 8 }
                }
            );

            assert_eq!(
                tokens[2],
                Tok {
                    kind: Kind::SubtractOp,
                    str: None,
                    num: None,
                    position: Position {
                        line: 1,
                        column: 13
                    }
                }
            );

            assert_eq!(
                tokens[3],
                Tok {
                    kind: Kind::NumberLiteral,
                    str: None,
                    num: Some(10.0),
                    position: Position {
                        line: 1,
                        column: 14
                    }
                }
            );
        }

        // tokenize a function signature
        {
            tokens.clear();
            buf_reader = BufReader::new("sum: a, b number -> number".as_bytes());
            if let Err(err) = tokenize(&mut buf_reader, &mut tokens, true) {
                panic!("error: {}", err.message);
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
