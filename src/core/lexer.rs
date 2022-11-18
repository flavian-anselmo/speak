use std::{io::BufReader, sync::mpsc::Sender};

// Kind is the sum type of all possible types
// of tokens in a Speak program
#[derive(Debug, Clone)]
pub enum Kind {
    FunctionExpr,
}

impl Kind {
    fn string(&self) -> String {
        match self {
            _ => unimplemented!(),
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
    num: Option<f64>,
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
    unbuffered: BufReader<R>,
    tokens_chan: Sender<Tok>,
    fatal_err: bool,
    debug_lexer: bool,
) {
}
