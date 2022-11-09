use std::io::BufReader;

// Kind is the sum type of all possible types
// of tokens in a Speak program
pub enum Kind {
    Separator,

    UnaryExpr,
    BinaryExpr,
    MatchExpr,
    MatchClause,

    Identifier,
    EmptyIdentifier,

    FunctionCall,

    NumberLiteral,
    StringLiteral,
    ObjectLiteral,
    ListLiteral,
    FunctionLiteral,

    TrueLiteral,
    FalseLiteral,

    // ambiguous operators and symbols
    AccessorOp,

    // =
    EqualOp,
    FunctionArrow,

    // :
    KeyValueSeparator,
    DefineOp,
    MatchColon,

    // -
    CaseArrow,
    Arrow,
    SubtractOp,

    // single char, unambiguous
    NegationOp,
    AddOp,
    MultiplyOp,
    DivideOp,
    ModulusOp,
    GreaterThanOp,
    LessThanOp,

    LogicalAndOp,
    LogicalOrOp,
    LogicalXorOp,

    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    LeftBrace,
    RightBrace,
}

impl Kind {
    fn string(&self) -> String {
        match self {
            Kind::UnaryExpr => "unary expression".to_string(),
            Kind::BinaryExpr => "binary expression".to_string(),

            Kind::TrueLiteral => "'true'".to_string(),
            Kind::FalseLiteral => "'false'".to_string(),

            Kind::AccessorOp => "'.'".to_string(),

            Kind::CaseArrow => "'=>'".to_string(),
            Kind::Arrow => "'->'".to_string(),

            Kind::NegationOp => "'~'".to_string(),
            Kind::AddOp => "'+'".to_string(),
            Kind::SubtractOp => "'-'".to_string(),
            Kind::MultiplyOp => "'*'".to_string(),
            Kind::DivideOp => "'/'".to_string(),
            Kind::ModulusOp => "'%'".to_string(),
            Kind::GreaterThanOp => "'>'".to_string(),
            Kind::LessThanOp => "'<'".to_string(),

            Kind::LogicalAndOp => "'&'".to_string(),
            Kind::LogicalOrOp => "'|'".to_string(),
            Kind::LogicalXorOp => "'^'".to_string(),

            Kind::Separator => "','".to_string(),
            Kind::LeftParen => "'('".to_string(),
            Kind::RightParen => "')'".to_string(),
            Kind::LeftBracket => "'['".to_string(),
            Kind::RightBracket => "']'".to_string(),
            Kind::LeftBrace => "'{'".to_string(),
            Kind::RightBrace => "'}'".to_string(),
            _ => "unknown token".to_string(),
        }
    }
}

pub struct Position {
    line: usize,
    column: usize,
}

impl Position {
    fn string(&self) -> String {
        format!("{}:{}", self.line, self.column)
    }
}

// Tok is the monomorphic struct representing all Ink program tokens
// in the lexer.
pub struct Tok {
    kind: Kind,
    // str and num are both present to implement Tok
    // as a monomorphic type for all tokens; will be zero
    // values often.
    str: String,
    num: f64,
    position: Position,
}

// Tokenize takes an io.Reader and transforms it into a stream of Tok (tokens).
//pub fn Tokenize(reader: BufReader) {}
