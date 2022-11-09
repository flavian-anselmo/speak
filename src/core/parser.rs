use crate::core::{eval, lexer};
use std::collections::HashMap;

use super::eval::Value;

/// Node represents an abstract syntax tree (AST) node in a Speak program.
pub trait Node {
    fn string(&self) -> String;
    fn position(&self) -> lexer::Position;
}
