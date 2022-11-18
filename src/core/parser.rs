use crate::core::{eval, lexer};
use std::collections::HashMap;

use super::eval::Value;

/// Node represents an abstract syntax tree (AST) node in a Speak program.
pub enum Node {}

impl Node {
    fn string(&self) -> String {
        unimplemented!()
    }

    fn position(&self) -> lexer::Position {
        unimplemented!()
    }
}

fn poss(n: Node) -> String {
    n.position().string()
}
