use super::{error::Err, eval::{Value, StackFrame}, lexer::Tok};
use crate::core::lexer;
use std::{
    fmt::Error,
    sync::mpsc::{Receiver, Sender},
};

/// Node represents an abstract syntax tree (AST) node in a Speak program.
#[derive(Debug, Clone)]
pub enum Node {
    FunctionExpNode(Box<FunctionExp>),
}

impl Node {
    fn string(&self) -> String {
        match self {
            Node::FunctionExpNode(f) => f.string(),
            _ => unimplemented!("string() not implemented for this node type"),
        }
    }

    fn position(&self) -> lexer::Position {
        match self {
            Node::FunctionExpNode(f) => f.position.clone(),
            _ => unimplemented!("position not implemented for node"),
        }
    }

    pub fn eval(&self, frame: &StackFrame, allow_thunk: bool) -> Result<Value, Error> {
        unimplemented!("Eval not implemented for node")
    }
}

fn poss(n: Node) -> String {
    n.position().string()
}

#[derive(Debug, Clone)]
pub struct FunctionExp {
    inputs: Vec<Node>,
    output: Node,
    // The function body may be empty for interface and function type declarations.
    body: Option<Node>,
    position: lexer::Position,
}

impl FunctionExp {
    pub fn string(&self) -> String {
        let args = self
            .inputs
            .clone()
            .into_iter()
            .map(|i| i.string())
            .collect::<Vec<String>>()
            .join(", ");
        format!("FUNCTION: {} -> {}", args, self.output.string(),)
    }
}

pub fn parse<T>(
    tokens_chan: Receiver<Tok<T>>,
    nodes_chan: Sender<Node>,
    fatal_error: bool,
    debug_parser: bool,
) -> Result<(), Err> {
    unimplemented!()
}
