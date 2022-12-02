use super::{
    error::{Err, ErrorReason},
    eval::value::Value,
    eval::StackFrame,
    lexer::{Position, Tok},
};
use std::sync::mpsc::{Receiver, Sender};

/// Node represents an abstract syntax tree (AST) node in a Speak program.
pub trait Node<V: Value> {
    type UnderlyingType;

    fn string(&self) -> String;
    fn position(&self) -> Position;
    fn eval(
        &self,
        stack: &mut StackFrame<V>,
        allow_thunk: bool,
    ) -> Result<Self::UnderlyingType, Err>;
}

#[derive(Debug, Clone)]
pub struct NumberLiteralNode<T: num_traits::Num> {
    pub value: T,
    pub position: Position,
}

impl<T, V> Node<V> for NumberLiteralNode<T>
where
    V: Value,
    T: num_traits::Num + std::fmt::Display,
{
    type UnderlyingType = T;

    fn string(&self) -> String {
        self.value.to_string()
    }

    fn position(&self) -> Position {
        self.position.clone()
    }

    fn eval(&self, _stack: &mut StackFrame<V>, _allow_thunk: bool) -> Result<T, Err> {
        match T::from_str_radix(self.value.to_string().as_str(), 10) {
            Ok(v) => Ok(v),
            Err(_err) => Err(Err {
                message: "error occured evaluation number literal".to_string(),
                reason: ErrorReason::System,
            }),
        }
    }
}

pub struct StringLiteralNode {
    pub value: String,
    pub position: Position,
}

impl<V: Value> Node<V> for StringLiteralNode {
    type UnderlyingType = String;

    fn string(&self) -> String {
        self.value.clone()
    }

    fn position(&self) -> Position {
        self.position.clone()
    }

    fn eval(&self, _stack: &mut StackFrame<V>, _allow_thunk: bool) -> Result<String, Err> {
        Ok(self.value.clone())
    }
}

// #[derive(Debug, Clone)]
// pub struct FunctionExp<V: Value> {
//     inputs: Vec<Box<dyn Node<Box<dyn Value>>>>,
//     output: N,
//     // The function body may be empty for interface and function type declarations.
//     body: [N],
//     position: Position,
// }

// impl<V, N> FunctionExp<V, N>
// where
//     V: Value,
//     N: Node<V>,
// {
//     pub fn string(&self) -> String {
//         let args = self
//             .inputs
//             .clone()
//             .into_iter()
//             .map(|i| i.string())
//             .collect::<Vec<String>>()
//             .join(", ");
//         format!("FUNCTION: {} -> {}", args, self.output.string(),)
//     }
// }

pub fn parse<V, N, T>(
    tokens_chan: Receiver<Tok<T>>,
    nodes_chan: Sender<N>,
    fatal_error: bool,
    debug_parser: bool,
) -> Result<(), Err> {
    unimplemented!()
}
