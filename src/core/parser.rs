use super::{
    error::{Err, ErrorReason},
    eval::StackFrame,
    eval::{
        r#type::Type,
        value::{self, Value},
    },
    lexer::{number_type_to_enum, Kind, Position, Tok},
};
use num_traits::{Num, Signed};
use std::{
    any::Any,
    borrow::BorrowMut,
    sync::mpsc::{Receiver, Sender},
};

/// Node represents an abstract syntax tree (AST) node in a Speak program.
pub trait Node<V: Value> {
    type UnderlyingType: Value;

    fn string(&self) -> String;
    fn position(&self) -> &Position;
    fn eval<'a>(
        &'a mut self,
        stack: &'a mut StackFrame<V>,
        allow_thunk: bool,
    ) -> Result<&'a Self::UnderlyingType, Err>;
}

#[derive(Debug, Clone)]
pub struct NumberLiteralNode<T: Value> {
    pub value: T,
    pub position: Position,
}

impl<T, V> Node<V> for NumberLiteralNode<T>
where
    V: Value,
    T: Value,
{
    type UnderlyingType = T;

    fn string(&self) -> String {
        self.value.string()
    }

    fn position(&self) -> &Position {
        &self.position
    }

    fn eval<'a>(&'a mut self, _: &mut StackFrame<V>, _: bool) -> Result<&'a T, Err> {
        Ok(&self.value)
    }
}

/// the number evaluation requires inferring the type of the number thus a more generic
/// implementation is required.
pub fn eval_number_literal<T: num_traits::Num>(value: &str) -> Result<T, Err> {
    match T::from_str_radix(value, 10) {
        Ok(v) => Ok(v),
        Err(_err) => Err(Err {
            message: "error occured evaluating number literal".to_string(),
            reason: ErrorReason::System,
        }),
    }
}

#[test]
fn this_test() {
    let res = eval_number_literal::<f32>("0.234");
    assert!(Ok(0.234f32) == res);
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

    fn position(&self) -> &Position {
        &self.position
    }

    fn eval<'a>(&'a mut self, _: &mut StackFrame<V>, _: bool) -> Result<&'a String, Err> {
        Ok(&self.value)
    }
}

pub struct BoolLiteralNode {
    pub value: bool,
    pub position: Position,
}

impl<V: Value> Node<V> for BoolLiteralNode {
    type UnderlyingType = bool;

    fn string(&self) -> String {
        self.value.to_string()
    }

    fn position(&self) -> &Position {
        &self.position
    }

    fn eval<'a>(&'a mut self, _: &mut StackFrame<V>, _: bool) -> Result<&'a bool, Err> {
        Ok(&self.value)
    }
}

pub struct EmptyIdentifierNode {
    pub position: Position,
}
impl<V: Value> Node<V> for EmptyIdentifierNode {
    type UnderlyingType = ();

    fn string(&self) -> String {
        "empty identifier".to_string()
    }

    fn position(&self) -> &Position {
        &self.position
    }

    fn eval(&mut self, _: &mut StackFrame<V>, _: bool) -> Result<&(), Err> {
        Ok(&())
    }
}

pub struct IdentifierNode {
    pub value: String,
    pub position: Position,
}

impl<V: Value> Node<V> for IdentifierNode {
    type UnderlyingType = V;

    fn string(&self) -> String {
        self.value.clone()
    }

    fn position(&self) -> &Position {
        &self.position
    }

    fn eval<'a>(&'a mut self, stack: &'a mut StackFrame<V>, _: bool) -> Result<&V, Err> {
        if let Some(val) = stack.get(&self.value) {
            return Ok(val);
        }

        Err(Err {
            message: format!("{} is not defined [{}]", self.value, self.position.string()),
            reason: ErrorReason::System,
        })
    }
}

#[derive(Debug, Clone)]
pub enum OperandNode<N: Signed> {
    NumberValue(N),
    BoolValue(bool),
    Identifier(String),
}

#[derive(Debug, Clone)]
pub struct UnaryExpressionNode<V: Value> {
    pub operator: Kind,
    pub operand: V,
    pub position: Position,
}

impl<V: Value> Node<V> for UnaryExpressionNode<V> {
    type UnderlyingType = V;

    fn string(&self) -> String {
        format!(
            "Unary {} ({})",
            self.operator.string(),
            self.operand.string()
        )
    }

    fn position(&self) -> &Position {
        &self.position
    }

    fn eval(&mut self, _: &mut StackFrame<V>, _: bool) -> Result<&V, Err> {
        match self.operator {
            Kind::NegationOp => match self.operand.value_type() {
                Type::Int8 => {
                    let v = self
                        .operand
                        .as_any()
                        .downcast_mut::<i8>()
                        .expect("this type is u8");

                    let v = self
                        .operand
                        .as_any()
                        .downcast_mut::<i8>()
                        .expect("this type is u8");
                    *v = -*v;
                }

                Type::Int16 => {
                    let v = self
                        .operand
                        .as_any()
                        .downcast_mut::<i16>()
                        .expect("this type is u8");
                    *v = -*v;
                }

                Type::Int32 => {
                    let v = self
                        .operand
                        .as_any()
                        .downcast_mut::<i32>()
                        .expect("this type is i32");
                    *v = -*v;
                }

                Type::Int64 => {
                    let v = self
                        .operand
                        .as_any()
                        .downcast_mut::<i64>()
                        .expect("this type is i64");
                    *v = -*v;
                }

                Type::Float32 => {
                    let v = self
                        .operand
                        .as_any()
                        .downcast_mut::<f32>()
                        .expect("this type is f32");
                    *v = -*v;
                }

                Type::Float64 => {
                    let v = self
                        .operand
                        .as_any()
                        .downcast_mut::<f64>()
                        .expect("this type is f64");
                    *v = -*v;
                }

                Type::Bool => {
                    let v = self
                        .operand
                        .as_any()
                        .downcast_mut::<bool>()
                        .expect("this type is bool");
                    *v = !*v;
                }

                _ => {
                    return Err(Err {
                        message: format!(
                            "{} is not a boolean or a number type [{}]",
                            self.operand.string(),
                            self.position.string()
                        ),
                        reason: ErrorReason::System,
                    })
                }
            },

            _ => {
                return Err(Err {
                    message: format!(
                        "invalid unary operator {} at {}",
                        self.operator.string(),
                        self.position.string()
                    ),
                    reason: ErrorReason::Syntax,
                });
            }
        }

        Ok(&self.operand)
    }
}

pub struct BinaryExpressionNode<N: num_traits::Signed> {
    pub operator: Kind,
    pub leftOperand: OperandNode<N>,
    pub rightOperand: OperandNode<N>,
    pub position: Position,
}

impl<V: Value, N: num_traits::Signed + std::fmt::Display + Clone> Node<V>
    for BinaryExpressionNode<N>
{
    type UnderlyingType = V;

    fn string(&self) -> String {
        format!(
            "Binary ({}) {} ({})",
            match self.leftOperand {
                OperandNode::NumberValue(ref v) => v.to_string(),
                OperandNode::BoolValue(ref v) => v.to_string(),
                OperandNode::Identifier(ref v) => v.clone(),
            },
            self.operator.string(),
            match self.rightOperand {
                OperandNode::NumberValue(ref v) => v.to_string(),
                OperandNode::BoolValue(ref v) => v.to_string(),
                OperandNode::Identifier(ref v) => v.clone(),
            }
        )
    }

    fn position(&self) -> &Position {
        &self.position
    }

    fn eval(&mut self, _stack: &mut StackFrame<V>, _allow_thunk: bool) -> Result<&V, Err> {
        if self.operator == Kind::AssignOp {
        } else if self.operator == Kind::AccessorOp {
        }

        match self.operator {
            Kind::AssignOp => {}
            Kind::AccessorOp => {}
            _ => {}
        }

        unimplemented!()
    }
}

#[derive(Debug)]
pub struct FunctionCallNode<T: Sized> {
    function: T,
    arguments: Vec<T>,
}

impl< V: Value, T: Node< V>> Node< V> for FunctionCallNode<T> {
    type UnderlyingType = V;

    fn string(&self) -> String {
        self.arguments.iter().fold(
            format!("Call ({}) on (", self.function.string()),
            |acc, arg| format!("{}, {}", acc, arg.string()),
        )
    }

    fn position(&self) -> &Position {
        &self.function.position()
    }

    fn eval(&mut self, _stack: &mut StackFrame<V>, _allow_thunk: bool) -> Result<&V, Err> {
        todo!()
    }
}

pub fn parse<V, N, T>(
    tokens_chan: Receiver<Tok<T>>,
    nodes_chan: Sender<N>,
    fatal_error: bool,
    debug_parser: bool,
) -> Result<(), Err> {
    unimplemented!()
}
