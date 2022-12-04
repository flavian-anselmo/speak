use super::{
    error::{Err, ErrorReason},
    eval::StackFrame,
    eval::{
        r#type::Type,
        value::{self, Bool, Value},
    },
    lexer::{number_type_to_enum, Kind, Position, Tok},
};
use num_traits::{NumCast, Signed};
use std::{
    any::Any,
    borrow::BorrowMut,
    sync::mpsc::{Receiver, Sender},
};

/// Node represents an abstract syntax tree (AST) node in a Speak program.
pub trait Node<'a, V: Value> {
    type UnderlyingType;

    fn string(&self) -> String;
    fn position(&self) -> &Position;
    fn eval(
        &'a mut self,
        stack: &'a mut StackFrame<V>,
        allow_thunk: bool,
    ) -> Result<&'a Self::UnderlyingType, Err>;
}

#[derive(Debug, Clone)]
pub struct NumberLiteralNode<T: num_traits::Num> {
    pub value: T,
    pub position: Position,
}

impl<'a, T, V> Node<'a, V> for NumberLiteralNode<T>
where
    V: Value,
    T: num_traits::Num + std::fmt::Display,
{
    type UnderlyingType = T;

    fn string(&self) -> String {
        self.value.to_string()
    }

    fn position(&self) -> &Position {
        &self.position
    }

    fn eval(&'a mut self, _: &mut StackFrame<V>, _: bool) -> Result<&(T), Err> {
        unimplemented!("NumberLiteralNode::eval is not implemented")
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

impl<'a, V: Value> Node<'a, V> for StringLiteralNode {
    type UnderlyingType = String;

    fn string(&self) -> String {
        self.value.clone()
    }

    fn position(&self) -> &Position {
        &self.position
    }

    fn eval(&mut self, _: &mut StackFrame<V>, _: bool) -> Result<&String, Err> {
        Ok(&self.value)
    }
}

pub struct BoolLiteralNode {
    pub value: bool,
    pub position: Position,
}

impl<'a, V: Value> Node<'a, V> for BoolLiteralNode {
    type UnderlyingType = bool;

    fn string(&self) -> String {
        self.value.to_string()
    }

    fn position(&self) -> &Position {
        &self.position
    }

    fn eval(&mut self, _: &mut StackFrame<V>, _: bool) -> Result<&bool, Err> {
        Ok(&self.value)
    }
}

pub struct EmptyIdentifierNode {
    pub position: Position,
}

impl<'a, V: Value> Node<'a, V> for EmptyIdentifierNode {
    type UnderlyingType = ();

    fn string(&self) -> String {
        "empty identifier".to_string()
    }

    fn position(&self) -> &Position {
        &self.position
    }

    fn eval(&mut self, _: &mut StackFrame<V>, _: bool) -> Result<&(), Err> {
        unimplemented!("EmptyIdentifierNode::eval")
    }
}

pub struct IdentifierNode {
    pub value: String,
    pub position: Position,
}

impl<'a, V: Value> Node<'a, V> for IdentifierNode {
    type UnderlyingType = V;

    fn string(&self) -> String {
        self.value.clone()
    }

    fn position(&self) -> &Position {
        &self.position
    }

    fn eval(&'a mut self, stack: &'a mut StackFrame<V>, _: bool) -> Result<&V, Err> {
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

impl<'a, V: Value> Node<'a, V> for UnaryExpressionNode<V> {
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

    fn eval(&'a mut self, _: &mut StackFrame<V>, _: bool) -> Result<&V, Err> {
        match self.operator {
            Kind::NegationOp => match self.operand.value_type() {
                Type::Uint8 => {
                    self.operand
                        .as_any()
                        .downcast_mut::<value::Uint8>()
                        .expect("this type is u8")
                        .mutate(|v| *v = !*v);
                    Ok(&self.operand)
                }
                Type::Uint16 => {
                    self.operand
                        .as_any()
                        .downcast_mut::<value::Uint8>()
                        .expect("this type is u16")
                        .mutate(|v| *v = !*v);
                    Ok(&self.operand)
                }

                Type::Uint32 => {
                    self.operand
                        .as_any()
                        .downcast_mut::<value::Uint8>()
                        .expect("this type is u32")
                        .mutate(|v| *v = !*v);
                    Ok(&self.operand)
                }

                Type::Uint64 => {
                    self.operand
                        .as_any()
                        .downcast_mut::<value::Uint8>()
                        .expect("this type is u64")
                        .mutate(|v| *v = !*v);
                    Ok(&self.operand)
                }

                Type::Int8 => {
                    self.operand
                        .as_any()
                        .downcast_mut::<value::Int8>()
                        .expect("this type is i8")
                        .mutate(|v| *v = -*v);
                    Ok(&self.operand)
                }

                Type::Int16 => {
                    self.operand
                        .as_any()
                        .downcast_mut::<value::Int16>()
                        .expect("this type is i16")
                        .mutate(|v| *v = -*v);
                    Ok(&self.operand)
                }

                Type::Int32 => {
                    self.operand
                        .as_any()
                        .downcast_mut::<value::Int32>()
                        .expect("this type is i32")
                        .mutate(|v| *v = -*v);
                    Ok(&self.operand)
                }

                Type::Int64 => {
                    self.operand
                        .as_any()
                        .downcast_mut::<value::Int64>()
                        .expect("this type is i64")
                        .mutate(|v| *v = -*v);
                    Ok(&self.operand)
                }

                Type::Float32 => {
                    self.operand
                        .as_any()
                        .downcast_mut::<value::Float32>()
                        .expect("this type is f32")
                        .mutate(|v| *v = -*v);
                    Ok(&self.operand)
                }

                Type::Float64 => {
                    self.operand
                        .as_any()
                        .downcast_mut::<value::Float64>()
                        .expect("this type is f64")
                        .mutate(|v| *v = -*v);
                    Ok(&self.operand)
                }

                Type::Bool => {
                    self.operand
                        .as_any()
                        .downcast_mut::<value::Bool>()
                        .expect("this type is bool")
                        .mutate(|v| *v = !*v);
                    Ok(&self.operand)
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
    }
}

pub struct BinaryExpressionNode<N: num_traits::Signed> {
    pub operator: Kind,
    pub leftOperand: OperandNode<N>,
    pub rightOperand: OperandNode<N>,
    pub position: Position,
}

impl<'a, V: Value, N: num_traits::Signed + std::fmt::Display + Clone> Node<'a, V>
    for BinaryExpressionNode<N>
{
    type UnderlyingType = OperandNode<N>;

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

    fn eval(
        &mut self,
        _stack: &mut StackFrame<V>,
        _allow_thunk: bool,
    ) -> Result<&OperandNode<N>, Err> {
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

pub struct FunctionCallNode<T> {
    function: T,
    arguments: [T],
}

impl<'a, V: Value, T: Node<'a, V>> Node<'a, V> for FunctionCallNode<T> {
    type UnderlyingType = ();

    fn string(&self) -> String {
        self.arguments.iter().fold(
            format!("Call ({}) on (", self.function.string()),
            |acc, arg| format!("{}, {}", acc, arg.string()),
        )
    }

    fn position(&self) -> &Position {
        &self.function.position()
    }

    fn eval(&mut self, _stack: &mut StackFrame<V>, _allow_thunk: bool) -> Result<&(), Err> {
        Ok(&())
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
