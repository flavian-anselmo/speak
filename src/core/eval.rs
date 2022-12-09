use self::value::Value;

use super::{
    error::{Err, ErrorReason},
    log::{log_debug, log_err},
    parser::Node,
};
use std::{collections::HashMap, env, sync::mpsc::Receiver};

const MAX_PRINT_LEN: usize = 120;

pub mod r#type {
    #[derive(Debug, PartialEq, Eq, Clone)]
    pub enum Type {
        // Unsigned integer types.
        Uint8, // `byte` is an alias
        Uint16,
        Uint32,
        Uint64, // `uint` is an alias

        // Signed integer types.
        Int8,
        Int16,
        Int32, // `int` | `rune` is an alias
        Int64,

        // Floating point types.
        Float32,
        Float64, // `float` is an alias

        // Boolean type.
        Bool,

        // String type.
        String,

        // Array type.
        Array { r#type: Box<Type> },

        // Map type.
        Map,

        // Function type.
        Function,

        // Interface type.
        Interface,

        // Struct type.
        Struct,

        // Enum type.
        Enum,

        // Empty type.
        Empty,
    }

    // type aliases
    impl Type {
        pub fn string(&self) -> String {
            match self {
                Type::Uint8 => "byte".to_string(),
                Type::Uint16 => "uint16".to_string(),
                Type::Uint32 => "uint32".to_string(),
                Type::Uint64 => "uint".to_string(),
                Type::Int8 => "int8".to_string(),
                Type::Int16 => "int16".to_string(),
                Type::Int32 => "int".to_string(),
                Type::Int64 => "int64".to_string(),
                Type::Float32 => "float32".to_string(),
                Type::Float64 => "float".to_string(),
                Type::Bool => "bool".to_string(),
                Type::String => "string".to_string(),
                Type::Array { r#type } => format!("[]{}", r#type.string()),
                Type::Map => "map".to_string(),
                Type::Function => "function".to_string(),
                Type::Interface => "interface".to_string(),
                Type::Struct => "struct".to_string(),
                Type::Enum => "enum".to_string(),
                Type::Empty => "empty".to_string(),
            }
        }
    }
}

pub mod value {
    use crate::core::{
        error::{Err, ErrorReason},
        lexer::number_type_to_enum,
    };
    use std::any::Any;
    use std::fmt::{Debug, Display};

    use super::r#type::Type;
    use num_traits::{cast, FromPrimitive, Num, NumCast, Signed, ToPrimitive};

    /// Value represents any value in the Speak programming language.
    /// Each value corresponds to some primitive or object value created
    /// during the execution of a Speak program.
    pub trait Value: Debug {
        // This value stores the actual value type.
        type UnderlyingValue;

        fn as_any(&mut self) -> &mut dyn Any;
        fn value_type(&self) -> Type;
        fn string(&self) -> String;
        fn equals(&self, value: Self::UnderlyingValue) -> bool;
    }

    impl Value for u8 {
        type UnderlyingValue = u8;

        fn as_any(&mut self) -> &mut dyn Any {
            self
        }

        fn value_type(&self) -> Type {
            Type::Uint8
        }

        fn string(&self) -> String {
            self.to_string()
        }

        fn equals(&self, value: u8) -> bool {
            self == &value
        }
    }

    impl Value for u16 {
        type UnderlyingValue = u16;

        fn as_any(&mut self) -> &mut dyn Any {
            self
        }

        fn value_type(&self) -> Type {
            Type::Uint16
        }

        fn string(&self) -> String {
            self.to_string()
        }

        fn equals(&self, value: u16) -> bool {
            self == &value
        }
    }

    impl Value for u32 {
        type UnderlyingValue = u32;

        fn as_any(&mut self) -> &mut dyn Any {
            self
        }

        fn value_type(&self) -> Type {
            Type::Uint32
        }

        fn string(&self) -> String {
            self.to_string()
        }

        fn equals(&self, value: u32) -> bool {
            self == &value
        }
    }

    impl Value for u64 {
        type UnderlyingValue = u64;

        fn as_any(&mut self) -> &mut dyn Any {
            self
        }

        fn value_type(&self) -> Type {
            Type::Uint64
        }

        fn string(&self) -> String {
            self.to_string()
        }

        fn equals(&self, value: u64) -> bool {
            self == &value
        }
    }

    impl Value for i8 {
        type UnderlyingValue = i8;

        fn as_any(&mut self) -> &mut dyn Any {
            self
        }

        fn value_type(&self) -> Type {
            Type::Int8
        }

        fn string(&self) -> String {
            self.to_string()
        }

        fn equals(&self, value: i8) -> bool {
            self == &value
        }
    }

    impl Value for i16 {
        type UnderlyingValue = i16;

        fn as_any(&mut self) -> &mut dyn Any {
            self
        }

        fn value_type(&self) -> Type {
            Type::Int16
        }

        fn string(&self) -> String {
            self.to_string()
        }

        fn equals(&self, value: i16) -> bool {
            self == &value
        }
    }

    impl Value for i32 {
        type UnderlyingValue = i32;

        fn as_any(&mut self) -> &mut dyn Any {
            self
        }

        fn value_type(&self) -> Type {
            Type::Int32
        }

        fn string(&self) -> String {
            self.to_string()
        }

        fn equals(&self, value: i32) -> bool {
            self == &value
        }
    }

    impl Value for i64 {
        type UnderlyingValue = i64;

        fn as_any(&mut self) -> &mut dyn Any {
            self
        }

        fn value_type(&self) -> Type {
            Type::Int64
        }

        fn string(&self) -> String {
            self.to_string()
        }

        fn equals(&self, value: i64) -> bool {
            self == &value
        }
    }

    impl Value for f32 {
        type UnderlyingValue = f32;

        fn as_any(&mut self) -> &mut dyn Any {
            self
        }

        fn value_type(&self) -> Type {
            Type::Float32
        }

        fn string(&self) -> String {
            self.to_string()
        }

        fn equals(&self, value: f32) -> bool {
            self == &value
        }
    }

    impl Value for f64 {
        type UnderlyingValue = f64;

        fn as_any(&mut self) -> &mut dyn Any {
            self
        }

        fn value_type(&self) -> Type {
            Type::Float64
        }

        fn string(&self) -> String {
            self.to_string()
        }

        fn equals(&self, value: f64) -> bool {
            self == &value
        }
    }

    impl Value for bool {
        type UnderlyingValue = bool;

        fn as_any(&mut self) -> &mut dyn Any {
            self
        }

        fn value_type(&self) -> Type {
            Type::Bool
        }

        fn string(&self) -> String {
            self.to_string()
        }

        fn equals(&self, value: bool) -> bool {
            self == &value
        }
    }

    impl Value for String {
        type UnderlyingValue = String;

        fn as_any(&mut self) -> &mut dyn Any {
            self
        }

        fn value_type(&self) -> Type {
            Type::String
        }

        fn string(&self) -> String {
            self.clone()
        }

        fn equals(&self, value: String) -> bool {
            self == &value
        }
    }

    impl Value for () {
        type UnderlyingValue = ();

        fn as_any(&mut self) -> &mut dyn Any {
            self
        }

        fn value_type(&self) -> Type {
            Type::Empty
        }

        fn string(&self) -> String {
            "null".to_string()
        }

        fn equals(&self, _: ()) -> bool {
            true
        }
    }
}

pub struct Engine {}

/// ValueTable is used anytime a map of names/labels to Speak Values is needed,
/// and is notably used to represent stack frames/heaps and CompositeValue dictionaries.
#[derive(Debug, Clone)]
pub struct VTable<V: Value>(HashMap<String, V>);

impl<V: Value> VTable<V> {
    fn new(map: HashMap<String, V>) -> Self {
        Self(map)
    }

    fn get(&self, name: &str) -> Option<&V> {
        self.0.get(name)
    }

    fn set(&mut self, key: String, value: V) {
        self.0.insert(key, value);
    }
}

/// StackFrame represents the heap of variables local to a particular function call frame,
/// and recursively references other parent StackFrames internally.
#[derive(Debug, Clone)]
pub enum StackFrame<V: Value> {
    Frame {
        item: VTable<V>,
        next: Box<StackFrame<V>>,
    },
    Nil,
}

impl<V: Value> StackFrame<V> {
    /// Creates a new stack frame with the provided value table and parent stack frame.
    fn new(value_table: VTable<V>, parent: StackFrame<V>) -> Self {
        Self::Frame {
            item: value_table,
            next: Box::new(parent),
        }
    }

    /// Get a value from the current stack frame chain.
    pub fn get(&self, name: &str) -> Option<&V> {
        if let StackFrame::Frame { item, next: _ } = self {
            return item.get(name);
        }

        return None;
    }

    /// Sets a value to the provided stack frame.
    fn set(&mut self, name: String, val: V) {
        if let StackFrame::Frame { item, next: _ } = self {
            item.set(name, val)
        }
    }

    /// Updates a value in the stack frame chain.
    fn up(&mut self, name: String, val: V) {
        if let StackFrame::Frame { item, next: _ } = self {
            let l = &mut item.0;
            l.insert(name, val);
        }
    }

    /// Provides the vtable to the function provided for mutation.
    fn mutate<F: FnMut(&mut VTable<V>) -> Result<(), Err>>(&mut self, mut f: F) -> Result<(), Err> {
        match self {
            StackFrame::Frame { item, next: _ } => f(item),
            StackFrame::Nil => Err(Err {
                message: "frame not present".to_string(),
                reason: ErrorReason::System,
            }),
        }
    }

    /// dumps the stack frame chain to return out.
    fn string(&self) -> Option<String> {
        if let StackFrame::Frame { item, next } = self {
            let mut entries = Vec::new();
            for (k, v) in &item.0 {
                let mut v_str = v.string();
                if v_str.len() > MAX_PRINT_LEN {
                    v_str = format!("{}...", &v_str[..MAX_PRINT_LEN])
                }
                entries.push(format!("{k} -> {v_str}"))
            }

            return Some(format!(
                "{{\n\t{}\n}} -parent-> {:?}",
                entries.join("\n\t"),
                next
            ));
        }

        return None;
    }
}

/// Context represents a single, isolated execution context with its global heap,
/// imports, call stack, and cwd (working directory).
pub struct Context<V: Value> {
    /// cwd is an always-absolute path to current working dir (of module system)
    cwd: String,
    /// The currently executing file's path, if any
    file: String,
    engine: Engine,
    /// Frame represents the Context's global heap
    frame: StackFrame<V>,
}

impl<V: Value> Context<V> {
    fn reset_wd(&mut self) {
        self.cwd = env::current_dir().unwrap().to_str().unwrap().to_string();
    }

    pub fn dump(&self) {
        if let Some(s) = self.frame.string() {
            log_debug(&format!("frame_dump:\n{}", s));
        }
    }

    // Takes a channel of Nodes to evaluate, and executes the Speak programs defined
    // in the syntax tree. Returning the last value of the last expression in the AST,
    // or an error to stderr if there was a runtime error.
    pub fn eval<T: Value, N: Node<V>>(
        &mut self,
        nodes: Vec<&mut N>,
        dump_frame: bool,
    ) -> Result<V, Err> {
        let len = nodes.len();
        for (i, node) in nodes.into_iter().enumerate() {
            match node.eval(&mut self.frame, false) {
                Ok(val) => {
                    if i == len - 1 {
                        if dump_frame {
                            self.dump();
                        }

                        // let bar: &dyn Bar = &123;
                        //      let val: Box<dyn Value<UnderlyingValue = u8>> = val;
                        // let val: Box<dyn Value> = Box::new(val);

                        return Ok(val);
                    }
                }
                Err(err) => {
                    log_err(&ErrorReason::Assert, &format!("eval error: {:?}", err));
                    if dump_frame {
                        self.dump();
                    }

                    log_err(&ErrorReason::Assert, &format!("eval error: {:?}", err));
                    return Err(err);
                }
            }
        }
        Ok(unimplemented!("this never calls"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stack_frame() {
        let mut frame = StackFrame::new(VTable::new(HashMap::new()), StackFrame::Nil);

        // test stackframe.set(), stackframe.get()
        frame.set("a".to_string(), "hello".to_string());
        assert!(frame
            .get("a")
            .expect("key must be present")
            .equals("hello".to_string()));

        // test stackframe.string()
        assert_eq!(
            frame.string().expect("frame must be present"),
            "{\n\ta -> hello\n} -parent-> Nil".to_string()
        );

        // test stackframe.up(), stackframe.get()
        frame.up("a".to_string(), "mutated value".to_string());
        assert!(frame
            .get("a")
            .expect("key must be present")
            .equals("mutated value".to_string()));

        //test stackframe.get, in parent frame
        let frame = StackFrame::Frame {
            item: VTable::new(HashMap::new()),
            next: Box::new(frame),
        };
        assert!(frame.get("a").is_none())
    }
}
