use self::value::Value;

use super::{
    error::ErrorReason,
    log::{log_debug, log_err},
    parser::Node,
};
use std::{borrow::Borrow, cell::RefCell, collections::HashMap, env, rc::Rc, sync::mpsc::Receiver};

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
    use super::r#type::Type;

    /// Value represents any value in the Speak programming language.
    /// Each value corresponds to some primitive or object value created
    /// during the execution of a Speak program.
    pub trait Value: Sized + std::fmt::Debug + Clone {
        // This value stores the actual value type.
        type UndelyingValue;

        fn value_type(&self) -> Type;
        fn string(&self) -> String;
        fn equals(&self, value: Self::UndelyingValue) -> bool;
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    struct Uint8(u8);

    impl Value for Uint8 {
        type UndelyingValue = u8;

        fn value_type(&self) -> Type {
            Type::Uint8
        }

        fn string(&self) -> String {
            self.0.to_string()
        }

        fn equals(&self, value: u8) -> bool {
            self.0 == value
        }
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    struct Uint16(u16);

    impl Value for Uint16 {
        type UndelyingValue = u16;

        fn value_type(&self) -> Type {
            Type::Uint16
        }

        fn string(&self) -> String {
            self.0.to_string()
        }

        fn equals(&self, value: u16) -> bool {
            self.0 == value
        }
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    struct Uint32(u32);

    impl Value for Uint32 {
        type UndelyingValue = u32;

        fn value_type(&self) -> Type {
            Type::Uint32
        }

        fn string(&self) -> String {
            self.0.to_string()
        }

        fn equals(&self, value: u32) -> bool {
            self.0 == value
        }
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    struct Uint64(u64);

    impl Value for Uint64 {
        type UndelyingValue = u64;

        fn value_type(&self) -> Type {
            Type::Uint64
        }

        fn string(&self) -> String {
            self.0.to_string()
        }

        fn equals(&self, value: u64) -> bool {
            self.0 == value
        }
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    struct Int8(i8);

    impl Value for Int8 {
        type UndelyingValue = i8;

        fn value_type(&self) -> Type {
            Type::Int8
        }

        fn string(&self) -> String {
            self.0.to_string()
        }

        fn equals(&self, value: i8) -> bool {
            self.0 == value
        }
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    struct Int16(i16);

    impl Value for Int16 {
        type UndelyingValue = i16;

        fn value_type(&self) -> Type {
            Type::Int16
        }

        fn string(&self) -> String {
            self.0.to_string()
        }

        fn equals(&self, value: i16) -> bool {
            self.0 == value
        }
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    struct Int32(i32);

    impl Value for Int32 {
        type UndelyingValue = i32;

        fn value_type(&self) -> Type {
            Type::Int32
        }

        fn string(&self) -> String {
            self.0.to_string()
        }

        fn equals(&self, value: i32) -> bool {
            self.0 == value
        }
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    struct Int64(i64);

    impl Value for Int64 {
        type UndelyingValue = i64;

        fn value_type(&self) -> Type {
            Type::Int64
        }

        fn string(&self) -> String {
            self.0.to_string()
        }

        fn equals(&self, value: i64) -> bool {
            self.0 == value
        }
    }

    #[derive(Debug, PartialEq, Clone)]
    struct Float32(f32);

    impl Value for Float32 {
        type UndelyingValue = f32;

        fn value_type(&self) -> Type {
            Type::Float32
        }

        fn string(&self) -> String {
            self.0.to_string()
        }

        fn equals(&self, value: f32) -> bool {
            self.0 == value
        }
    }

    #[derive(Debug, PartialEq, Clone)]
    struct Float64(f64);

    impl Value for Float64 {
        type UndelyingValue = f64;

        fn value_type(&self) -> Type {
            Type::Float64
        }

        fn string(&self) -> String {
            self.0.to_string()
        }

        fn equals(&self, value: f64) -> bool {
            self.0 == value
        }
    }

    #[derive(Debug, PartialEq, Clone)]
    pub struct String_(pub String);

    impl Value for String_ {
        type UndelyingValue = String;

        fn value_type(&self) -> Type {
            Type::String
        }

        fn string(&self) -> String {
            self.0.clone()
        }

        fn equals(&self, value: String) -> bool {
            self.0 == value
        }
    }
}

pub struct Engine {}

/// ValueTable is used anytime a map of names/labels to Speak Values is needed,
/// and is notably used to represent stack frames/heaps and CompositeValue dictionaries.
#[derive(Debug, Clone)]
pub struct ValueTable<V: Value>(HashMap<String, V>);

impl<V: Value> ValueTable<V> {
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
    Cons(Rc<RefCell<ValueTable<V>>>, Rc<StackFrame<V>>),
    Nil,
}

impl<V: Value> StackFrame<V> {
    fn new(value_table: ValueTable<V>, parent: StackFrame<V>) -> Self {
        Self::Cons(Rc::new(RefCell::new(value_table)), Rc::new(parent))
    }

    /// Get a value from the stack frame chain.
    fn get(&self, name: &str) -> Option<V> {
        if let StackFrame::Cons(frame, next_frame) = self {
            match frame.as_ref().borrow().get(name) {
                Some(v) => return Some(v.clone()),
                None => return next_frame.get(name),
            }
        }
        return None;
    }

    /// sets a value to the provided stack frame.
    fn set(&mut self, name: String, val: V) {
        if let StackFrame::Cons(frame, _) = self {
            frame.as_ref().borrow_mut().set(name, val)
        }
    }

    /// updates a value in the stack frame chain.
    fn up(&mut self, name: String, val: V) {
        if let StackFrame::Cons(frame, next_frame) = self {
            frame.as_ref().borrow_mut().0.insert(name.clone(), val);
        }
    }

    /// dumps the stack frame chain to return out.
    fn string(&self) -> Option<String> {
        if let StackFrame::Cons(frame, next_frame) = self {
            let mut entries = Vec::new();

            for (k, v) in &frame.as_ref().borrow().0 {
                let mut v_str = v.string();
                if v_str.len() > MAX_PRINT_LEN {
                    v_str = format!("{}...", &v_str[..MAX_PRINT_LEN])
                }
                entries.push(format!("{k} -> {v_str}"))
            }

            return Some(format!(
                "{{\n\t{}\n}} -parent-> {:?}",
                entries.join("\n\t"),
                next_frame
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
    pub fn eval<N: Node<V>>(&mut self, nodes: Receiver<N>, dump_frame: bool) {
        for node in nodes {
            if let Err(err) = node.eval(&mut self.frame, false) {
                log_err(&ErrorReason::Assert, &format!("eval error: {:?}", err));
                break;
            }
        }

        if dump_frame {
            self.dump();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stack_frame() {
        let mut frame = StackFrame::new(ValueTable::new(HashMap::new()), StackFrame::Nil);

        // test stackframe.set(), stackframe.get()
        frame.set("a".to_string(), value::String_("hello".to_string()));
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
        frame.up("a".to_string(), value::String_("mutated value".to_string()));
        assert!(frame
            .get("a")
            .expect("key must be present")
            .equals("mutated value".to_string()));

        //test stackframe.get, in parent frame
        let frame = StackFrame::Cons(
            Rc::new(RefCell::new(ValueTable::new(HashMap::new()))),
            Rc::new(frame),
        );
        assert!(frame
            .get("a")
            .expect("key must be present")
            .equals("mutated value".to_string()));
    }
}
