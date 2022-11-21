use super::{
    error::ErrorReason,
    log::{log_debug, log_err},
    parser::Node,
};
use num_traits::Num;
use std::{borrow::Borrow, cell::RefCell, collections::HashMap, env, rc::Rc, sync::mpsc::Receiver};

const MAX_PRINT_LEN: usize = 120;

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

    // Pointer type.
    Pointer,

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
        unimplemented!()
    }
}

/// Value represents any value in the Speak programming language.
/// Each value corresponds to some primitive or object value created
/// during the execution of a Speak program.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    // Numerical values.
    Uint8Value(u8),
    Uint16Value(u16),
    Uint32Value(u32),
    Uint64Value(u64),
    Int8Value(i8),
    Int16Value(i16),
    Int32Value(i32),
    Int64Value(i64),
    Float32Value(f32),
    Float64Value(f64),

    /// BoolValue represents a boolean value in Speak.
    BoolValue(bool),

    /// StringValue represents all characters and strings in Speak.
    StringValue(Vec<u8>),

    /// EmptyValue is the value of the empty identifier.
    /// it is globally unique and matches everything in equality.
    EmptyValue,
}

impl Value {
    // value_type returns the type of the value.
    fn value_type(&self) -> Type {
        match self {
            Value::Uint8Value(_) => Type::Uint8,
            Value::Uint16Value(_) => Type::Uint16,
            Value::Uint32Value(_) => Type::Uint32,
            Value::Uint64Value(_) => Type::Uint64,
            Value::Int8Value(_) => Type::Int8,
            Value::Int16Value(_) => Type::Int16,
            Value::Int32Value(_) => Type::Int32,
            Value::Int64Value(_) => Type::Int64,
            Value::Float32Value(_) => Type::Float32,
            Value::Float64Value(_) => Type::Float64,

            Value::EmptyValue => Type::Empty,
            Value::StringValue(_) => Type::String,
            Value::BoolValue(_) => Type::Bool,
        }
    }

    /// string returns the string representation of the value.
    pub fn string(&self) -> String {
        match self {
            Value::Uint8Value(v) => v.to_string(),
            Value::Uint16Value(v) => v.to_string(),
            Value::Uint32Value(v) => v.to_string(),
            Value::Uint64Value(v) => v.to_string(),
            Value::Int8Value(v) => v.to_string(),
            Value::Int16Value(v) => v.to_string(),
            Value::Int32Value(v) => v.to_string(),
            Value::Int64Value(v) => v.to_string(),
            Value::Float32Value(v) => v.to_string(),
            Value::Float64Value(v) => v.to_string(),

            Value::BoolValue(b) => b.to_string(),

            Value::StringValue(s) => String::from_utf8(s.clone()).unwrap(),

            Value::EmptyValue => String::from("()"),
        }
    }

    /// Equals reports whether the given value is deep-equal to the
    /// receiving value. It does not compare references.
    fn equals(&self, value: Value) -> bool {
        if Value::EmptyValue == value || Value::EmptyValue == self.clone() {
            return true;
        }

        let compare_numeric = || {
            if self.clone() != value {
                return <f64 as Num>::from_str_radix(&self.string(), 10).unwrap()
                    == <f64 as Num>::from_str_radix(&value.string(), 10).unwrap();
            }
            true
        };

        match self {
            Value::Uint8Value(_)
            | Value::Uint16Value(_)
            | Value::Uint32Value(_)
            | Value::Uint64Value(_)
            | Value::Int8Value(_)
            | Value::Int16Value(_)
            | Value::Int32Value(_)
            | Value::Int64Value(_)
            | Value::Float32Value(_)
            | Value::Float64Value(_) => compare_numeric(),

            Value::BoolValue(b) => match value {
                Value::BoolValue(b2) => b == &b2,
                _ => false,
            },

            Value::StringValue(_) => self.string() == value.string(),

            _ => false,
        }
    }
}

pub struct Engine {}

/// ValueTable is used anytime a map of names/labels to Speak Values is needed,
/// and is notably used to represent stack frames/heaps and CompositeValue dictionaries.
#[derive(Debug, Clone)]
struct ValueTable(HashMap<String, Value>);

impl ValueTable {
    fn new() -> Self {
        Self(HashMap::new())
    }

    fn get(&self, name: &str) -> Option<Value> {
        self.0.get(name).cloned()
    }

    fn set(&mut self, key: String, value: Value) {
        self.0.insert(key, value);
    }
}

/// StackFrame represents the heap of variables local to a particular function call frame,
/// and recursively references other parent StackFrames internally.
#[derive(Debug, Clone)]
pub enum StackFrame {
    Ptr(Rc<RefCell<ValueTable>>, Rc<StackFrame>),
    Nil,
}

impl StackFrame {
    /// Get a value from the stack frame chain.
    fn get(&self, name: &str) -> Option<Value> {
        if let StackFrame::Ptr(frame, next_frame) = self {
            match (*frame.clone()).borrow().get(name) {
                Some(v) => return Some(v),
                None => return next_frame.get(name.clone()),
            }
        }
        return None;
    }

    /// sets a value to the provided stack frame.
    fn set(&mut self, name: String, val: Value) {
        if let StackFrame::Ptr(frame, _) = self {
            (*frame.clone()).borrow_mut().set(name.clone(), val.clone())
        }
    }

    /// updates a value in the stack frame chain.
    fn up(&mut self, name: String, val: Value) {
        if let StackFrame::Ptr(frame, next_frame) = self {
            (*frame.clone())
                .borrow_mut()
                .0
                .insert(name.clone(), val.clone());
        }
    }

    /// dumps the stack frame chain to return out.
    fn string(&self) -> Option<String> {
        if let StackFrame::Ptr(frame, next_frame) = self {
            let mut entries = Vec::new();
            for (k, v) in (*frame.clone()).borrow().0.clone() {
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

#[test]
fn test_stack_frame() {
    let mut frame = StackFrame::Ptr(
        Rc::new(RefCell::new(ValueTable::new())),
        Rc::new(StackFrame::Nil),
    );

    // test stackframe.set(), stackframe.get()
    {
        frame.set(
            "a".to_string(),
            Value::StringValue("a".to_string().into_bytes()),
        );

        assert!(frame
            .get("a")
            .expect("key must be present")
            .equals(Value::StringValue("a".to_string().into_bytes())));
    }

    // test stackframe.string()
    {
        assert_eq!(
            frame.string().expect("frame must be present"),
            "{\n\ta -> a\n} -parent-> Nil".to_string()
        );
    }

    // test stackframe.up(), stackframe.get()
    {
        frame.up(
            "a".to_string(),
            Value::StringValue("mutated value".to_string().into_bytes()),
        );

        assert!(frame
            .get("a")
            .expect("key must be present")
            .equals(Value::StringValue("mutated value".to_string().into_bytes())));
    }
}

/// Context represents a single, isolated execution context with its global heap,
/// imports, call stack, and cwd (working directory).
pub struct Context {
    /// cwd is an always-absolute path to current working dir (of module system)
    cwd: String,
    /// The currently executing file's path, if any
    file: String,
    engine: Engine,
    /// Frame represents the Context's global heap
    frame: StackFrame,
}

impl Context {
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
    pub fn eval(&self, nodes: Receiver<Node>, dump_frame: bool) {
        for node in nodes {
            if let Err(err) = node.eval(&self.frame, false) {
                log_err(&ErrorReason::Assert, &format!("eval error: {:?}", err));
                break;
            }
        }

        if dump_frame {
            self.dump();
        }
    }
}
