use super::{error::ErrorReason, log::log_err};
use std::collections::HashMap;

const MAX_PRINT_LEN: usize = 120;

#[derive(Debug, PartialEq, Eq)]
pub enum Types {
    // Unsigned integer types.
    Uint8,
    Uint16,
    Uint32,
    Uint64,

    // Signed integer types.
    Int8,
    Int16,
    Int32,
    Int64,

    // Floating point types.
    Float32,
    Float64,

    // Boolean type.
    Bool,

    // String type.
    String,

    // Array type.
    Array,

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

    // Type type.
    Type,
}

// type aliases
impl Types {
    pub const BYTE: Types = Types::Uint8;
    pub const RUNE: Types = Types::Int32;
    pub const UINT: Types = Types::Uint64;
    pub const FLOAT: Types = Types::Float64;
}

/// Value represents any value in the Speak programming language.
/// Each value corresponds to some primitive or object value created
/// during the execution of a Speak program.
#[derive(Debug, Clone)]
pub enum Value {
    /// EmptyValue is the value of the empty identifier.
    /// it is globally unique and matches everything in equality.
    EmptyValue,

    /// StringValue represents all characters and strings in Speak.
    StringValue(Vec<u8>),
}

impl Value {
    // value_type returns the type of the value.
    fn value_type(&self) -> Types {
        match self {
            Value::EmptyValue => Types::Empty,
            Value::StringValue(_) => Types::String,
        }
    }

    /// string returns the string representation of the value.
    fn string(&self) -> String {
        match self {
            Value::EmptyValue => String::from_utf8(vec![]).unwrap(),
            Value::StringValue(_) => "_".to_string(), // TODO
        }
    }

    /// Equals reports whether the given value is deep-equal to the
    /// receiving value. It does not compare references.
    fn equals(&self, value: Value) -> bool {
        match self {
            Value::EmptyValue => true,
            Value::StringValue(str_value) => {
                // TODO
                if Types::String == value.value_type() {
                    return "_".to_string() == value.string();
                }
                false
            }
        }
    }
}

pub struct Engine {}

/// ValueTable is used anytime a map of names/labels to Speak Values is needed,
/// and is notably used to represent stack frames/heaps and CompositeValue dictionaries.
type ValueTable = HashMap<String, Value>;

/// StackFrame represents the heap of variables local to a particular function call frame,
/// and recursively references other parent StackFrames internally.
#[derive(Debug, Clone)]
pub struct StackFrame {
    // The parent StackFrame, if any.
    parent: Option<Box<StackFrame>>,
    // The variables local to this StackFrame.
    value_table: ValueTable,
}

impl StackFrame {
    /// Get a value from the stack frame chain. TODO: perf. improve
    fn get(&self, name: String) -> (Option<Value>, bool) {
        let mut frame = self.clone();
        loop {
            match frame.value_table.get(&name) {
                Some(val) => return (Some(val.clone()), true),
                None => match self.parent.clone() {
                    Some(addr) => frame = *addr,
                    None => return (None, false),
                },
            }
        }
    }

    /// Set a value to the most recent call stack frame.
    fn set(&mut self, name: String, val: Value) {
        self.value_table.insert(name, val);
    }

    /// Up updates a value in the stack frame chain. TODO: perf. improve
    fn up(&mut self, name: String, val: Value) {
        let mut frame = self.clone();
        loop {
            match frame.value_table.insert(name.clone(), val.clone()) {
                Some(_) => {}
                None => match self.parent.clone() {
                    Some(addr) => frame = *addr,
                    None => log_err(
                        &ErrorReason::Assert,
                        &format!(
                            "StackFrame.Up expected to find variable '{name}' in frame but did not"
                        ),
                    ),
                },
            }
        }
    }

    fn string(&self) -> String {
        let mut entries = Vec::new();
        for (k, v) in self.value_table.clone() {
            let mut vStr = v.string();
            if vStr.len() > MAX_PRINT_LEN {
                vStr = format!("{}...", &vStr[..MAX_PRINT_LEN])
            }
            entries.push(format!("{k} -> {vStr}"))
        }

        format!(
            "{{\n\t{}\n}} -prnt-> {:?}",
            entries.join("\n\t"),
            self.parent
        )
    }
}

/// Context represents a single, isolated execution context with its global heap,
/// imports, call stack, and cwd (working directory).
pub struct Context {
    /// cwd is an always-absolute path to current working dir (of module system)
    cwd: String,
    /// The currently executing file's path, if any
    file: String,
    engine: Option<Engine>,
    /// Frame represents the Context's global heap
    frame: Option<Box<StackFrame>>,
}