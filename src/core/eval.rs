use self::value::_Value;

use super::{
    error::{Err, ErrorReason},
    log::{log_debug, log_err},
    parser::_Node,
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
        parser::_Node,
    };
    use std::any::Any;
    use std::fmt::{Debug, Display};

    use super::{r#type::Type, StackFrame, VTable, MAX_PRINT_LEN};
    use num_traits::{cast, FromPrimitive, Num, NumCast, Signed, ToPrimitive};

    /// Value represents any value in the Speak programming language.
    /// Each value corresponds to some primitive or object value created
    /// during the execution of a Speak program.
    #[derive(Debug, PartialEq, Clone)]
    pub enum _Value {
        Numeric(_Numeric),
        Bool(bool),
        String(String),

        // Function is the value of any variables referencing functions
        // defined in a Speak program.
        Function(Function),

        // FunctionCallThunk is an internal representation of a lazy
        // function evaluation used to implement tail call optimization.
        FunctionCallThunk { vt: VTable, func: Function },

        Empty,
    }

    #[derive(Debug, PartialEq, Clone)]
    pub enum _Numeric {
        Uint8(u8),
        Uint16(u16),
        Uint32(u32),
        Uint64(u64),
        Int8(i8),
        Int16(i16),
        Int32(i32),
        Int64(i64),
        Float32(f32),
        Float64(f64),
    }

    #[derive(Debug, PartialEq, Clone)]
    pub struct Function {
        // It's defn must be of variant `FunctionLiteral`.
        pub defn: Box<_Node>,
        pub parent_frame: StackFrame,
    }

    impl Function {
        fn string(&self) -> String {
            let func_str = self.defn.string();
            if func_str.len() > MAX_PRINT_LEN {
                return format!("{}..", &func_str[..MAX_PRINT_LEN]);
            }

            return func_str;
        }
    }

    impl _Value {
        pub fn value_type(&self) -> Type {
            match self {
                _Value::Numeric(n) => match n {
                    _Numeric::Uint8(_) => Type::Uint8,
                    _Numeric::Uint16(_) => Type::Uint16,
                    _Numeric::Uint32(_) => Type::Uint32,
                    _Numeric::Uint64(_) => Type::Uint64,
                    _Numeric::Int8(_) => Type::Int8,
                    _Numeric::Int16(_) => Type::Int16,
                    _Numeric::Int32(_) => Type::Int32,
                    _Numeric::Int64(_) => Type::Int64,
                    _Numeric::Float32(_) => Type::Float32,
                    _Numeric::Float64(_) => Type::Float64,
                },
                _Value::Bool(_) => Type::Bool,
                _Value::String(_) => Type::String,
                _Value::Function { .. } => Type::Function,
                _Value::FunctionCallThunk { .. } => Type::Function,
                _Value::Empty => Type::Empty,
            }
        }

        pub fn equals(&self, value: Self) -> bool {
            *self == value
        }

        pub fn string(&self) -> String {
            match self {
                _Value::Numeric(n) => match n {
                    _Numeric::Uint8(value) => value.to_string(),
                    _Numeric::Uint16(value) => value.to_string(),
                    _Numeric::Uint32(value) => value.to_string(),
                    _Numeric::Uint64(value) => value.to_string(),
                    _Numeric::Int8(value) => value.to_string(),
                    _Numeric::Int16(value) => value.to_string(),
                    _Numeric::Int32(value) => value.to_string(),
                    _Numeric::Int64(value) => value.to_string(),
                    _Numeric::Float32(value) => value.to_string(),
                    _Numeric::Float64(value) => value.to_string(),
                },
                _Value::Bool(value) => value.to_string(),
                _Value::String(value) => value.to_string(),
                _Value::Function(func) => func.string(),
                _Value::FunctionCallThunk { func, vt: _ } => {
                    format!("Thubk of ({})", func.string())
                }
                _Value::Empty => "()".to_string(),
            }
        }
    }
}

pub struct Engine {}

/// ValueTable is used anytime a map of names/labels to Speak Values is needed,
/// and is notably used to represent stack frames/heaps and CompositeValue dictionaries.
#[derive(Debug, Clone, PartialEq)]
pub struct VTable(HashMap<String, _Value>);

impl VTable {
    fn new(map: HashMap<String, _Value>) -> Self {
        Self(map)
    }

    fn get(&self, name: &str) -> Option<&_Value> {
        self.0.get(name)
    }

    fn set(&mut self, key: String, value: _Value) {
        self.0.insert(key, value);
    }
}

/// StackFrame represents the heap of variables local to a particular function call frame,
/// and recursively references other parent StackFrames internally.
#[derive(Debug, Clone, PartialEq)]
pub enum StackFrame {
    Frame { item: VTable, next: Box<StackFrame> },
    Nil,
}

impl StackFrame {
    /// Creates a new stack frame with the provided value table and parent stack frame.
    fn new(value_table: VTable, parent: StackFrame) -> Self {
        Self::Frame {
            item: value_table,
            next: Box::new(parent),
        }
    }

    /// Get a value from the current stack frame chain.
    pub fn get(&self, name: &str) -> Option<&_Value> {
        if let StackFrame::Frame { item, next: _ } = self {
            return item.get(name);
        }

        return None;
    }

    /// Sets a value to the provided stack frame.
    fn set(&mut self, name: String, val: _Value) {
        if let StackFrame::Frame { item, next: _ } = self {
            item.set(name, val)
        }
    }

    /// Updates a value in the stack frame chain.
    fn up(&mut self, name: String, val: _Value) {
        if let StackFrame::Frame { item, next: _ } = self {
            let l = &mut item.0;
            l.insert(name, val);
        }
    }

    /// Provides the vtable to the function provided for mutation.
    fn mutate<F: FnMut(&mut VTable) -> Result<(), Err>>(&mut self, mut f: F) -> Result<(), Err> {
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
    pub fn eval(&mut self, nodes: Vec<_Node>, dump_frame: bool) -> Result<_Value, Err> {
        let len = nodes.len();
        let mut last_val = _Value::Empty;

        let mut iter = nodes.into_iter().enumerate();
        while let Some((i, node)) = iter.next() {
            let mut node = node;
            match node.eval(&mut self.frame, false) {
                Ok(val) => {
                    if i == len - 1 {
                        if dump_frame {
                            self.dump();
                        }
                        last_val = val;
                    }
                }
                Err(err) => {
                    log_err(&ErrorReason::Assert, &format!("eval error: {:?}", err));
                    if dump_frame {
                        self.dump();
                    }

                    return Err(err);
                }
            }
        }

        Ok(last_val)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stack_frame() {
        let mut frame = StackFrame::new(VTable::new(HashMap::new()), StackFrame::Nil);

        // test stackframe.set(), stackframe.get()
        frame.set("a".to_string(), _Value::String("hello".to_string()));
        assert!(frame
            .get("a")
            .expect("key must be present")
            .equals(_Value::String("hello".to_string())));

        // test stackframe.string()
        assert_eq!(
            frame.string().expect("frame must be present"),
            "{\n\ta -> hello\n} -parent-> Nil".to_string()
        );

        // test stackframe.up(), stackframe.get()
        frame.up("a".to_string(), _Value::String("mutated value".to_string()));
        assert!(frame
            .get("a")
            .expect("key must be present")
            .equals(_Value::String("mutated value".to_string())));

        //test stackframe.get, in parent frame
        let frame = StackFrame::Frame {
            item: VTable::new(HashMap::new()),
            next: Box::new(frame),
        };
        assert!(frame.get("a").is_none())
    }
}
