use self::value::_Value;
use super::{
    error::{Err, ErrorReason},
    lexer::{tokenize, Tok},
    log::{log_debug, log_err},
    parser::{_Node, parse},
    runtime,
};
use std::{collections::HashMap, env, fmt, fs, io::BufReader, sync::mpsc::channel};

const MAX_PRINT_LEN: usize = 120;

pub mod r#type {
    #[derive(Debug, PartialEq, Eq, Clone)]
    pub enum Type {
        /// Floating point number: f64
        Number,

        /// Boolean type.
        Bool,

        /// String type.
        String,

        // Array type.
        // Array {
        //     r#type: Box<Type>,
        // },

        // Map type.
        //Map,

        // Function type.
        Function,

        // // Interface type.
        // Interface,

        // // Struct type.
        // Struct,

        // // Enum type.
        // Enum,

        // Empty type.
        Empty,
    }

    // type aliases
    impl Type {
        pub fn string(&self) -> String {
            match self {
                Type::Number => "number".to_string(),
                Type::Bool => "bool".to_string(),
                Type::String => "string".to_string(),
                // Type::Array { r#type } => format!("[]{}", r#type.string()),
                // Type::Map => "map".to_string(),
                Type::Function => "function".to_string(),
                // Type::Interface => "interface".to_string(),
                // Type::Struct => "struct".to_string(),
                // Type::Enum => "enum".to_string(),
                Type::Empty => "empty".to_string(),
            }
        }
    }
}

pub mod value {
    use crate::core::parser::_Node;
    use std::fmt::Debug;

    use super::{r#type::Type, NativeFn, VTable, MAX_PRINT_LEN};

    /// Value represents any value in the Speak programming language.
    /// Each value corresponds to some primitive or object value created
    /// during the execution of a Speak program.
    #[derive(Debug, Clone)]
    pub enum _Value {
        Number(f64),
        Bool(bool),
        String(String),

        /// This is the value of any variables referencing functions
        /// defined in a Speak program.
        Function(Function),

        /// This is a function whose implementation is written in rust and
        /// is part of the interpreter.
        NativeFunction(NativeFn),

        /// This is an internal representation of a lazy
        /// function evaluation used to implement tail call optimization.
        FunctionCallThunk {
            vt: VTable,
            func: Function,
        },

        Empty,
    }

    #[derive(Debug, Clone)]
    pub struct Function {
        // defn must be of variant `FunctionLiteral`.
        pub defn: Box<_Node>,
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
                _Value::Number(_) => Type::Number,
                _Value::Bool(_) => Type::Bool,
                _Value::String(_) => Type::String,
                _Value::Function { .. }
                | _Value::FunctionCallThunk { .. }
                | _Value::NativeFunction(..) => Type::Function,
                _Value::Empty => Type::Empty,
            }
        }

        pub fn equals(&self, value: _Value) -> bool {
            match (self, value) {
                (_Value::Number(a), _Value::Number(b)) => a == &b,
                (_Value::Bool(a), _Value::Bool(b)) => a == &b,
                (_Value::String(a), _Value::String(b)) => a == &b,
                (_Value::Empty, _) | (_, _Value::Empty) => true,
                _ => false, // types here are incomparable
            }
        }

        pub fn string(&self) -> String {
            match self {
                _Value::Number(value) => value.to_string(),
                _Value::Bool(value) => value.to_string(),
                _Value::String(value) => value.to_string(),
                _Value::Function(func) => func.string(),
                _Value::NativeFunction(func) => format!("Native Function ({})", func.0),
                _Value::FunctionCallThunk { func, .. } => {
                    format!("Thunk of ({})", func.string())
                }
                _Value::Empty => "()".to_string(),
            }
        }
    }
}

#[derive(Clone)]
pub struct NativeFunction<F: Fn(&mut StackFrame, &[_Value]) -> Result<_Value, Err>>(String, pub F);
type NativeFn = NativeFunction<fn(&mut StackFrame, &[_Value]) -> Result<_Value, Err>>;

impl fmt::Debug for NativeFn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "NativeFunction {{ name: {} }}", self.0)
    }
}

/// This loads up the built-in functions which come with the interpreter.
pub fn load_runtime(ctx: &mut Context) {
    if let StackFrame::Frame { item, next: _ } = &mut ctx.frame {
        item.set(
            "println".to_string(),
            _Value::NativeFunction(NativeFunction(
                "println".to_string(),
                runtime::speak_println,
            )),
        );
        item.set(
            "sprint".to_string(),
            _Value::NativeFunction(NativeFunction("sprint".to_string(), runtime::speak_sprint)),
        );
        item.set(
            "sprintf".to_string(),
            _Value::NativeFunction(NativeFunction(
                "println".to_string(),
                runtime::speak_sprintf,
            )),
        );
        item.set(
            "len".to_string(),
            _Value::NativeFunction(NativeFunction("len".to_string(), runtime::speak_len)),
        );

        item.set(
            "mod".to_string(),
            _Value::NativeFunction(NativeFunction("mod".to_string(), runtime::speak_mod())),
        );

        return;
    }

    log_err(&ErrorReason::Assert, "Stackframe provided is Nil")
}

/// This is a global execution context for the lifetime of the Speak program.
#[derive(Debug)]
pub struct Engine {
    pub fatal_error: bool,
    pub debug_lex: bool,
    pub debug_parse: bool,
    pub debug_dump: bool,
}

impl Default for Engine {
    fn default() -> Self {
        Self {
            fatal_error: true,
            debug_lex: false,
            debug_parse: true,
            debug_dump: false,
        }
    }
}

/// ValueTable is used anytime a map of names/labels to Speak Values is needed,
/// and is notably used to represent stack frames/heaps and CompositeValue dictionaries.
#[derive(Debug, Clone)]
pub struct VTable(pub HashMap<String, _Value>);

impl VTable {
    fn get(&self, name: &str) -> Option<&_Value> {
        self.0.get(name)
    }

    fn set(&mut self, key: String, value: _Value) {
        self.0.insert(key, value);
    }
}

/// StackFrame represents the heap of variables local to a particular function call frame,
/// and recursively references other parent StackFrames internally.
#[derive(Debug)]
pub enum StackFrame {
    Frame { item: VTable, next: Box<StackFrame> },
    Nil,
}

impl StackFrame {
    /// Creates a new stack frame with the provided value table and parent stack frame.
    pub fn new(value_table: VTable, parent: StackFrame) -> Self {
        Self::Frame {
            item: value_table,
            next: Box::new(parent),
        }
    }

    /// Get a value from the current stack frame chain.
    pub fn get(&self, name: &str) -> Option<&_Value> {
        let mut frame = self;
        while let StackFrame::Frame { item, next } = frame {
            match item.get(name) {
                Some(val) => return Some(val),
                None => {
                    frame = next;
                }
            }
        }

        return None;
    }

    /// Sets a value to the provided stack frame.
    pub fn set(&mut self, name: String, val: _Value) {
        if let StackFrame::Frame { item, next: _ } = self {
            item.set(name, val)
        }
    }

    /// Updates a value in the stack frame chain.
    // fn up(&mut self, name: String, val: _Value) {
    //     let mut frame = self;
    //     while let StackFrame::Frame { item, next } = frame {
    //         match item.get(&name) {
    //             Some(_) => {
    //                 item.0.insert(name, val);
    //                 return;
    //             }
    //             None => {
    //                 frame = next;
    //             }
    //         }
    //     }

    //     log_err(
    //         &ErrorReason::Assert,
    //         &format!(
    //             "StackFrame.up expected to find variable '{}' in frame but did not",
    //             name
    //         ),
    //     );
    // }

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
#[derive(Debug)]
pub struct Context {
    /// cwd is an always-absolute path to current working dir (of module system)
    _cwd: Option<String>,
    /// The currently executing file's path, if any
    _file: Option<String>,
    /// Frame represents the Context's global heap
    frame: StackFrame,

    fatal_err: bool,
    debug_lex: bool,
    debug_parse: bool,
    debug_dump: bool,
}

impl Context {
    pub fn new(verbose: &bool) -> Self {
        Context {
            _cwd: Some(env::current_dir().unwrap().to_str().unwrap().to_string()),
            _file: None,
            frame: StackFrame::new(VTable(HashMap::new()), StackFrame::Nil),
            fatal_err: true,
            debug_lex: *verbose,
            debug_parse: *verbose,
            debug_dump: *verbose,
        }
    }

    // fn reset_wd(&mut self) {
    //     self._cwd = Some(env::current_dir().unwrap().to_str().unwrap().to_string());
    // }

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

        // load runtime
        load_runtime(self);

        let mut iter = nodes.into_iter().enumerate();
        while let Some((i, node)) = iter.next() {
            let mut node = node;
            //let frame = &mut self.frame;
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

    /// Runs a Speak program defined by the buffer. This is the main way to invoke Speak programs
    /// from Rust.
    pub fn exec(&mut self, input: BufReader<&[u8]>) -> Result<_Value, Err> {
        let (tx, rx) = channel::<Tok>();

        let mut buf = input;
        tokenize(&mut buf, &tx, self.fatal_err, self.debug_lex)?;

        let (nodes_chan, nodes_rx) = channel::<_Node>();

        parse(rx, nodes_chan, self.fatal_err, self.debug_parse);

        self.eval(nodes_rx.iter().collect::<Vec<_Node>>(), self.debug_dump)
    }

    /// Allows to Exec() a program file in a given context.
    pub fn exec_path(&mut self, path: String) -> Result<_Value, Err> {
        match fs::read(path) {
            Ok(data) => self.exec(BufReader::new(&data[..])),
            Err(err) => Err(Err {
                message: format!("Speak encountered a system error: {}", err),
                reason: ErrorReason::System,
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stack_frame() {
        let mut frame = StackFrame::new(VTable(HashMap::new()), StackFrame::Nil);

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
        // frame.up("a".to_string(), _Value::String("mutated value".to_string()));
        // assert!(frame
        //     .get("a")
        //     .expect("key must be present")
        //     .equals(_Value::String("mutated value".to_string())));

        // test stackframe.get, in parent frame
        let frame = StackFrame::Frame {
            item: VTable(HashMap::new()),
            next: Box::new(frame),
        };
        assert!(frame.get("a").is_some());
        assert!(frame.get("b").is_none());
    }
}
