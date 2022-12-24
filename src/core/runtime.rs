use super::{
    error::{Err, ErrorReason},
    eval::value::Value,
    lexer::{tokenize, Tok},
    log::{log_debug, log_err},
    parser::{parse, Node},
};
use core::fmt;
use std::{collections::HashMap, env, fs, io::BufReader, sync::mpsc::channel};

pub const MAX_PRINT_LEN: usize = 120;

/// ValueTable is used anytime a map of names/labels to Speak Values is needed,
/// and is notably used to represent stack frames/heaps and CompositeValue dictionaries.
#[derive(Debug, Clone)]
pub struct VTable(pub HashMap<String, Value>);

impl VTable {
    fn get(&self, name: &str) -> Option<&Value> {
        self.0.get(name)
    }

    fn set(&mut self, key: String, value: Value) {
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
    pub fn get(&self, name: &str) -> Option<&Value> {
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
    pub fn set(&mut self, name: String, val: Value) {
        if let StackFrame::Frame { item, next: _ } = self {
            item.set(name, val)
        }
    }

    /// Updates a value in the stack frame chain.
    fn up(&mut self, name: String, val: Value) {
        let mut frame = self;
        while let StackFrame::Frame { item, next } = frame {
            match item.get(&name) {
                Some(_) => {
                    item.0.insert(name, val);
                    return;
                }
                None => {
                    frame = next;
                }
            }
        }

        log_err(
            &ErrorReason::Assert,
            &format!(
                "StackFrame.up expected to find variable '{}' in frame but did not",
                name
            ),
        );
    }

    /// dumps the stack frame chain to return out.
    pub fn string(&self) -> Option<String> {
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

    /// Takes a channel of Nodes to evaluate, and executes the Speak programs defined
    /// in the syntax tree. Returning the last value of the last expression in the AST,
    /// or an error to stderr if there was a runtime error.
    pub fn eval(&mut self, nodes: Vec<Node>, dump_frame: bool) -> Result<Value, Err> {
        let len = nodes.len();
        let mut last_val = Value::Empty;

        // load runtime
        load_builtins(self);

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
    pub fn exec(&mut self, input: BufReader<&[u8]>) -> Result<Value, Err> {
        let (tx, rx) = channel::<Tok>();

        let mut buf = input;
        tokenize(&mut buf, &tx, self.fatal_err, self.debug_lex)?;

        let (nodes_chan, nodes_rx) = channel::<Node>();

        parse(rx, nodes_chan, self.fatal_err, self.debug_parse);

        self.eval(nodes_rx.iter().collect::<Vec<Node>>(), self.debug_dump)
    }

    /// Allows to Exec() a program file in a given context.
    pub fn exec_path(&mut self, path: String) -> Result<Value, Err> {
        match fs::read(path) {
            Ok(data) => self.exec(BufReader::new(&data[..])),
            Err(err) => Err(Err {
                message: format!("Speak encountered a system error: {}", err),
                reason: ErrorReason::System,
            }),
        }
    }
}

/// Native function are convenience functions that come with the interpreter; an example is the
/// `println` function
#[derive(Clone)]
pub struct NativeFunction<F: Fn(&mut StackFrame, &[Value]) -> Result<Value, Err>>(
    pub String,
    pub F,
);
pub type NativeFn = NativeFunction<fn(&mut StackFrame, &[Value]) -> Result<Value, Err>>;

impl fmt::Debug for NativeFn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "NativeFunction {{ name: {} }}", self.0)
    }
}

/// This loads up the built-in functions which come with the interpreter.
pub fn load_builtins(ctx: &mut Context) {
    if let StackFrame::Frame { item, next: _ } = &mut ctx.frame {
        item.set(
            "println".to_string(),
            Value::NativeFunction(NativeFunction("println".to_string(), |_, inputs| {
                println!(
                    "{}",
                    inputs
                        .iter()
                        .fold(String::new(), |acc, x| acc + &x.string())
                );

                Ok(Value::Empty)
            })),
        );

        item.set(
            "sprint".to_string(),
            Value::NativeFunction(NativeFunction("sprint".to_string(), |_, inputs| {
                Ok(Value::String(inputs[0].string()))
            })),
        );

        item.set(
            "sprintf".to_string(),
            Value::NativeFunction(NativeFunction("sprintf".to_string(), |_, inputs| {
                if inputs.len() <= 1 {
                    return Err(Err {
                        reason: ErrorReason::Runtime,
                        message: "sprintf takes at least two arguments".to_string(),
                    });
                }

                Ok(Value::String(
                    inputs[0].string().split("{}").enumerate().fold(
                        String::new(),
                        |acc, (i, x)| {
                            if i == inputs.len() - 1 {
                                acc + x
                            } else {
                                acc + x + &inputs[i + 1].string()
                            }
                        },
                    ),
                ))
            })),
        );

        item.set(
            "len".to_string(),
            Value::NativeFunction(NativeFunction("len".to_string(), |_, inputs| {
                if inputs.len() != 1 {
                    return Err(Err {
                        reason: super::error::ErrorReason::Runtime,
                        message: "len() takes exactly one argument".to_string(),
                    });
                }

                // todo: check if input is a string or list, fail for number
                Ok(Value::Number(inputs.len() as f64))
            })),
        );

        return item.set(
            "mod".to_string(),
            Value::NativeFunction(NativeFunction(
                "mod".to_string(),
                |_stack: &mut StackFrame, inputs: &[Value]| -> Result<Value, Err> {
                    for i in inputs {
                        match i {
                            Value::String(_path) => {
                                // TODO: load data to stack
                                unimplemented!()
                            }
                            _ => {
                                return Err(Err {
                                    message: "mod arguements must be string literals".to_string(),
                                    reason: ErrorReason::Runtime,
                                });
                            }
                        }
                    }

                    Ok(Value::Empty)
                },
            )),
        );
    }

    log_err(&ErrorReason::Assert, "Stackframe provided is Nil")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stack_frame() {
        let mut frame = StackFrame::new(VTable(HashMap::new()), StackFrame::Nil);

        // test stackframe.set(), stackframe.get()
        frame.set("a".to_string(), Value::String("hello".to_string()));
        assert!(frame
            .get("a")
            .expect("key must be present")
            .equals(Value::String("hello".to_string())));

        // test stackframe.string()
        assert_eq!(
            frame.string().expect("frame must be present"),
            "{\n\ta -> hello\n} -parent-> Nil".to_string()
        );

        // test stackframe.up(), stackframe.get()
        frame.up("a".to_string(), Value::String("mutated value".to_string()));
        assert!(frame
            .get("a")
            .expect("key must be present")
            .equals(Value::String("mutated value".to_string())));

        // test stackframe.get, in parent frame
        let frame = StackFrame::Frame {
            item: VTable(HashMap::new()),
            next: Box::new(frame),
        };
        assert!(frame.get("a").is_some());
        assert!(frame.get("b").is_none());
    }
}
