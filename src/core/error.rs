use std::sync::mpsc::SendError;

// ErrorReason enums represent possible errors that the Speak interpreter
// binding functions may return.
#[derive(Debug, PartialEq, Clone)]
pub enum ErrorReason {
    // Unknown,
    Syntax,
    Runtime,
    System,
    Assert,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Err {
    pub reason: ErrorReason,
    pub message: String,
}

impl From<std::io::Error> for Err {
    fn from(err: std::io::Error) -> Self {
        Err {
            reason: ErrorReason::System,
            message: format!("System error: {}", err),
        }
    }
}

impl<T> From<SendError<T>> for Err {
    fn from(err: SendError<T>) -> Self {
        Err {
            reason: ErrorReason::System,
            message: format!("System error: {}", err),
        }
    }
}
