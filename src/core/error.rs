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

impl ErrorReason {
    pub fn value(&self) -> u8 {
        match self {
            //  ErrorReason::Unknown => 0,
            ErrorReason::Syntax => 1,
            ErrorReason::Runtime => 2,
            ErrorReason::System => 40,
            ErrorReason::Assert => 100,
        }
    }
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
