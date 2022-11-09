// ErrorReason enums represent possible errors that the Speak interpreter
// binding functions may return.
pub enum ErrorReason {
    Unknown,
    Syntax,
    Runtime,
    System,
    Assert,
}

impl ErrorReason {
    pub fn value(&self) -> u8 {
        match self {
            ErrorReason::Unknown => 0,
            ErrorReason::Syntax => 1,
            ErrorReason::Runtime => 2,
            ErrorReason::System => 40,
            ErrorReason::Assert => 100,
        }
    }
}

pub struct Err {
    reason: ErrorReason,
    message: String,
}

impl Err {
    pub fn error(&self) -> String {
        self.message.clone()
    }
}
