use super::{
    error::{Err, ErrorReason},
    eval::{value::_Value, StackFrame},
};

pub fn speak_mod(/*TODO: ctx: &mut Context*/
) -> fn(&mut StackFrame, &[_Value]) -> Result<_Value, Err> {
    |_stack: &mut StackFrame, inputs: &[_Value]| -> Result<_Value, Err> {
        for i in inputs {
            match i {
                _Value::String(_path) => {
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

        Ok(_Value::Empty)
    }
}

// pub fn speak_println(ctx: &mut Context) -> Box<dyn Fn(&[_Value]) -> Result<_Value, Err>>
pub fn speak_println(_: &mut StackFrame, input: &[_Value]) -> Result<_Value, Err> {
    println!(
        "{}",
        input.iter().fold(String::new(), |acc, x| acc + &x.string())
    );

    Ok(_Value::Empty)
}

pub fn speak_sprint(_: &mut StackFrame, input: &[_Value]) -> Result<_Value, Err> {
    Ok(_Value::String(input[0].string()))
}

pub fn speak_sprintf(_: &mut StackFrame, input: &[_Value]) -> Result<_Value, Err> {
    if input.len() <= 1 {
        return Err(Err {
            reason: ErrorReason::Runtime,
            message: "sprintf takes at least two arguments".to_string(),
        });
    }

    Ok(_Value::String(
        input[0]
            .string()
            .split("{}")
            .enumerate()
            .fold(String::new(), |acc, (i, x)| {
                if i == input.len() - 1 {
                    acc + x
                } else {
                    acc + x + &input[i + 1].string()
                }
            }),
    ))
}

pub fn speak_len(_: &mut StackFrame, input: &[_Value]) -> Result<_Value, Err> {
    if input.len() != 1 {
        return Err(Err {
            reason: super::error::ErrorReason::Runtime,
            message: "len() takes exactly one argument".to_string(),
        });
    }

    // todo: check if input is a string or list, fail for number
    Ok(_Value::Number(input.len() as f64))
}
