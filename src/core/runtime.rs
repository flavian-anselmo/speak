use super::{
    error::{Err, ErrorReason},
    eval::{value::_Value, Context},
};

pub fn speak_println(_: &Context, input: &[_Value]) -> Result<_Value, Err> {
    println!(
        "{}",
        input.iter().fold(String::new(), |acc, x| acc + &x.string())
    );

    Ok(_Value::Empty)
}

pub fn speak_sprint(_: &Context, input: &[_Value]) -> Result<_Value, Err> {
    Ok(_Value::String(input[0].string()))
}

pub fn speak_sprintf(_: &Context, input: &[_Value]) -> Result<_Value, Err> {
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

pub fn speak_len(_: &Context, input: &[_Value]) -> Result<_Value, Err> {
    if input.len() != 1 {
        return Err(Err {
            reason: super::error::ErrorReason::Runtime,
            message: "len() takes exactly one argument".to_string(),
        });
    }

    // todo: check if input is a string or list, fail for number
    Ok(_Value::Number(input.len() as f64))
}
