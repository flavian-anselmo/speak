use super::{
    error::Err,
    eval::{value::_Value, Context},
};

pub fn speak_println(ctx: &Context, input: &[_Value]) -> Result<_Value, Err> {
    println!(
        "{}",
        input.iter().fold(String::new(), |acc, x| acc + &x.string())
    );

    Ok(_Value::Empty)
}

pub fn speak_len(ctx: &Context, input: &[_Value]) -> Result<_Value, Err> {
    if input.len() != 1 {
        return Err(Err {
            reason: super::error::ErrorReason::Runtime,
            message: "len() takes exactly one argument".to_string(),
        });
    }

    // todo: check if input is a string or list, fail for number
    Ok(_Value::Number(input.len() as f64))
}
