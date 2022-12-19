use std::task::Context;

use super::{error::Err, eval::value::_Value};

pub fn speak_println(ctx: &Context, input: &_Value) -> Result<(), Err> {
    println!("{}", input.string());
    Ok(())
}
