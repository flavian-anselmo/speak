#[macro_use]
extern crate lazy_static;
mod core;
use clap::{Parser, Subcommand};
use std::io::{self, BufReader, Write};

use crate::core::runtime::Context;

/// The `Speak` CLI Compiler
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct SpeakCLI {
    // CLI ARGUEMENTS
    #[clap(subcommand)]
    command: Commands,

    /// Allows the compiler to take a `Speak` identifier config file.
    #[clap(short, require_equals(true))]
    iconfig: Option<String>,

    /// Log all interpreter debug information.
    #[clap(short, long)]
    verbose: bool,
}

#[derive(Subcommand, Debug)]
enum Commands {
    /// runs `Speak` file provided
    Run {
        file_path: String,
    },
    Repl,
    /// Generates the `Speak` identifier config file.
    Geniconf,
}

fn main() {
    let speak_cli = SpeakCLI::parse();
    let mut ctx = Context::new(&speak_cli.verbose);
    match speak_cli.command {
        Commands::Run { file_path } => match ctx.exec_path(file_path) {
            Ok(val) => core::log::log_interactive(&val.string()),
            Err(err) => core::log::log_err(&err.reason, &err.message),
        },
        Commands::Repl => {
            let mut input = String::new();
            core::log::log_interactive("> ");
            io::stdout().flush().unwrap();

            match io::stdin().read_line(&mut input) {
                Ok(_) => match ctx.exec(BufReader::new(input.as_bytes())) {
                    Ok(val) => {
                        core::log::log_interactive(&val.string());
                        io::stdout().flush().unwrap();
                    }
                    Err(err) => {
                        core::log::log_err(&err.reason, &err.message);
                        io::stdout().flush().unwrap();
                    }
                },
                Err(err) => {
                    core::log::log_err(&core::error::ErrorReason::System, &err.to_string());
                    io::stdout().flush().unwrap();
                }
            }
        }
        Commands::Geniconf => {
            println!("HERE 2");
        }
    }
    println!("HERE 3");
}
