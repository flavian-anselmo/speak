mod core;
use clap::{Parser, Subcommand};

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
    /// runs `Speak` files provided
    Run {
        files: Vec<String>,
    },
    Repl,
    /// Generates the `Speak` identifier config file.
    Geniconf,
}

fn main() {
    let speak_cli = SpeakCLI::parse();

    match speak_cli.command {
        Commands::Run { files: _ } => {}
        Commands::Repl => {}
        Commands::Geniconf => {}
    }
}
