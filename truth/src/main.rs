use serde_json::{Value, json};
use std::{collections::BTreeMap, env, path::PathBuf, process::ExitCode};
use truth::Corpus;

const HELP: &str =
    "Usage: truth [--root PATH] [--json] status\n       truth [--root PATH] [--json] inspect ID";

fn run(args: &[String]) -> Result<Value, (u8, Value)> {
    let mut root = PathBuf::from(".");
    let mut positional = Vec::new();
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--json" => {}
            "--root" => {
                root = args.next().map(PathBuf::from).ok_or_else(|| {
                    (
                        2,
                        json!({"code":"usage", "message": "--root requires a path"}),
                    )
                })?;
            }
            value if value.starts_with('-') => {
                return Err((
                    2,
                    json!({"code":"usage", "message":format!("unknown option {value}")}),
                ));
            }
            value => positional.push(value),
        }
    }
    let id = match positional.as_slice() {
        ["status"] => None,
        ["inspect", id] if !id.is_empty() => Some(*id),
        _ => return Err((2, json!({"code":"usage", "message":HELP}))),
    };
    let corpus = Corpus::load(&root).map_err(|error| {
        (
            1,
            json!({"code":error.code, "path":error.path, "message":error.message}),
        )
    })?;
    let mut output = json!({
        "schema_version": 1,
        "validation": "structural",
        "input_identity": corpus.input_identity(),
    });
    if let Some(id) = id {
        let matches: Vec<_> = corpus
            .inspect(id)
            .map(|(kind, record)| json!({"kind":kind, "path":record.path, "record":record.fields}))
            .collect();
        if matches.is_empty() {
            return Err((
                3,
                json!({"code":"unknown_id", "message":format!("unknown ID {id}"),
                "id":id, "input_identity":corpus.input_identity()}),
            ));
        }
        output["id"] = json!(id);
        output["matches"] = json!(matches);
    } else {
        output["counts"] = json!(corpus.counts().collect::<BTreeMap<_, _>>());
    }
    Ok(output)
}

fn main() -> ExitCode {
    let args: Vec<_> = env::args().skip(1).collect();
    if matches!(args.as_slice(), [arg] if arg == "--help" || arg == "-h") {
        println!("{HELP}");
        return ExitCode::SUCCESS;
    }
    let machine = args.iter().any(|arg| arg == "--json");
    match run(&args) {
        Ok(output) => {
            if machine {
                println!("{output}");
            } else if let Some(counts) = output["counts"].as_object() {
                println!("Corpus structure ({})", output["input_identity"]);
                for (kind, count) in counts {
                    println!("{kind:16} {count}");
                }
            } else if let Some(matches) = output["matches"].as_array() {
                println!("{} ({})", output["id"], output["input_identity"]);
                for record in matches {
                    println!(
                        "{} · {}\n{:#}",
                        record["kind"], record["path"], record["record"]
                    );
                }
            }
            ExitCode::SUCCESS
        }
        Err((code, error)) => {
            if machine {
                eprintln!("{}", json!({"schema_version":1,"error":error}));
            } else if let Some(path) = error["path"].as_str() {
                eprintln!(
                    "truth: {path}: {}",
                    error["message"].as_str().unwrap_or_default()
                );
            } else {
                eprintln!("truth: {}", error["message"].as_str().unwrap_or_default());
            }
            ExitCode::from(code)
        }
    }
}
