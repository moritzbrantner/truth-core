use serde_json::{Value, json};
use std::{collections::BTreeMap, env, ffi::OsString, path::PathBuf, process::ExitCode};
use truth::{Corpus, bridges};

const HELP: &str = "Usage: truth [--root PATH] [--json] status
       truth [--root PATH] [--json] inspect ID
       truth [--root PATH] [--json] bridges --constants FILE (--queue FILE | --target ID)...
             [--targets N] [--top K] [--pool M]";

fn usage(message: impl Into<String>) -> (u8, Value) {
    (2, json!({"code":"usage", "message": message.into()}))
}

fn read_json(path: &str) -> Result<Value, (u8, Value)> {
    let bytes = std::fs::read(path).map_err(|error| {
        (
            1,
            json!({"code":"read_error", "path":path, "message":error.to_string()}),
        )
    })?;
    serde_json::from_slice(&bytes).map_err(|error| {
        (
            1,
            json!({"code":"invalid_json", "path":path, "message":error.to_string()}),
        )
    })
}

fn input_error(path: &str, message: String) -> (u8, Value) {
    (
        1,
        json!({"code":"invalid_input", "path":path, "message":message}),
    )
}

#[derive(Default)]
struct BridgeArgs {
    constants: Option<String>,
    queue: Option<String>,
    targets: Vec<String>,
    limit: Option<usize>,
    options: bridges::Options,
}

fn number(value: Option<&str>, flag: &str) -> Result<usize, (u8, Value)> {
    value
        .and_then(|value| value.parse().ok())
        .filter(|&value: &usize| value > 0)
        .ok_or_else(|| usage(format!("{flag} requires a positive integer")))
}

fn run_bridges(corpus: &Corpus, args: BridgeArgs) -> Result<Value, (u8, Value)> {
    let path = args
        .constants
        .ok_or_else(|| usage("bridges requires --constants FILE"))?;
    let constants =
        bridges::parse_constants(&read_json(&path)?).map_err(|error| input_error(&path, error))?;
    let mut targets = args.targets;
    if let Some(queue) = args.queue {
        let ids = bridges::parse_queue(&read_json(&queue)?)
            .map_err(|error| input_error(&queue, error))?;
        targets.extend(ids.into_iter().take(args.limit.unwrap_or(10)));
    }
    if targets.is_empty() {
        return Err(usage("bridges requires --queue FILE or --target ID"));
    }
    bridges::report(corpus, &constants, &targets, args.options)
        .map_err(|message| (3, json!({"code":"unknown_id", "message":message})))
}

/// Arguments stay OS-native so a non-UTF-8 `--root` path works; every other
/// argument must be UTF-8 text and is otherwise a usage error.
fn run(args: &[OsString]) -> Result<Value, (u8, Value)> {
    let mut root = PathBuf::from(".");
    let mut positional = Vec::new();
    let mut bridge = BridgeArgs::default();
    let mut bridge_flags = false;
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        let arg = arg.to_str().ok_or_else(|| {
            (
                2,
                json!({"code":"usage", "message": "arguments other than the --root path must be UTF-8"}),
            )
        })?;
        match arg {
            "--json" => {}
            "--root" => {
                root = args.next().map(PathBuf::from).ok_or_else(|| {
                    (
                        2,
                        json!({"code":"usage", "message": "--root requires a path"}),
                    )
                })?;
            }
            "--constants" | "--queue" | "--target" | "--targets" | "--top" | "--pool" => {
                bridge_flags = true;
                let value = args
                    .next()
                    .and_then(|value| value.to_str())
                    .map(str::to_owned);
                let text = value
                    .clone()
                    .ok_or_else(|| usage(format!("{arg} requires a UTF-8 value")))?;
                match arg {
                    "--constants" => bridge.constants = Some(text),
                    "--queue" => bridge.queue = Some(text),
                    "--target" => bridge.targets.push(text),
                    "--targets" => bridge.limit = Some(number(value.as_deref(), arg)?),
                    "--top" => bridge.options.top = number(value.as_deref(), arg)?,
                    _ => bridge.options.pool = number(value.as_deref(), arg)?,
                }
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
    let (id, bridges) = match positional.as_slice() {
        ["status"] if !bridge_flags => (None, false),
        ["inspect", id] if !id.is_empty() && !bridge_flags => (Some(*id), false),
        ["bridges"] => (None, true),
        _ => return Err(usage(HELP)),
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
    if bridges {
        let report = run_bridges(&corpus, bridge)?;
        for (key, value) in report.as_object().into_iter().flatten() {
            output[key] = value.clone();
        }
    } else if let Some(id) = id {
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
    let args: Vec<OsString> = env::args_os().skip(1).collect();
    if matches!(args.as_slice(), [arg] if arg == "--help" || arg == "-h") {
        println!("{HELP}");
        return ExitCode::SUCCESS;
    }
    let machine = args.iter().any(|arg| arg == "--json");
    match run(&args) {
        Ok(output) => {
            if machine {
                println!("{output}");
            } else if let Some(targets) = output["targets"].as_array() {
                println!(
                    "Bridge candidates ({}); advisory ranking only, not a proof",
                    output["input_identity"]
                );
                for target in targets {
                    println!("\n{}", target["statement_id"].as_str().unwrap_or_default());
                    if let Some(reason) = target["skipped"].as_str() {
                        println!("  skipped: {reason}");
                    }
                    for arity in ["singles", "pairs", "triples"] {
                        for candidate in target[arity].as_array().into_iter().flatten() {
                            let ids: Vec<_> = candidate["statement_ids"]
                                .as_array()
                                .into_iter()
                                .flatten()
                                .filter_map(Value::as_str)
                                .collect();
                            println!(
                                "  {arity:8} {:.3}  {}",
                                candidate["score"].as_f64().unwrap_or(0.0),
                                ids.join(" + ")
                            );
                        }
                    }
                }
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
