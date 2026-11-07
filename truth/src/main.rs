use serde_json::{Value, json};
use std::{collections::BTreeMap, env, ffi::OsString, path::PathBuf, process::ExitCode};
use truth::{Corpus, bridges, check, orphans, thickness};

const HELP: &str = "Usage: truth [--root PATH] [--json] status
       truth [--root PATH] [--json] check
       truth [--root PATH] [--json] inspect ID
       truth [--root PATH] [--json] thickness [--queue] [--frontier-root STATEMENT-ID]
       truth [--root PATH] [--json] orphans [--frontier-root STATEMENT-ID] [--by module|family] [--senses]
       truth [--root PATH] [--json] bridges --constants FILE (--queue-file FILE | --target ID)...
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
        return Err(usage("bridges requires --queue-file FILE or --target ID"));
    }
    bridges::report(corpus, &constants, &targets, args.options)
        .map_err(|message| (3, json!({"code":"unknown_id", "message":message})))
}

/// `thickness` output: JSON as `scripts/corpus.py thickness --json` prints it
/// (plus `input_identity`), and the same text as the Python command.
fn thickness_command(
    root: &std::path::Path,
    corpus: &Corpus,
    frontier_root: &str,
    queue: bool,
) -> (Value, String) {
    let records = thickness::Records::from_corpus(corpus);
    let kinds = thickness::transcription_kinds(root, &records.results);
    let frontier = thickness::frontier_inputs(frontier_root, &records, kinds);
    let report = thickness::thickness_report(&frontier, &records);
    if queue {
        let queue = thickness::thickness_queue(&frontier, &report, &records);
        let text = thickness::format_thickness_queue(frontier_root, &queue);
        (
            json!({"root": frontier_root, "queue": queue, "input_identity": corpus.input_identity()}),
            text,
        )
    } else {
        let text = thickness::format_thickness(&report);
        (
            json!({"report": report, "delta": null, "input_identity": corpus.input_identity()}),
            text,
        )
    }
}

/// The partial-port notice `check` prints on stderr before its result.
fn check_notice() -> String {
    format!(
        "notice: truth check is a partial port of `python3 scripts/corpus.py check`, which stays the corpus gate; \
         still Python-only: {}",
        check::PYTHON_ONLY.join("; ")
    )
}

/// `check`: Python's `corpus ok: …` line and warnings, or its first error.
fn check_command(root: &std::path::Path) -> Result<(Value, Option<String>), (u8, Value)> {
    match check::check(root) {
        Ok(outcome) => {
            let summary = outcome.summary();
            let mut text = vec![check_notice()];
            text.extend(
                outcome
                    .warnings
                    .iter()
                    .map(|warning| format!("warning: {warning}")),
            );
            Ok((
                json!({
                    "schema_version": 1,
                    "ok": true,
                    "complete": false,
                    "python_only": check::PYTHON_ONLY,
                    "counts": outcome.counts.iter().map(|(k, v)| (k.to_string(), json!(v))).collect::<serde_json::Map<_, _>>(),
                    "warnings": outcome.warnings,
                    "summary": summary,
                }),
                Some(format!("\u{0}{}\u{0}{summary}", text.join("\n"))),
            ))
        }
        Err(message) => Err((
            1,
            json!({"code": "corpus_error", "message": message, "complete": false,
                   "python_only": check::PYTHON_ONLY}),
        )),
    }
}

/// Arguments stay OS-native so a non-UTF-8 `--root` path works; every other
/// argument must be UTF-8 text and is otherwise a usage error.
fn run(args: &[OsString]) -> Result<(Value, Option<String>), (u8, Value)> {
    let mut root = PathBuf::from(".");
    let mut positional = Vec::new();
    let mut bridge = BridgeArgs::default();
    let mut bridge_flags = false;
    let mut queue = false;
    let mut senses = false;
    let mut group_by: Option<orphans::GroupBy> = None;
    let mut frontier_root = thickness::DEFAULT_ROOT.to_owned();
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
            "--queue" => queue = true,
            "--senses" => senses = true,
            "--by" => {
                group_by = Some(
                    args.next()
                        .and_then(|value| value.to_str())
                        .and_then(orphans::GroupBy::parse)
                        .ok_or_else(|| usage("--by requires module or family"))?,
                );
            }
            "--frontier-root" => {
                frontier_root = args
                    .next()
                    .and_then(|value| value.to_str())
                    .filter(|value| !value.is_empty())
                    .ok_or_else(|| {
                        (
                            2,
                            json!({"code":"usage", "message": "--frontier-root requires a statement ID"}),
                        )
                    })?
                    .to_owned();
            }
            "--root" => {
                root = args.next().map(PathBuf::from).ok_or_else(|| {
                    (
                        2,
                        json!({"code":"usage", "message": "--root requires a path"}),
                    )
                })?;
            }
            "--constants" | "--queue-file" | "--target" | "--targets" | "--top" | "--pool" => {
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
                    "--queue-file" => bridge.queue = Some(text),
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
    if matches!(positional.as_slice(), ["check"]) {
        if bridge_flags
            || queue
            || senses
            || group_by.is_some()
            || frontier_root != thickness::DEFAULT_ROOT
        {
            return Err(usage("check takes no options besides --root and --json"));
        }
        return check_command(&root);
    }
    let thickness = matches!(positional.as_slice(), ["thickness"]);
    let orphan_report = matches!(positional.as_slice(), ["orphans"]);
    let (id, bridges) = match positional.as_slice() {
        ["status"] | ["thickness"] | ["orphans"] if !bridge_flags => (None, false),
        ["inspect", id] if !id.is_empty() && !bridge_flags => (Some(*id), false),
        ["bridges"] => (None, true),
        _ => return Err(usage(HELP)),
    };
    if !thickness && queue {
        return Err(usage("--queue applies only to thickness"));
    }
    if !thickness && !orphan_report && frontier_root != thickness::DEFAULT_ROOT {
        return Err(usage(
            "--frontier-root applies only to thickness and orphans",
        ));
    }
    if !orphan_report && (senses || group_by.is_some()) {
        return Err(usage("--by and --senses apply only to orphans"));
    }
    if senses && group_by.is_some() {
        return Err(usage("--senses and --by are alternatives"));
    }
    let corpus = Corpus::load(&root).map_err(|error| {
        (
            1,
            json!({"code":error.code, "path":error.path, "message":error.message}),
        )
    })?;
    if thickness {
        let (output, text) = thickness_command(&root, &corpus, &frontier_root, queue);
        return Ok((output, Some(text)));
    }
    if orphan_report {
        let (mut output, text) = if senses {
            let report = orphans::sense_report(&corpus, &frontier_root);
            let text = orphans::format_senses(&report);
            (report, text)
        } else {
            let by = group_by.unwrap_or(orphans::GroupBy::Module);
            let report = orphans::report(&root, &corpus, &frontier_root, by);
            let text = orphans::format(&report);
            (report, text)
        };
        output["schema_version"] = json!(1);
        output["input_identity"] = json!(corpus.input_identity());
        return Ok((output, Some(text)));
    }
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
    Ok((output, None))
}

fn main() -> ExitCode {
    let args: Vec<OsString> = env::args_os().skip(1).collect();
    if matches!(args.as_slice(), [arg] if arg == "--help" || arg == "-h") {
        println!("{HELP}");
        return ExitCode::SUCCESS;
    }
    let machine = args.iter().any(|arg| arg == "--json");
    match run(&args) {
        Ok((output, text)) => {
            if machine {
                println!("{output}");
            } else if let Some(text) = text {
                // `check` text: stderr part, then the stdout summary.
                if let Some(rest) = text.strip_prefix('\u{0}') {
                    let (stderr, stdout) = rest.split_once('\u{0}').unwrap_or((rest, ""));
                    eprintln!("{stderr}");
                    println!("{stdout}");
                } else {
                    println!("{text}");
                }
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
            } else if error["code"] == "corpus_error" {
                eprintln!("{}", check_notice());
                eprintln!(
                    "corpus error: {}",
                    error["message"].as_str().unwrap_or_default()
                );
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
