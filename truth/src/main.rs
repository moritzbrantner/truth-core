use serde_json::{Value, json};
use std::{collections::BTreeMap, env, ffi::OsString, path::PathBuf, process::ExitCode};
use truth::{Corpus, bridges, check, context, dossier, frontier, related, thickness};

const HELP: &str = "Usage: truth [--root PATH] [--json] status
       truth [--root PATH] [--json] check
       truth [--root PATH] [--json] inspect ID
       truth [--root PATH] [--json] thickness [--queue] [--frontier-root STATEMENT-ID]
       truth [--root PATH] [--json] frontier [--reaching-root] [--routes] [--frontier-root STATEMENT-ID]
       truth [--root PATH] [--json] frontier-diff --base REV [--head REV] [--frontier-root STATEMENT-ID]
       truth [--root PATH] [--json] bridges --constants FILE (--queue-file FILE | --target ID)...
             [--targets N] [--top K] [--pool M]
       truth [--root PATH] [--json] related STATEMENT-ID [--limit N]
       truth [--root PATH] [--json] dossier (STATEMENT-ID | --all) [--frontier-json FILE] [--limit N]
       truth [--root PATH] [--json] context TARGET [--frontier-json FILE] [--limit N] [--related N]

dossier and context compute the frontier in-process, or read it from FILE, written by
`python3 scripts/corpus.py frontier --json [--root STATEMENT-ID]` on the same checkout.";

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
    let flags = frontier::transcription_flags(root, &records);
    let frontier = thickness::frontier_inputs(frontier_root, &records, &flags);
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

#[derive(Default)]
struct FrontierArgs {
    reaching_root: bool,
    routes: bool,
    base: Option<String>,
    head: Option<String>,
}

/// `frontier`: JSON as `scripts/corpus.py frontier --json` prints it (plus
/// `input_identity`; `next_steps` only without `--routes`, as in Python), and
/// the same text as the Python command. Only the requested form is computed.
fn frontier_command_output(
    root: &std::path::Path,
    corpus: &Corpus,
    frontier_root: &str,
    args: &FrontierArgs,
    machine: bool,
) -> (Value, String) {
    let next_steps = machine && !args.routes;
    let report =
        frontier::current_frontier(root, corpus, frontier_root, args.reaching_root, next_steps);
    let identity = json!(corpus.input_identity());
    if args.routes {
        let mut routes = report["routes"].clone();
        let text = if machine {
            String::new()
        } else {
            frontier::format_routes(&routes)
        };
        routes["input_identity"] = identity;
        return (routes, text);
    }
    let text = if machine {
        String::new()
    } else {
        frontier::format_frontier(&report)
    };
    let mut report = report;
    report["input_identity"] = identity;
    (report, text)
}

/// `frontier-diff`: Python `frontier_delta` between the base revision and the
/// head revision or working tree (see `frontier::revision_frontier` for the
/// engine each revision uses).
fn frontier_diff_output(
    root: &std::path::Path,
    corpus: &Corpus,
    frontier_root: &str,
    args: &FrontierArgs,
) -> Result<(Value, String), (u8, Value)> {
    let failed = |message: String| (1, json!({"code": "revision_error", "message": message}));
    let base_revision = args.base.as_deref().unwrap_or_default();
    let (base, base_engine) =
        frontier::revision_frontier(root, base_revision, frontier_root).map_err(failed)?;
    let (head, head_engine) = match args.head.as_deref() {
        Some(revision) => {
            frontier::revision_frontier(root, revision, frontier_root).map_err(failed)?
        }
        None => (
            frontier::current_frontier(root, corpus, frontier_root, true, false),
            "rust",
        ),
    };
    let mut delta = frontier::frontier_delta(&base, &head);
    delta["base"] = json!(base_revision);
    delta["head"] = json!(args.head.as_deref().unwrap_or("working tree"));
    let text = frontier::format_frontier_delta(&delta);
    delta["engines"] = json!({"base": base_engine, "head": head_engine});
    delta["input_identity"] = json!(corpus.input_identity());
    Ok((delta, text))
}

#[derive(Default)]
struct ResearchArgs {
    flags: bool,
    all: bool,
    limit: Option<i64>,
    related: Option<i64>,
    frontier: Option<String>,
}

fn integer(value: Option<&str>, flag: &str) -> Result<i64, (u8, Value)> {
    value
        .and_then(|value| value.parse().ok())
        .ok_or_else(|| usage(format!("{flag} requires an integer")))
}

fn unknown(message: &str) -> (u8, Value) {
    (3, json!({"code":"unknown_id", "message":message}))
}

fn invalid_target(message: &str) -> (u8, Value) {
    (2, json!({"code":"invalid_target", "message":message}))
}

fn with_identity(value: impl serde::Serialize, corpus: &Corpus) -> Value {
    let mut value = serde_json::to_value(value).unwrap_or(Value::Null);
    if let Some(object) = value.as_object_mut() {
        object.insert("input_identity".into(), json!(corpus.input_identity()));
    }
    value
}

/// The frontier view `dossier` and `context` read: from `--frontier-json
/// FILE` (a `corpus.py frontier --json` report) when given, otherwise
/// computed in-process by the Rust frontier on this checkout.
fn frontier_view(
    root: &std::path::Path,
    corpus: &Corpus,
    args: &ResearchArgs,
    frontier_root: &str,
) -> Result<dossier::FrontierView, (u8, Value)> {
    let (view, source) = match args.frontier.as_deref() {
        Some(path) => {
            let view = dossier::FrontierView::from_report(&read_json(path)?)
                .map_err(|error| input_error(path, error))?;
            if frontier_root != thickness::DEFAULT_ROOT
                && view.root.as_deref() != Some(frontier_root)
            {
                return Err(usage(format!(
                    "--frontier-root {frontier_root} differs from the report root {}",
                    view.root.as_deref().unwrap_or("None")
                )));
            }
            (view, path)
        }
        None => {
            let report = frontier::current_frontier(root, corpus, frontier_root, false, false);
            let view = dossier::FrontierView::from_report(&report)
                .map_err(|error| input_error("corpus", error))?;
            (view, "corpus")
        }
    };
    if !view.root_known {
        return Err(input_error(
            source,
            format!(
                "unknown root statement: {}",
                view.root.as_deref().unwrap_or("None")
            ),
        ));
    }
    Ok(view)
}

/// `related`, `dossier` and `context`: JSON as the Python commands print it
/// (plus `input_identity`, except `dossier --all`) and byte-identical text.
fn research_command(
    root: &std::path::Path,
    corpus: &Corpus,
    command: &str,
    target: Option<&str>,
    args: &ResearchArgs,
    frontier_root: &str,
) -> Result<(Value, Option<String>), (u8, Value)> {
    match command {
        "related" => {
            let target = target.ok_or_else(|| usage(HELP))?;
            let report =
                related::related(corpus, target, args.limit.unwrap_or(related::DEFAULT_LIMIT))
                    .map_err(|error| match error {
                        related::LookupError::Unknown(message) => unknown(&message),
                        related::LookupError::Invalid(message) => invalid_target(&message),
                    })?;
            let text = related::format_related(&report);
            Ok((with_identity(&report, corpus), Some(text)))
        }
        "dossier" => {
            let index = dossier::DossierIndex::new(corpus);
            if let Some(id) = target
                && corpus.get("statements", id).is_none()
            {
                return Err(unknown(&format!("unknown statement: {id}")));
            }
            let view = frontier_view(root, corpus, args, frontier_root)?;
            if args.all {
                let all: serde_json::Map<String, Value> = index
                    .statement_ids()
                    .into_iter()
                    .filter_map(|id| index.dossier(id, &view).map(|d| (id.to_owned(), json!(d))))
                    .collect();
                let text = Value::Object(all.clone()).to_string();
                return Ok((Value::Object(all), Some(text)));
            }
            let id = target.ok_or_else(|| usage(HELP))?;
            let found = index
                .dossier(id, &view)
                .ok_or_else(|| unknown(&format!("unknown statement: {id}")))?;
            let limit = args
                .limit
                .unwrap_or(dossier::DEFAULT_LIMIT)
                .try_into()
                .ok()
                .filter(|limit: &usize| *limit > 0);
            let text = dossier::format_dossier(&found, &index, limit);
            Ok((with_identity(&found, corpus), Some(text)))
        }
        _ => {
            let target = target.ok_or_else(|| usage(HELP))?;
            let argument =
                context::resolve_target(corpus, target).map_err(|error| match error {
                    context::TargetError::Unknown(message) => unknown(&message),
                    context::TargetError::Ambiguous(message) => invalid_target(&message),
                })?;
            let view = frontier_view(root, corpus, args, frontier_root)?;
            let count = args.related.unwrap_or(context::DEFAULT_RELATED);
            let mut matches = Vec::new();
            if count != 0 {
                let conclusion = corpus
                    .get("arguments", &argument)
                    .and_then(|record| record.fields.get("conclusion_statement_id"))
                    .and_then(Value::as_str)
                    .unwrap_or_default();
                match related::related(corpus, conclusion, count) {
                    Ok(report) => matches = report.matches,
                    Err(error) => {
                        eprintln!("context: related ranking unavailable: {}", error.message())
                    }
                }
            }
            let pack = context::context_pack(root, corpus, &view, &argument, &matches);
            let text = context::format_context(&pack, args.limit.unwrap_or(context::DEFAULT_LIMIT));
            Ok((with_identity(&pack, corpus), Some(text)))
        }
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
    let machine = args.iter().any(|arg| arg == "--json");
    let mut root = PathBuf::from(".");
    let mut positional = Vec::new();
    let mut bridge = BridgeArgs::default();
    let mut bridge_flags = false;
    let mut queue = false;
    let mut frontier_root = thickness::DEFAULT_ROOT.to_owned();
    let mut frontier = FrontierArgs::default();
    let mut research = ResearchArgs::default();
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
            "--reaching-root" => frontier.reaching_root = true,
            "--routes" => frontier.routes = true,
            "--base" | "--head" => {
                let value = args
                    .next()
                    .and_then(|value| value.to_str())
                    .filter(|value| !value.is_empty())
                    .ok_or_else(|| usage(format!("{arg} requires a revision")))?
                    .to_owned();
                if arg == "--base" {
                    frontier.base = Some(value);
                } else {
                    frontier.head = Some(value);
                }
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
            "--all" => {
                research.flags = true;
                research.all = true;
            }
            "--limit" | "--related" | "--frontier-json" => {
                research.flags = true;
                let value = args.next().and_then(|value| value.to_str());
                match arg {
                    "--limit" => research.limit = Some(integer(value, arg)?),
                    "--related" => research.related = Some(integer(value, arg)?),
                    _ => {
                        research.frontier = Some(
                            value
                                .ok_or_else(|| usage(format!("{arg} requires a UTF-8 path")))?
                                .to_owned(),
                        )
                    }
                }
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
        if bridge_flags || research.flags || queue || frontier_root != thickness::DEFAULT_ROOT {
            return Err(usage("check takes no options besides --root and --json"));
        }
        return check_command(&root);
    }
    let research_target = match positional.as_slice() {
        [command @ ("related" | "dossier" | "context"), rest @ ..] if !bridge_flags => {
            let target = match rest {
                [] if *command == "dossier" && research.all => None,
                [id] if !id.is_empty() && !research.all => Some(*id),
                _ => return Err(usage(HELP)),
            };
            let applies = match *command {
                "related" => {
                    research.frontier.is_none()
                        && research.related.is_none()
                        && frontier_root == thickness::DEFAULT_ROOT
                }
                "dossier" => research.related.is_none(),
                _ => true,
            };
            let frontier_flags = frontier.reaching_root
                || frontier.routes
                || frontier.base.is_some()
                || frontier.head.is_some();
            if !applies || queue || frontier_flags {
                return Err(usage(format!("an option does not apply to {command}")));
            }
            Some((*command, target))
        }
        _ => None,
    };
    if research_target.is_none() && research.flags {
        return Err(usage(
            "--all, --limit, --related and --frontier-json apply only to related, dossier and context",
        ));
    }
    if let Some((command, target)) = research_target {
        let corpus = Corpus::load(&root).map_err(|error| {
            (
                1,
                json!({"code":error.code, "path":error.path, "message":error.message}),
            )
        })?;
        return research_command(&root, &corpus, command, target, &research, &frontier_root);
    }
    let thickness = matches!(positional.as_slice(), ["thickness"]);
    let command = positional.first().copied().unwrap_or_default();
    let frontier_command = matches!(positional.as_slice(), ["frontier"] | ["frontier-diff"]);
    let (id, bridges) = match positional.as_slice() {
        ["status"] | ["thickness"] | ["frontier"] | ["frontier-diff"] if !bridge_flags => {
            (None, false)
        }
        ["inspect", id] if !id.is_empty() && !bridge_flags => (Some(*id), false),
        ["bridges"] => (None, true),
        _ => return Err(usage(HELP)),
    };
    if !thickness && queue {
        return Err(usage("--queue applies only to thickness"));
    }
    if !thickness && !frontier_command && frontier_root != thickness::DEFAULT_ROOT {
        return Err(usage(
            "--frontier-root applies only to thickness, frontier, frontier-diff, dossier and context",
        ));
    }
    if command != "frontier" && (frontier.reaching_root || frontier.routes) {
        return Err(usage("--reaching-root and --routes apply only to frontier"));
    }
    if command != "frontier-diff" && (frontier.base.is_some() || frontier.head.is_some()) {
        return Err(usage("--base and --head apply only to frontier-diff"));
    }
    if command == "frontier-diff" && frontier.base.is_none() {
        return Err(usage("frontier-diff requires --base REV"));
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
    if command == "frontier" {
        let (output, text) =
            frontier_command_output(&root, &corpus, &frontier_root, &frontier, machine);
        return Ok((output, Some(text)));
    }
    if command == "frontier-diff" {
        let (output, text) = frontier_diff_output(&root, &corpus, &frontier_root, &frontier)?;
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
