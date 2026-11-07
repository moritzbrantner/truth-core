//! `truth check`: a port of `scripts/corpus.py check` (`validate()` and
//! `check_warnings()`), rule for rule and in the same order, so the first
//! error a broken corpus reports is the one Python reports.
//!
//! Partial port: the rules in [`PYTHON_ONLY`] still run only in Python, and
//! `scripts/corpus.py check` stays the corpus gate until they are ported.
//! Messages are Python's, except where Python formats a parser exception
//! (invalid JSON) or a value that is not a string, list or scalar.

use crate::{Record, thickness};
use fancy_regex::Regex;
use serde_json::{Map, Value};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fs,
    path::{Path, PathBuf},
};

/// Rules of `corpus.py check` that this port does not run yet.
pub const PYTHON_ONLY: &[&str] = &[
    "source_evidence.validate_manifest: the per-kind passage manifest schema (text witness, media span, web snapshot, bibliographic span)",
    "check_warnings: the opaque-atom transcription warning (transcription_flags opaque_atoms)",
];

type Obj = Map<String, Value>;
type Res<T> = Result<T, String>;

const ENTITY_KINDS: &[&str] = &["argument", "claim", "inference", "source", "statement"];
const MATHLIB_PERMITTED_AXIOMS: &[&str] = &["propext", "Classical.choice", "Quot.sound"];
const FLOOR_BASES: &[&str] = &["common_ground", "observation", "retorsion"];
const LEGACY_FLOOR_STATEMENTS: &[&str] = &["STMT-EXCLUDED-MIDDLE"];
const DISAGREEMENT_NONE: &str = "none recorded";
const TRANSCRIPTION_KINDS: &[&str] = &[
    "assembly",
    "instantiation",
    "opaque_atoms",
    "single_application",
];
const ATTEMPT_KINDS: &[&str] = &[
    "countermodel",
    "derivation",
    "reading",
    "refutation",
    "source-search",
];
const ATTEMPT_OUTCOMES: &[&str] = &["blocked", "failed", "rejected", "succeeded", "superseded"];
const ATTRIBUTION_PREFIX: &str = "The passage states ";
const MIN_ATTRIBUTION_CHARS: usize = 40;
const STRENGTH_ROLES: &[&str] = &[
    "allowed_cases",
    "converse",
    "delta_forward",
    "equivalence",
    "implication",
    "reconstruction",
    "remainder_identity",
];
const DATA_STRUCTURES: &[&str] = &[
    "TruthCore.Explanation.ExistencePSR.Model",
    "TruthCore.German.Kant.CosmologicalInference.Ontic",
];

/// What a successful check reports.
pub struct Outcome {
    pub counts: Vec<(&'static str, usize)>,
    pub warnings: Vec<String>,
}

impl Outcome {
    /// The `corpus ok: …` line, byte-identical to Python's.
    pub fn summary(&self) -> String {
        let count = |kind: &str| {
            self.counts
                .iter()
                .find(|(name, _)| *name == kind)
                .map_or(0, |(_, count)| *count)
        };
        format!(
            "corpus ok: {} sources, {} passages, {} statements, {} claims, {} inferences, {} arguments, \
             {} relations, {} results, {} candidates, {} definitions, {} disambiguations, {} attempts, {} models",
            count("sources"),
            count("passages"),
            count("statements"),
            count("claims"),
            count("inferences"),
            count("arguments"),
            count("relations"),
            count("results"),
            count("candidates"),
            count("definitions"),
            count("disambiguations"),
            count("attempts"),
            count("models"),
        )
    }
}

// ---------------------------------------------------------------------------
// Python value semantics

fn get<'a>(record: &'a Obj, field: &str) -> Option<&'a Value> {
    record.get(field).filter(|value| !value.is_null())
}

fn string<'a>(record: &'a Obj, field: &str) -> Option<&'a str> {
    record.get(field).and_then(Value::as_str)
}

fn text<'a>(record: &'a Obj, field: &str) -> &'a str {
    string(record, field).unwrap_or_default()
}

fn strings<'a>(record: &'a Obj, field: &str) -> Vec<&'a str> {
    record
        .get(field)
        .and_then(Value::as_array)
        .map(|items| items.iter().filter_map(Value::as_str).collect())
        .unwrap_or_default()
}

fn truthy(value: Option<&Value>) -> bool {
    match value {
        None | Some(Value::Null) => false,
        Some(Value::Bool(value)) => *value,
        Some(Value::String(value)) => !value.is_empty(),
        Some(Value::Array(value)) => !value.is_empty(),
        Some(Value::Object(value)) => !value.is_empty(),
        Some(Value::Number(value)) => value.as_f64() != Some(0.0),
    }
}

/// `value in (None, "", [])`.
fn absent(value: Option<&Value>) -> bool {
    match value {
        None | Some(Value::Null) => true,
        Some(Value::String(text)) => text.is_empty(),
        Some(Value::Array(items)) => items.is_empty(),
        _ => false,
    }
}

fn quote(text: &str) -> String {
    let delimiter = if text.contains('\'') && !text.contains('"') {
        '"'
    } else {
        '\''
    };
    let mut out = String::from(delimiter);
    for c in text.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c == delimiter => {
                out.push('\\');
                out.push(c);
            }
            c if (c as u32) < 0x20 || c as u32 == 0x7f => {
                out.push_str(&format!("\\x{:02x}", c as u32))
            }
            c => out.push(c),
        }
    }
    out.push(delimiter);
    out
}

/// Python `repr` of a JSON value.
fn py_repr(value: Option<&Value>) -> String {
    match value {
        None | Some(Value::Null) => "None".into(),
        Some(Value::Bool(true)) => "True".into(),
        Some(Value::Bool(false)) => "False".into(),
        Some(Value::Number(number)) => number.to_string(),
        Some(Value::String(text)) => quote(text),
        Some(Value::Array(items)) => format!(
            "[{}]",
            items
                .iter()
                .map(|item| py_repr(Some(item)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Some(Value::Object(object)) => format!(
            "{{{}}}",
            object
                .iter()
                .map(|(key, item)| format!("{}: {}", quote(key), py_repr(Some(item))))
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

/// Python `str` (what an f-string prints) of a JSON value.
fn py_str(value: Option<&Value>) -> String {
    match value {
        Some(Value::String(text)) => text.clone(),
        other => py_repr(other),
    }
}

fn str_list_repr<S: AsRef<str>>(items: &[S]) -> String {
    format!(
        "[{}]",
        items
            .iter()
            .map(|item| quote(item.as_ref()))
            .collect::<Vec<_>>()
            .join(", ")
    )
}

fn require(record: &Obj, fields: &[&str], path: &str) -> Res<()> {
    let missing: Vec<&str> = fields
        .iter()
        .copied()
        .filter(|field| absent(record.get(*field)))
        .collect();
    if missing.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "{path}: missing required field(s): {}",
            missing.join(", ")
        ))
    }
}

fn require_string_list<'a>(
    record: &'a Obj,
    field: &str,
    path: &str,
    allow_empty: bool,
) -> Res<Vec<&'a str>> {
    let items = record
        .get(field)
        .and_then(Value::as_array)
        .and_then(|items| {
            items
                .iter()
                .map(|item| item.as_str().filter(|text| !text.is_empty()))
                .collect::<Option<Vec<_>>>()
        })
        .ok_or_else(|| format!("{path}: {field} must be a list of non-empty strings"))?;
    if !allow_empty && items.is_empty() {
        return Err(format!("{path}: {field} must not be empty"));
    }
    Ok(items)
}

/// No two equal items (Python `len(set(items)) == len(items)`).
fn distinct(items: &[Value]) -> bool {
    items
        .iter()
        .enumerate()
        .all(|(i, item)| !items[..i].contains(item))
}

fn is_word(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

fn is_ident(text: &str) -> bool {
    let mut chars = text.chars();
    chars
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// finite_models `NAME`: dotted identifiers.
fn lean_name(value: Option<&Value>) -> bool {
    value
        .and_then(Value::as_str)
        .is_some_and(|text| text.split('.').all(is_ident))
}

/// finite_models `TERM`: a dotted identifier whose later segments may be numerals.
fn lean_term(text: &str) -> bool {
    let mut segments = text.split('.');
    segments.next().is_some_and(is_ident)
        && segments.all(|segment| {
            is_ident(segment)
                || (!segment.is_empty() && segment.chars().all(|c| c.is_ascii_digit()))
        })
}

/// `PREFIX[A-Z0-9-]+` as a full match.
fn upper_id(text: &str, prefix: &str) -> bool {
    text.strip_prefix(prefix).is_some_and(|rest| {
        !rest.is_empty()
            && rest
                .chars()
                .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '-')
    })
}

/// Python `re` `$` also matches before one final newline.
fn dollar(text: &str) -> &str {
    text.strip_suffix('\n').unwrap_or(text)
}

fn digits(text: &str, count: usize) -> bool {
    text.len() == count && text.chars().all(|c| c.is_ascii_digit())
}

/// `datetime.date.fromisoformat(value).isoformat() == value`.
fn iso_date(text: &str) -> bool {
    let parts: Vec<&str> = text.split('-').collect();
    let [year, month, day] = parts.as_slice() else {
        return false;
    };
    if !(digits(year, 4) && digits(month, 2) && digits(day, 2)) {
        return false;
    }
    let (year, month, day): (u32, u32, u32) = (
        year.parse().unwrap_or(0),
        month.parse().unwrap_or(0),
        day.parse().unwrap_or(0),
    );
    let leap = year % 4 == 0 && (year % 100 != 0 || year % 400 == 0);
    let days = match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if leap => 29,
        2 => 28,
        _ => 0,
    };
    year >= 1 && day >= 1 && day <= days
}

/// `STMT-…`, `DEF-…` and `DISAMB-…` IDs cited in prose (Python `PROSE_ID_RE`).
fn prose_ids(text: &str) -> Vec<&str> {
    let chars: Vec<(usize, char)> = text.char_indices().collect();
    let upper = |c: char| c.is_ascii_uppercase() || c.is_ascii_digit();
    let mut found = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        let (start, _) = chars[i];
        let boundary = i == 0 || !is_word(chars[i - 1].1);
        let prefix = ["STMT-", "DEF-", "DISAMB-"]
            .into_iter()
            .find(|prefix| text[start..].starts_with(prefix));
        if let (true, Some(prefix)) = (boundary, prefix) {
            let mut j = i + prefix.len();
            let mut ends = Vec::new();
            loop {
                let first = j;
                while j < chars.len() && upper(chars[j].1) {
                    j += 1;
                }
                if j == first {
                    break;
                }
                ends.push(j);
                if j + 1 < chars.len() && chars[j].1 == '-' && upper(chars[j + 1].1) {
                    j += 1;
                } else {
                    break;
                }
            }
            let last_ok = |end: usize| end >= chars.len() || !is_word(chars[end].1);
            let end = match ends.as_slice() {
                [] => None,
                [.., last] if last_ok(*last) => Some(*last),
                [.., before, _] => Some(*before),
                [_] => None,
            };
            if let Some(end) = end {
                let stop = chars.get(end).map_or(text.len(), |(offset, _)| *offset);
                found.push(&text[start..stop]);
                i = end;
                continue;
            }
        }
        i += 1;
    }
    found
}

// ---------------------------------------------------------------------------
// Loading

fn relative(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .into_owned()
}

fn read_object(root: &Path, path: &Path) -> Res<Obj> {
    let rel = relative(root, path);
    let text =
        fs::read_to_string(path).map_err(|error| format!("{rel}: cannot read JSON: {error}"))?;
    let value: Value =
        serde_json::from_str(&text).map_err(|error| format!("{rel}: cannot read JSON: {error}"))?;
    match value {
        Value::Object(object) => Ok(object),
        _ => Err(format!("{rel}: top-level JSON value must be an object")),
    }
}

fn json_paths(directory: &Path) -> Vec<PathBuf> {
    let mut paths: Vec<PathBuf> = fs::read_dir(directory)
        .into_iter()
        .flatten()
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|ext| ext == "json") && path.is_file())
        .collect();
    paths.sort();
    paths
}

/// Python `load_dir`: every `corpus/<name>/*.json` object, in path order.
fn load_dir(root: &Path, name: &str) -> Res<Vec<Record>> {
    json_paths(&root.join("corpus").join(name))
        .into_iter()
        .map(|path| {
            Ok(Record {
                fields: read_object(root, &path)?,
                path: relative(root, &path),
            })
        })
        .collect()
}

/// Python `index_by_id`: record position by ID.
fn index_by_id(records: &[Record], kind: &str) -> Res<HashMap<String, usize>> {
    let mut index: HashMap<String, usize> = HashMap::new();
    for (position, record) in records.iter().enumerate() {
        require(&record.fields, &["id"], &record.path)?;
        let id = string(&record.fields, "id")
            .ok_or_else(|| format!("{}: id must be a string", record.path))?;
        if let Some(first) = index.get(id) {
            return Err(format!(
                "{}: duplicate {kind} id {id}; first seen in {}",
                record.path, records[*first].path
            ));
        }
        index.insert(id.to_owned(), position);
    }
    Ok(index)
}

/// `.lean` files under `TruthCore/`, sorted like Python's `sorted(rglob)`.
fn lean_files(root: &Path) -> Vec<(Vec<String>, PathBuf)> {
    let mut files = Vec::new();
    let mut pending = vec![root.join("TruthCore")];
    while let Some(directory) = pending.pop() {
        for entry in fs::read_dir(&directory).into_iter().flatten().flatten() {
            let path = entry.path();
            if path.is_dir() {
                pending.push(path);
            } else if path.extension().is_some_and(|ext| ext == "lean") {
                let parts = path
                    .strip_prefix(root)
                    .unwrap_or(&path)
                    .components()
                    .map(|part| part.as_os_str().to_string_lossy().into_owned())
                    .collect();
                files.push((parts, path));
            }
        }
    }
    files.sort();
    files
}

/// The concatenated Lean text, with a token set that answers most
/// substring queries without a scan (a token is always a substring).
struct LeanText {
    text: String,
    tokens: HashSet<String>,
}

impl LeanText {
    fn load(files: &[(Vec<String>, PathBuf)]) -> Self {
        let text = files
            .iter()
            .map(|(_, path)| fs::read_to_string(path).unwrap_or_default())
            .collect::<Vec<_>>()
            .join("\n");
        let tokens = text
            .split(|c: char| c.is_whitespace() || (c.is_ascii_punctuation() && c != '_'))
            .filter(|token| !token.is_empty())
            .map(str::to_owned)
            .collect();
        Self { text, tokens }
    }

    fn contains(&self, needle: &str) -> bool {
        self.tokens.contains(needle) || self.text.contains(needle)
    }
}

fn lean_tail_exists(path: &str, declaration: Option<&Value>, lean: &LeanText) -> Res<()> {
    let declaration = declaration
        .and_then(Value::as_str)
        .filter(|text| !text.is_empty())
        .ok_or_else(|| {
            format!("{path}: lean_declaration must be a non-empty string when present")
        })?;
    let tail = declaration.rsplit('.').next().unwrap_or(declaration);
    if lean.contains(tail) {
        Ok(())
    } else {
        Err(format!(
            "{path}: Lean declaration tail {} was not found under TruthCore/",
            quote(tail)
        ))
    }
}

fn module_path(root: &Path, module: &str) -> PathBuf {
    root.join(module.replace('.', "/") + ".lean")
}

/// `^(?:public\s+)?import\s+(\S+)` over a whole file, multiline.
fn lean_imports(text: &str) -> Vec<&str> {
    let mut imports = Vec::new();
    let mut line_start = true;
    for (offset, c) in text.char_indices() {
        if line_start {
            let mut rest = &text[offset..];
            if let Some(after) = rest.strip_prefix("public") {
                let trimmed = after.trim_start();
                if trimmed.len() < after.len() && trimmed.starts_with("import") {
                    rest = trimmed;
                }
            }
            if let Some(after) = rest.strip_prefix("import") {
                let trimmed = after.trim_start();
                if trimmed.len() < after.len() {
                    let end = trimmed.find(char::is_whitespace).unwrap_or(trimmed.len());
                    if end > 0 {
                        imports.push(&trimmed[..end]);
                    }
                }
            }
        }
        line_start = c == '\n';
    }
    imports
}

struct Checker<'r> {
    root: &'r Path,
    imports: std::cell::RefCell<HashMap<String, Vec<String>>>,
}

impl Checker<'_> {
    fn imports_mathlib(&self, module: &str) -> bool {
        let mut seen: HashSet<String> = HashSet::new();
        let mut pending = vec![module.to_owned()];
        while let Some(current) = pending.pop() {
            if !seen.insert(current.clone()) {
                continue;
            }
            if current == "Mathlib" || current.starts_with("Mathlib.") {
                return true;
            }
            let path = module_path(self.root, &current);
            if !current.starts_with("TruthCore") || !path.is_file() {
                continue;
            }
            let mut cache = self.imports.borrow_mut();
            let next = cache.entry(current).or_insert_with(|| {
                lean_imports(&fs::read_to_string(&path).unwrap_or_default())
                    .into_iter()
                    .map(str::to_owned)
                    .collect()
            });
            pending.extend(next.iter().cloned());
        }
        false
    }

    fn permitted_axioms_error(&self, config: &Obj) -> Option<String> {
        let axioms = config.get("permitted_axioms");
        if axioms.and_then(Value::as_array).is_some_and(Vec::is_empty) {
            return None;
        }
        let mut listed: Option<Vec<&str>> = axioms
            .and_then(Value::as_array)
            .and_then(|items| items.iter().map(Value::as_str).collect());
        let mut expected = MATHLIB_PERMITTED_AXIOMS.to_vec();
        expected.sort();
        if let Some(listed) = listed.as_mut() {
            listed.sort();
        }
        if listed.as_deref() != Some(expected.as_slice()) {
            return Some(format!(
                "permitted_axioms must be [] or exactly {} (docs/axiom-policy.md)",
                str_list_repr(MATHLIB_PERMITTED_AXIOMS)
            ));
        }
        if !self.imports_mathlib(text(config, "solution_module")) {
            return Some(format!(
                "only a Solution that imports Mathlib may permit {}; results without Mathlib stay zero-axiom",
                str_list_repr(MATHLIB_PERMITTED_AXIOMS)
            ));
        }
        None
    }

    /// Python `validate_result_config`.
    fn result_config(
        &self,
        path: &str,
        result: &Obj,
        argument_ids: &HashMap<String, usize>,
    ) -> Res<Obj> {
        require(
            result,
            &[
                "id",
                "argument_id",
                "challenge_module",
                "solution_module",
                "theorem",
                "comparator_config",
                "status",
            ],
            path,
        )?;
        let argument_id = result.get("argument_id");
        if !argument_id
            .and_then(Value::as_str)
            .is_some_and(|id| argument_ids.contains_key(id))
        {
            return Err(format!(
                "{path}: unknown argument_id {}",
                py_str(argument_id)
            ));
        }
        validate_result_transcription(path, result)?;
        let challenge = module_path(self.root, text(result, "challenge_module"));
        let solution = module_path(self.root, text(result, "solution_module"));
        let canonical = format!("results/{}/comparator.json", py_str(result.get("id")));
        if string(result, "comparator_config") != Some(canonical.as_str()) {
            return Err(format!(
                "{path}: Comparator path must match executable gate: {canonical}"
            ));
        }
        let config_path = self.root.join(&canonical);
        for expected in [&challenge, &solution, &config_path] {
            if !expected.is_file() {
                return Err(format!(
                    "{path}: referenced file does not exist: {}",
                    relative(self.root, expected)
                ));
            }
        }
        let config: Value =
            serde_json::from_str(&fs::read_to_string(&config_path).unwrap_or_default())
                .map_err(|error| format!("{canonical}: invalid Comparator JSON: {error}"))?;
        let empty = Obj::new();
        let config_object = config.as_object().unwrap_or(&empty);
        if config_object.get("challenge_module") != result.get("challenge_module") {
            return Err(format!(
                "{canonical}: challenge module disagrees with result record"
            ));
        }
        if config_object.get("solution_module") != result.get("solution_module") {
            return Err(format!(
                "{canonical}: solution module disagrees with result record"
            ));
        }
        if !strings(config_object, "theorem_names").contains(&text(result, "theorem")) {
            return Err(format!(
                "{canonical}: theorem is not listed in theorem_names"
            ));
        }
        if let Some(error) = self.permitted_axioms_error(config_object) {
            return Err(format!("{canonical}: {error}"));
        }
        if config_object.get("enable_nanoda") != Some(&Value::Bool(true)) {
            return Err(format!("{canonical}: NanoDa must be enabled"));
        }
        Ok(config_object.clone())
    }
}

fn validate_result_transcription(label: &str, result: &Obj) -> Res<()> {
    match result.get("transcription") {
        None | Some(Value::Null) => {
            let description = text(result, "description");
            let rest = ["Opaque-atom ", "Near-", "Logical "]
                .into_iter()
                .find_map(|prefix| description.strip_prefix(prefix))
                .filter(|rest| {
                    rest.starts_with("transcription") || rest.starts_with("Transcription")
                })
                .unwrap_or(description);
            let labelled = (rest.starts_with("transcription") || rest.starts_with("Transcription"))
                && !rest["transcription".len()..]
                    .chars()
                    .next()
                    .is_some_and(is_word);
            if labelled {
                return Err(format!(
                    "{label}: description labels the result a transcription; declare it in the structured transcription field (#391)"
                ));
            }
        }
        Some(Value::String(kind)) if TRANSCRIPTION_KINDS.contains(&kind.as_str()) => {}
        Some(_) => {
            return Err(format!(
                "{label}: transcription must be one of {}",
                TRANSCRIPTION_KINDS.join(", ")
            ));
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Record rules

fn validate_model(model: &Obj, statements: &HashMap<&str, &Obj>, root: &Path) -> Res<()> {
    if !string(model, "id").is_some_and(|id| upper_id(id, "MODEL-")) {
        return Err("model id must be MODEL-…".into());
    }
    for key in ["description", "vocabulary", "lean_declaration"] {
        if !string(model, key).is_some_and(|value| !value.is_empty()) {
            return Err(format!("missing {key}"));
        }
    }
    if !lean_name(model.get("lean_declaration")) {
        return Err("invalid model Lean declaration".into());
    }
    let modules = model.get("modules").and_then(Value::as_array);
    let unique = |items: &Vec<Value>| distinct(items);
    if !modules.is_some_and(|modules| {
        !modules.is_empty() && modules.iter().all(|m| lean_name(Some(m))) && unique(modules)
    }) {
        return Err("modules must be a nonempty unique list".into());
    }
    for module in modules.into_iter().flatten().filter_map(Value::as_str) {
        if !module_path(root, module).is_file() {
            return Err(format!("unknown module {module}"));
        }
    }
    let bindings = model.get("bindings").and_then(Value::as_object);
    if !bindings.is_some_and(|bindings| {
        !bindings.is_empty()
            && bindings.iter().all(|(key, value)| {
                lean_name(Some(&Value::String(key.clone())))
                    && value.as_str().is_some_and(lean_term)
            })
    }) {
        return Err("bindings must name nonempty Lean terms".into());
    }
    let bindings = bindings.expect("checked");
    let carriers = model.get("carriers").and_then(Value::as_array);
    if !carriers.is_some_and(|carriers| !carriers.is_empty()) {
        return Err("carriers must be nonempty".into());
    }
    for carrier in carriers.into_iter().flatten() {
        let carrier = carrier.as_object();
        if !carrier.is_some_and(|carrier| {
            string(carrier, "binding").is_some_and(|binding| bindings.contains_key(binding))
                && lean_name(carrier.get("theorem"))
        }) {
            return Err("carrier needs a binding and enumeration theorem".into());
        }
        let elements = carrier
            .and_then(|c| c.get("elements"))
            .and_then(Value::as_array);
        if !elements.is_some_and(|elements| {
            !elements.is_empty() && elements.iter().all(|e| lean_name(Some(e))) && unique(elements)
        }) {
            return Err("carrier elements must be nonempty unique Lean terms".into());
        }
    }
    let evaluations = model.get("evaluations").and_then(Value::as_array);
    if !evaluations.is_some_and(|evaluations| !evaluations.is_empty()) {
        return Err("evaluations must be nonempty".into());
    }
    let mut seen = HashSet::new();
    for evaluation in evaluations.into_iter().flatten() {
        let evaluation = evaluation
            .as_object()
            .ok_or_else(|| "evaluation must be an object".to_owned())?;
        let sid = evaluation.get("statement_id");
        let known = sid.and_then(Value::as_str).filter(|sid| {
            statements
                .get(sid)
                .is_some_and(|statement| lean_name(statement.get("lean_declaration")))
        });
        let Some(sid) = known else {
            return Err(format!("unknown or unbound statement {}", py_str(sid)));
        };
        if !seen.insert(sid) {
            return Err(format!("duplicate/conflicting evaluation {sid}"));
        }
        if !matches!(string(evaluation, "value"), Some("satisfies" | "violates"))
            || !lean_name(evaluation.get("theorem"))
        {
            return Err("evaluation needs satisfies/violates and a theorem declaration".into());
        }
        if !evaluation
            .get("arguments")
            .and_then(Value::as_array)
            .is_some_and(|args| {
                args.iter()
                    .all(|arg| arg.as_str().is_some_and(|arg| bindings.contains_key(arg)))
            })
        {
            return Err(format!(
                "evaluation {sid} arguments must reference registered bindings"
            ));
        }
    }
    Ok(())
}

/// configurations `TYPE`: names, application and arrows only.
fn profile_type(text: &str) -> bool {
    if text.is_empty() {
        return false;
    }
    let mut previous_name = false;
    for c in text.chars() {
        let name = c.is_ascii_alphanumeric() || c == '_' || c == '.';
        if name && !previous_name && !(c.is_ascii_alphabetic() || c == '_') {
            return false;
        }
        if !name && c != '→' && !c.is_whitespace() {
            return false;
        }
        previous_name = name;
    }
    true
}

struct CaseContext<'a> {
    statements: &'a HashMap<&'a str, &'a Obj>,
    results: &'a HashMap<&'a str, &'a Obj>,
    arguments: &'a HashMap<&'a str, &'a Obj>,
    models: &'a BTreeMap<&'a str, &'a Obj>,
    root: &'a Path,
}

fn validate_case(case: &Obj, cx: &CaseContext) -> Res<()> {
    const ALLOWED: &[&str] = &[
        "id",
        "description",
        "seed_statement_id",
        "semantics",
        "configurations",
        "incompatibility_result_ids",
        "implication_result_ids",
        "model_bindings",
    ];
    if case.keys().any(|key| !ALLOWED.contains(&key.as_str())) {
        return Err("unknown configuration fields (derived statuses may not be stored)".into());
    }
    if !string(case, "id").is_some_and(|id| upper_id(id, "CONFIG-")) {
        return Err("configuration case needs a CONFIG- identifier".into());
    }
    if !string(case, "seed_statement_id").is_some_and(|sid| cx.statements.contains_key(sid)) {
        return Err("unknown configuration seed".into());
    }
    let profile = case
        .get("semantics")
        .and_then(Value::as_object)
        .ok_or_else(|| "semantics must be an explicit object".to_owned())?;
    const PROFILE: &[&str] = &[
        "id",
        "logic",
        "frame",
        "domain",
        "identity",
        "vocabulary",
        "parameters",
        "parameter_order",
        "constants",
        "applications",
        "modules",
        "permitted_axioms",
    ];
    if profile.keys().any(|key| !PROFILE.contains(&key.as_str())) {
        return Err("unknown semantics fields".into());
    }
    for field in ["id", "logic", "frame", "domain", "identity", "vocabulary"] {
        if !string(profile, field).is_some_and(|value| !value.trim().is_empty()) {
            return Err(format!("semantics requires {field}"));
        }
    }
    let axioms = profile.get("permitted_axioms").and_then(Value::as_array);
    if !axioms.is_some_and(|axioms| {
        axioms.iter().all(|axiom| {
            axiom
                .as_str()
                .is_some_and(|axiom| MATHLIB_PERMITTED_AXIOMS.contains(&axiom))
        }) && distinct(axioms)
    }) {
        return Err(
            "profile requires explicit permitted_axioms from the approved axiom policy".into(),
        );
    }
    let parameters = profile
        .get("parameters")
        .and_then(Value::as_array)
        .filter(|parameters| !parameters.is_empty())
        .ok_or_else(|| "semantics requires ordered Lean parameters".to_owned())?;
    let mut names: Vec<String> = Vec::new();
    for parameter in parameters {
        let parameter = parameter.as_object();
        let Some(name) = parameter
            .and_then(|p| string(p, "name"))
            .filter(|name| is_ident(name))
        else {
            return Err("invalid parameter name".into());
        };
        if !parameter
            .and_then(|p| string(p, "type"))
            .is_some_and(profile_type)
        {
            return Err(
                "invalid parameter type (only names, application and arrows accepted)".into(),
            );
        }
        names.push(name.to_owned());
    }
    if names.iter().collect::<HashSet<_>>().len() != names.len() {
        return Err("duplicate profile parameter".into());
    }
    let empty = Obj::new();
    let constants = match profile.get("constants") {
        None => Some(&empty),
        Some(value) => value.as_object(),
    };
    let Some(constants) = constants.filter(|constants| {
        constants.iter().all(|(name, term)| {
            is_ident(name) && !names.contains(name) && term.as_str().is_some_and(lean_term)
        })
    }) else {
        return Err("invalid/overlapping fixed profile constants".into());
    };
    names.extend(constants.keys().cloned());
    let order_ok = match profile.get("parameter_order") {
        None => true,
        Some(order) => order.as_array().is_some_and(|order| {
            let items: Option<Vec<&str>> = order.iter().map(Value::as_str).collect();
            items.is_some_and(|items| {
                let set: HashSet<&str> = items.iter().copied().collect();
                set.len() == items.len()
                    && set == names.iter().map(String::as_str).collect::<HashSet<_>>()
            })
        }),
    };
    if !order_ok {
        return Err("parameter_order must list every variable and fixed role exactly once".into());
    }
    if constants
        .values()
        .any(|term| !matches!(term.as_str(), Some("Bool" | "Nat")))
    {
        return Err(
            "supported fixed carriers are Bool or Nat; proposition-valued carriers are forbidden"
                .into(),
        );
    }
    let mut carriers: HashSet<String> = constants
        .values()
        .filter_map(Value::as_str)
        .map(str::to_owned)
        .collect();
    for parameter in parameters.iter().filter_map(Value::as_object) {
        let kind = text(parameter, "type")
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ");
        let words: Vec<&str> = kind.split(" → ").collect();
        let tokens: Vec<&str> = kind.split(' ').collect();
        let name = text(parameter, "name");
        if kind == "Type" {
            carriers.insert(name.to_owned());
            continue;
        }
        let frame = kind.starts_with("TruthCore.Modal.Frame ")
            && carriers.contains(kind.split_once(' ').map_or("", |(_, rest)| rest));
        let data = tokens.len() == 3
            && DATA_STRUCTURES.contains(&tokens[0])
            && tokens[1..].iter().all(|arg| carriers.contains(*arg));
        let function = words.len() >= 2
            && (carriers.contains(words[words.len() - 1]) || words[words.len() - 1] == "Prop")
            && words[..words.len() - 1]
                .iter()
                .all(|word| carriers.contains(*word));
        if !(frame || data || carriers.contains(&kind) || function) {
            return Err(format!(
                "{name}: unsupported semantic role type; proof-valued parameters are forbidden"
            ));
        }
    }
    let applications = profile
        .get("applications")
        .and_then(Value::as_object)
        .filter(|applications| !applications.is_empty())
        .ok_or_else(|| "profile requires explicit statement applications".to_owned())?;
    for (sid, args) in applications {
        if !cx
            .statements
            .get(sid.as_str())
            .is_some_and(|statement| lean_name(statement.get("lean_declaration")))
        {
            return Err(format!("unknown/unbound statement {sid}"));
        }
        if !args.as_array().is_some_and(|args| {
            args.iter().all(|arg| {
                arg.as_str()
                    .is_some_and(|arg| names.iter().any(|n| n == arg))
            })
        }) {
            return Err(format!(
                "{sid}: arguments must reference profile parameters"
            ));
        }
    }
    let selections = case
        .get("configurations")
        .and_then(Value::as_array)
        .filter(|selections| !selections.is_empty())
        .ok_or_else(|| "case requires named configurations".to_owned())?;
    let mut seen: HashSet<&str> = HashSet::new();
    for selection in selections {
        let selection = selection.as_object();
        let id = selection.and_then(|s| string(s, "id")).filter(|id| {
            let mut chars = id.chars();
            chars.next().is_some_and(|c| c.is_ascii_lowercase())
                && chars.all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-')
        });
        let Some(id) = id.filter(|id| !seen.contains(id)) else {
            return Err("invalid/duplicate selection id".into());
        };
        seen.insert(id);
        let selection = selection.expect("checked");
        let mut keys: Vec<&str> = selection.keys().map(String::as_str).collect();
        keys.sort();
        if keys != ["id", "statement_ids"] {
            return Err("selection stores only its id and statement set".into());
        }
        if !selection
            .get("statement_ids")
            .and_then(Value::as_array)
            .is_some_and(|ids| {
                ids.iter().all(|sid| {
                    sid.as_str()
                        .is_some_and(|sid| applications.contains_key(sid))
                }) && distinct(ids)
            })
        {
            return Err("selection needs unique profile statement IDs".into());
        }
    }
    let field_ids = |field: &str| -> Vec<&str> { strings(case, field) };
    for field in ["incompatibility_result_ids", "implication_result_ids"] {
        let valid = match case.get(field) {
            None => true,
            Some(ids) => ids.as_array().is_some_and(|ids| {
                ids.iter()
                    .all(|rid| rid.as_str().is_some_and(|rid| cx.results.contains_key(rid)))
                    && distinct(ids)
            }),
        };
        if !valid {
            return Err(format!("{field} must reference unique existing results"));
        }
        for rid in field_ids(field) {
            let result = cx.results[rid];
            if ["theorem", "solution_module"]
                .iter()
                .any(|key| !lean_name(result.get(*key)))
            {
                return Err(format!("{rid}: invalid result declarations"));
            }
            if field == "implication_result_ids" && truthy(result.get("transcription")) {
                return Err(format!(
                    "{rid}: transcription cannot supply a configuration deduction"
                ));
            }
            let argument = cx.arguments.get(text(result, "argument_id"));
            let Some(argument) = argument.filter(|argument| {
                strings(argument, "premise_statement_ids")
                    .iter()
                    .all(|sid| applications.contains_key(*sid))
            }) else {
                return Err(format!("{rid}: all premises require profile applications"));
            };
            let conclusion = text(argument, "conclusion_statement_id");
            if field == "implication_result_ids"
                && cx
                    .statements
                    .get(conclusion)
                    .and_then(|statement| string(statement, "lean_declaration"))
                    == Some("TruthCore.Logic.ConfigurationFalse")
            {
                return Err(format!(
                    "{rid}: False-concluding results belong in incompatibility_result_ids, not implication rules"
                ));
            }
            if field == "implication_result_ids" && !applications.contains_key(conclusion) {
                return Err(format!("{rid}: conclusion requires profile application"));
            }
        }
    }
    let incompatibility: HashSet<&str> = field_ids("incompatibility_result_ids")
        .into_iter()
        .collect();
    if field_ids("implication_result_ids")
        .iter()
        .any(|rid| incompatibility.contains(rid))
    {
        return Err("a contradiction certificate cannot also be an implication rule".into());
    }
    let witnesses = match case.get("model_bindings") {
        None => Vec::new(),
        Some(Value::Array(items)) => items.iter().collect(),
        Some(_) => return Err("model_bindings must be a list".into()),
    };
    let vocabulary = text(profile, "vocabulary");
    let mut seen: HashSet<&str> = HashSet::new();
    for witness in witnesses {
        let mid = witness.as_object().and_then(|w| string(w, "model_id"));
        let Some(mid) = mid.filter(|mid| cx.models.contains_key(mid) && !seen.contains(mid)) else {
            return Err("unknown/duplicate configuration model".into());
        };
        seen.insert(mid);
        let model = cx.models[mid];
        if text(model, "vocabulary") != vocabulary {
            return Err(format!("{mid}: vocabulary/profile mismatch"));
        }
        let model_bindings = model.get("bindings").and_then(Value::as_object);
        let parameters = witness
            .as_object()
            .and_then(|w| w.get("parameters"))
            .and_then(Value::as_object)
            .filter(|bindings| {
                bindings.keys().collect::<HashSet<_>>() == names.iter().collect::<HashSet<_>>()
                    && bindings.values().all(|key| {
                        key.as_str().is_some_and(|key| {
                            model_bindings.is_some_and(|mb| mb.contains_key(key))
                        })
                    })
            })
            .ok_or_else(|| {
                format!("{mid}: complete profile-to-model parameter binding required")
            })?;
        for evaluation in model
            .get("evaluations")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .filter_map(Value::as_object)
        {
            let sid = text(evaluation, "statement_id");
            if let Some(args) = applications.get(sid).and_then(Value::as_array) {
                let expected: Vec<&Value> = args
                    .iter()
                    .filter_map(|arg| arg.as_str().and_then(|arg| parameters.get(arg)))
                    .collect();
                let actual: Vec<&Value> = evaluation
                    .get("arguments")
                    .and_then(Value::as_array)
                    .map(|items| items.iter().collect())
                    .unwrap_or_default();
                if actual != expected {
                    return Err(format!(
                        "{mid}/{sid}: evaluation does not use the same profile assignment"
                    ));
                }
            }
        }
    }
    let mut omitted: Vec<&str> = cx
        .models
        .iter()
        .filter(|(mid, model)| text(model, "vocabulary") == vocabulary && !seen.contains(*mid))
        .map(|(mid, _)| *mid)
        .collect();
    omitted.sort();
    if !omitted.is_empty() {
        return Err(format!(
            "profile omits registered models in its vocabulary: {}",
            str_list_repr(&omitted)
        ));
    }
    let modules = profile.get("modules").and_then(Value::as_array);
    if !modules.is_some_and(|modules| {
        !modules.is_empty()
            && distinct(modules)
            && modules.iter().all(|m| {
                lean_name(Some(m))
                    && m.as_str()
                        .is_some_and(|m| module_path(cx.root, m).is_file())
            })
    }) {
        return Err("semantics modules must name existing unique Lean modules".into());
    }
    Ok(())
}

fn validate_attempt(
    attempt: &Obj,
    statements: &HashSet<&str>,
    evidence: &HashSet<&str>,
) -> Res<()> {
    if !string(attempt, "id").is_some_and(|id| upper_id(id, "ATTEMPT-")) {
        return Err("id must be an ATTEMPT- identifier".into());
    }
    let ids = attempt.get("statement_ids").and_then(Value::as_array);
    if !ids.is_some_and(|ids| {
        !ids.is_empty()
            && ids
                .iter()
                .all(|sid| sid.as_str().is_some_and(|sid| statements.contains(sid)))
    }) {
        return Err("statement_ids must be a non-empty list of known statements".into());
    }
    let ids = ids.expect("checked");
    if !distinct(ids) {
        return Err("statement_ids must not contain duplicates".into());
    }
    if !string(attempt, "date").is_some_and(iso_date) {
        return Err("date must be an ISO calendar date (YYYY-MM-DD)".into());
    }
    if !string(attempt, "kind").is_some_and(|kind| ATTEMPT_KINDS.contains(&kind)) {
        return Err(format!("kind must be one of {}", ATTEMPT_KINDS.join(", ")));
    }
    if !string(attempt, "outcome").is_some_and(|outcome| ATTEMPT_OUTCOMES.contains(&outcome)) {
        return Err(format!(
            "outcome must be one of {}",
            ATTEMPT_OUTCOMES.join(", ")
        ));
    }
    if !string(attempt, "summary").is_some_and(|summary| !summary.trim().is_empty()) {
        return Err("summary must be a non-empty string".into());
    }
    let pr = |reference: &str| {
        reference.strip_prefix("PR-").is_some_and(|number| {
            number.starts_with(|c: char| ('1'..='9').contains(&c))
                && number.chars().all(|c| c.is_ascii_digit())
        })
    };
    let references = attempt.get("evidence").and_then(Value::as_array);
    if !references.is_some_and(|references| {
        references.iter().all(|reference| {
            reference
                .as_str()
                .is_some_and(|reference| evidence.contains(reference) || pr(reference))
        })
    }) {
        return Err(
            "evidence must list known result/claim IDs or PR-<positive number> references".into(),
        );
    }
    let references = references.expect("checked");
    if !distinct(references) {
        return Err("evidence must not contain duplicates".into());
    }
    let blocker = get(attempt, "blocker");
    if blocker.is_some_and(|blocker| !blocker.as_str().is_some_and(|b| !b.trim().is_empty())) {
        return Err("blocker must be a non-empty string when present".into());
    }
    if string(attempt, "outcome") == Some("blocked") && blocker.is_none() {
        return Err("blocked attempts require a blocker".into());
    }
    Ok(())
}

fn validate_prose_ids(path: &str, record: &Obj, fields: &[&str], known: &HashSet<&str>) -> Res<()> {
    for field in fields {
        let prose = match record.get(*field) {
            None => String::new(),
            value => py_str(value),
        };
        for cited in prose_ids(&prose) {
            if !known.contains(cited) {
                return Err(format!("{path}: {field} cites unknown id {cited}"));
            }
        }
    }
    Ok(())
}

fn validate_term_links<'a>(
    path: &str,
    record: &'a Obj,
    definitions: &HashSet<&str>,
    disambiguations: &HashSet<&str>,
) -> Res<Vec<&'a str>> {
    let mut linked = Vec::new();
    for (field, known, kind) in [
        ("definition_ids", definitions, "definition"),
        ("disambiguation_ids", disambiguations, "disambiguation"),
    ] {
        if !record.contains_key(field) {
            continue;
        }
        let ids = require_string_list(record, field, path, false)?;
        for id in &ids {
            if !known.contains(id) {
                return Err(format!("{path}: unknown {kind} id {id}"));
            }
        }
        if field == "definition_ids" {
            linked = ids;
        }
    }
    Ok(linked)
}

fn validate_owner_approval(where_: &str, marking: &Obj) -> Res<()> {
    let Some(approval) = get(marking, "owner_approval") else {
        return Ok(());
    };
    let Some(approval) = approval.as_object().filter(|approval| {
        approval.len() == 2 && approval.contains_key("decision") && approval.contains_key("date")
    }) else {
        return Err(format!(
            "{where_}: self_evident owner_approval must be an object with exactly decision and date"
        ));
    };
    let url = |text: &str| {
        let Some(rest) =
            dollar(text).strip_prefix("https://github.com/moritzbrantner/truth-core/issues/")
        else {
            return false;
        };
        let Some((issue, comment)) = rest.split_once("#issuecomment-") else {
            return false;
        };
        !issue.is_empty()
            && !comment.is_empty()
            && issue.chars().all(|c| c.is_ascii_digit())
            && comment.chars().all(|c| c.is_ascii_digit())
    };
    if !string(approval, "decision").is_some_and(url) {
        return Err(format!(
            "{where_}: self_evident owner_approval decision must link the owner's issue comment"
        ));
    }
    let date = |text: &str| {
        let parts: Vec<&str> = dollar(text).split('-').collect();
        matches!(parts.as_slice(), [y, m, d] if digits(y, 4) && digits(m, 2) && digits(d, 2))
    };
    if !string(approval, "date").is_some_and(date) {
        return Err(format!(
            "{where_}: self_evident owner_approval date must be YYYY-MM-DD"
        ));
    }
    if get(marking, "disagreement").is_none() {
        return Err(format!(
            "{where_}: an owner-approved marking needs a disagreement record (#378, #1007)"
        ));
    }
    Ok(())
}

fn validate_disagreement(
    where_: &str,
    marking: &Obj,
    basis: &str,
    claim_ids: &HashSet<&str>,
    statement_ids: &HashSet<&str>,
) -> Res<()> {
    let Some(disagreement) = get(marking, "disagreement") else {
        if basis == "common_ground" {
            return Ok(());
        }
        return Err(format!(
            "{where_}: self_evident needs a disagreement record (#378): \"{DISAGREEMENT_NONE}\" or {{\"rival_statement_ids\": [...], \"claim_ids\": [...]}}"
        ));
    };
    if disagreement.as_str() == Some(DISAGREEMENT_NONE) {
        return Ok(());
    }
    let Some(object) = disagreement.as_object().filter(|object| {
        object
            .keys()
            .all(|key| matches!(key.as_str(), "rival_statement_ids" | "claim_ids" | "note"))
    }) else {
        return Err(format!(
            "{where_}: self_evident disagreement must be \"{DISAGREEMENT_NONE}\" or an object"
        ));
    };
    let empty = Value::Array(Vec::new());
    let rivals = object.get("rival_statement_ids").unwrap_or(&empty);
    let claims = object.get("claim_ids").unwrap_or(&empty);
    for (field, values, known) in [
        ("rival_statement_ids", rivals, statement_ids),
        ("claim_ids", claims, claim_ids),
    ] {
        let Some(values) = values
            .as_array()
            .and_then(|items| items.iter().map(Value::as_str).collect::<Option<Vec<_>>>())
        else {
            return Err(format!(
                "{where_}: self_evident disagreement {field} must be a list of ids"
            ));
        };
        let unknown: Vec<&str> = values.into_iter().filter(|v| !known.contains(v)).collect();
        if !unknown.is_empty() {
            return Err(format!(
                "{where_}: self_evident disagreement {field} unknown: {}",
                unknown.join(", ")
            ));
        }
    }
    if !truthy(Some(rivals)) && !truthy(Some(claims)) {
        return Err(format!(
            "{where_}: an object disagreement lists rivals or claims; otherwise use \"{DISAGREEMENT_NONE}\""
        ));
    }
    Ok(())
}

fn validate_self_evident(
    path: &str,
    statement: &Obj,
    claim_ids: &HashSet<&str>,
    result_ids: &HashSet<&str>,
    statement_ids: &HashSet<&str>,
) -> Res<()> {
    let Some(marking) = get(statement, "self_evident") else {
        return Ok(());
    };
    let where_ = path;
    let marking = marking.as_object().ok_or_else(|| {
        format!("{where_}: self_evident must be an object with justification_ids")
    })?;
    let justification = require_string_list(marking, "justification_ids", path, false)?;
    for id in &justification {
        if !claim_ids.contains(id) && !result_ids.contains(id) {
            return Err(format!(
                "{where_}: self_evident justification {id} is neither a claim id nor a result id"
            ));
        }
    }
    let Some(basis) = get(marking, "basis") else {
        if !string(statement, "id").is_some_and(|id| LEGACY_FLOOR_STATEMENTS.contains(&id)) {
            return Err(format!(
                "{where_}: self_evident needs a basis ({}); only the documented legacy markings may omit it",
                FLOOR_BASES.join(", ")
            ));
        }
        return validate_disagreement(where_, marking, "legacy", claim_ids, statement_ids);
    };
    let Some(basis) = basis.as_str().filter(|basis| FLOOR_BASES.contains(basis)) else {
        return Err(format!(
            "{where_}: self_evident basis must be one of {}",
            FLOOR_BASES.join(", ")
        ));
    };
    validate_disagreement(where_, marking, basis, claim_ids, statement_ids)?;
    validate_owner_approval(where_, marking)?;
    let known_statement = |field: &str, value: Option<&Value>| -> Res<()> {
        let Some(value) = value.and_then(Value::as_str).filter(|v| !v.is_empty()) else {
            return Err(format!(
                "{where_}: self_evident {field} must be a statement id"
            ));
        };
        if !statement_ids.contains(value) {
            return Err(format!(
                "{where_}: self_evident {field} {value} is not a known statement"
            ));
        }
        Ok(())
    };
    if get(marking, "owner_approval").is_some() {
        for field in ["denial_statement_id", "question_statement_id"] {
            if marking.contains_key(field) {
                known_statement(field, marking.get(field))?;
            }
        }
        for rival in marking
            .get("sceptical_rival_ids")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            known_statement("sceptical_rival_ids entry", Some(rival))?;
        }
        if let Some(positions) = marking.get("positions") {
            let positions = positions
                .as_array()
                .filter(|positions| !positions.is_empty())
                .ok_or_else(|| {
                    format!(
                        "{where_}: self_evident positions, when given, must be a non-empty list"
                    )
                })?;
            for position in positions {
                let position = position
                    .as_object()
                    .ok_or_else(|| format!("{where_}: each common_ground position is an object"))?;
                known_statement("position statement_id", position.get("statement_id"))?;
                for claim in require_string_list(position, "claim_ids", path, false)? {
                    if !claim_ids.contains(claim) {
                        return Err(format!(
                            "{where_}: self_evident position claim {claim} is not a known claim"
                        ));
                    }
                }
            }
        }
        return Ok(());
    }
    match basis {
        "retorsion" => {
            if justification.iter().any(|id| !result_ids.contains(id)) {
                return Err(format!(
                    "{where_}: a retorsion basis is justified by results only"
                ));
            }
            known_statement("denial_statement_id", marking.get("denial_statement_id"))?;
        }
        "common_ground" => {
            known_statement(
                "question_statement_id",
                marking.get("question_statement_id"),
            )?;
            let positions = marking
                .get("positions")
                .and_then(Value::as_array)
                .filter(|positions| !positions.is_empty())
                .ok_or_else(|| {
                    format!("{where_}: a common_ground basis needs a non-empty positions list")
                })?;
            let mut cited: HashSet<&str> = HashSet::new();
            for position in positions {
                let position = position
                    .as_object()
                    .ok_or_else(|| format!("{where_}: each common_ground position is an object"))?;
                known_statement("position statement_id", position.get("statement_id"))?;
                cited.extend(require_string_list(position, "claim_ids", path, false)?);
            }
            if cited != justification.iter().copied().collect() {
                return Err(format!(
                    "{where_}: common_ground justification_ids must be exactly the claims its positions cite"
                ));
            }
        }
        _ => {
            if !justification.iter().any(|id| claim_ids.contains(id)) {
                return Err(format!(
                    "{where_}: an observation basis needs a sourced claim among its justifications"
                ));
            }
            if marking.contains_key("sceptical_rival_ids") {
                for rival in require_string_list(marking, "sceptical_rival_ids", path, true)? {
                    known_statement(
                        "sceptical_rival_ids entry",
                        Some(&Value::String(rival.into())),
                    )?;
                }
            }
        }
    }
    Ok(())
}

fn validate_settlement_actions(statement: &Obj) -> Res<()> {
    let actions = match statement.get("settlement_actions") {
        None => return Ok(()),
        Some(Value::Array(actions)) => actions,
        Some(_) => return Err("settlement_actions must be a list".into()),
    };
    for action in actions {
        let action = action
            .as_object()
            .filter(|action| matches!(string(action, "kind"), Some("floor" | "definition")))
            .ok_or_else(|| "settlement action must have kind floor or definition".to_owned())?;
        if !matches!(
            string(action, "status"),
            Some("needs-owner-decision" | "approved")
        ) || !string(action, "description").is_some_and(|d| !d.is_empty())
        {
            return Err(
                "settlement action needs a description and status needs-owner-decision or approved"
                    .into(),
            );
        }
        if string(action, "status") == Some("approved")
            && !py_str(Some(
                action
                    .get("decision")
                    .unwrap_or(&Value::String(String::new())),
            ))
            .starts_with("https://github.com/moritzbrantner/truth-core/")
        {
            return Err("approved settlement action needs a repository owner decision URL".into());
        }
    }
    Ok(())
}

fn validate_case_split(
    result: &Obj,
    statements: &HashSet<&str>,
    results: &HashSet<&str>,
) -> Res<()> {
    if result
        .get("joint_settlement_schema")
        .is_some_and(|value| !value.is_boolean())
    {
        return Err("joint_settlement_schema must be boolean navigation metadata".into());
    }
    let Some(split) = get(result, "case_split") else {
        return Ok(());
    };
    let known = |set: &HashSet<&str>, value: Option<&Value>| {
        value
            .and_then(Value::as_str)
            .is_some_and(|v| set.contains(v))
    };
    let Some(split) = split
        .as_object()
        .filter(|split| known(statements, split.get("target_statement_id")))
    else {
        return Err("case_split needs a known target_statement_id".into());
    };
    if let Some(survival) = get(split, "survival_result_id")
        && !known(results, Some(survival))
    {
        return Err("case_split survival_result_id must name a known result".into());
    }
    let cases = split
        .get("cases")
        .and_then(Value::as_array)
        .filter(|cases| !cases.is_empty())
        .ok_or_else(|| "case_split needs nonempty cases".to_owned())?;
    let mut declarations = HashSet::new();
    let mut count = 0;
    for case in cases {
        let Some(case) = case
            .as_object()
            .filter(|case| string(case, "label").is_some_and(|l| !l.is_empty()))
        else {
            return Err("case_split case needs a label".into());
        };
        let Some(declaration) =
            string(case, "lean_declaration").filter(|d| d.starts_with("TruthCore."))
        else {
            return Err("case_split case needs a TruthCore lean_declaration".into());
        };
        declarations.insert(declaration);
        count += 1;
        if let Some(statement) = get(case, "statement_id")
            && !known(statements, Some(statement))
        {
            return Err("case_split case statement_id must name a known statement".into());
        }
    }
    if declarations.len() != count {
        return Err("case_split case declarations must be distinct".into());
    }
    Ok(())
}

fn validate_argument_derivation(
    path: &str,
    argument: &Obj,
    inferences: &HashMap<&str, &Obj>,
) -> Res<()> {
    let mut available: HashSet<&str> = strings(argument, "premise_statement_ids")
        .into_iter()
        .chain(strings(argument, "commitment_statement_ids"))
        .collect();
    let mut remaining: BTreeMap<&str, &Obj> = strings(argument, "inference_ids")
        .into_iter()
        .map(|id| (id, inferences[id]))
        .collect();
    while !remaining.is_empty() {
        let ready: Vec<&str> = remaining
            .iter()
            .filter(|(_, inference)| {
                let scoped = strings(inference, "assumption_statement_ids");
                strings(inference, "input_statement_ids")
                    .iter()
                    .all(|input| available.contains(input) || scoped.contains(input))
            })
            .map(|(id, _)| *id)
            .collect();
        if ready.is_empty() {
            let blocked: Vec<&str> = remaining.keys().copied().collect();
            return Err(format!(
                "{path}: inference applications are not grounded in advertised premises: {}",
                blocked.join(", ")
            ));
        }
        for id in ready {
            available.insert(text(remaining[id], "output_statement_id"));
            remaining.remove(id);
        }
    }
    if !available.contains(text(argument, "conclusion_statement_id")) {
        return Err(format!(
            "{path}: conclusion is not derivable from the listed inference applications"
        ));
    }
    Ok(())
}

fn validate_premise_program_relation(path: &str, relation: &Obj) -> Res<()> {
    let expected: Option<(&[&str], &str)> = match text(relation, "predicate") {
        "alternative_to" | "instance_of_schema" | "strengthens" => {
            Some((&["statement"], "statement"))
        }
        "refutes" | "root_route" => Some((&["argument"], "statement")),
        "attacks" => Some((&["argument", "claim", "statement"], "statement")),
        "supports" => Some((&["claim"], "statement")),
        _ => None,
    };
    let Some((subjects, object)) = expected else {
        return Ok(());
    };
    if !subjects.contains(&text(relation, "subject_kind"))
        || text(relation, "object_kind") != object
    {
        return Err(format!(
            "{path}: {} relates {} to {object}",
            text(relation, "predicate"),
            subjects.join("/")
        ));
    }
    Ok(())
}

fn validate_strength_comparison(
    relation: &Obj,
    statements: &HashMap<&str, &Obj>,
    results: &HashMap<&str, &Obj>,
    arguments: &HashMap<&str, &Obj>,
    configs: &HashMap<String, Obj>,
) -> Res<()> {
    let label = match relation.get("id") {
        None => "strength comparison".to_owned(),
        value => py_str(value),
    };
    if text(relation, "subject_kind") != "statement" || text(relation, "object_kind") != "statement"
    {
        return Err(format!("{label}: strength comparisons relate statements"));
    }
    let lean_statement = |sid: Option<&Value>| {
        sid.and_then(Value::as_str)
            .and_then(|sid| statements.get(sid))
            .is_some_and(|statement| truthy(statement.get("lean_declaration")))
    };
    for field in ["subject_id", "object_id", "delta_statement_id"] {
        if !lean_statement(relation.get(field)) {
            return Err(format!(
                "{label}: {field} needs a known statement with a Lean declaration"
            ));
        }
    }
    if relation.contains_key("remainder_statement_id")
        && !lean_statement(relation.get("remainder_statement_id"))
    {
        return Err(format!(
            "{label}: remainder_statement_id needs a known Lean statement"
        ));
    }
    let background = relation
        .get("background_statement_ids")
        .and_then(Value::as_array);
    let Some(background) = background.filter(|background| {
        background.iter().all(Value::is_string)
            && distinct(background)
            && background.iter().all(|sid| lean_statement(Some(sid)))
    }) else {
        return Err(format!(
            "{label}: background_statement_ids must list distinct known Lean statements in binder order"
        ));
    };
    let mut fields: HashSet<String> = ["stronger", "weaker", "delta"]
        .into_iter()
        .map(str::to_owned)
        .chain((0..background.len()).map(|i| format!("background.{i}")))
        .collect();
    if truthy(relation.get("remainder_statement_id")) {
        fields.insert("remainder".into());
    }
    let maps_ok = relation
        .get("statement_parameter_indices")
        .and_then(Value::as_object)
        .is_some_and(|maps| {
            maps.keys().cloned().collect::<HashSet<_>>() == fields
                && maps.values().all(|indices| {
                    indices.as_array().is_some_and(|indices| {
                        let numbers: Option<Vec<u64>> = indices.iter().map(Value::as_u64).collect();
                        numbers
                            .is_some_and(|numbers| numbers.windows(2).all(|pair| pair[0] < pair[1]))
                    })
                })
        });
    if !maps_ok {
        return Err(format!(
            "{label}: statement_parameter_indices must give each field an ordered subsequence of the shared telescope"
        ));
    }
    for (field, name) in [("comparison_spec", "comparison_spec"), ("note", "note")] {
        if !string(relation, field).is_some_and(|v| !v.trim().is_empty()) {
            return Err(format!("{label}: {name} must be nonempty text"));
        }
    }
    for forbidden in [
        "verified",
        "status",
        "strictly_stronger",
        "strict",
        "minimal",
        "unique_delta",
    ] {
        if relation.contains_key(forbidden) {
            return Err(format!(
                "{label}: {forbidden} is not registration authority; status is derived from checked evidence"
            ));
        }
    }
    let Some(evidence) = relation
        .get("evidence_result_ids")
        .and_then(Value::as_object)
        .filter(|evidence| {
            !evidence.is_empty()
                && evidence
                    .keys()
                    .all(|k| STRENGTH_ROLES.contains(&k.as_str()))
        })
    else {
        return Err(format!(
            "{label}: evidence_result_ids needs named supported certificate roles"
        ));
    };
    if (evidence.contains_key("allowed_cases") || evidence.contains_key("remainder_identity"))
        && !truthy(relation.get("remainder_statement_id"))
    {
        return Err(format!(
            "{label}: remainder certificates need a named remainder_statement_id"
        ));
    }
    let separator = get(relation, "separator");
    if let Some(separator) = separator {
        let separator = separator
            .as_object()
            .ok_or_else(|| format!("{label}: separator must name a setting and result_id"))?;
        for field in ["setting", "result_id"] {
            if !string(separator, field).is_some_and(|v| !v.trim().is_empty()) {
                return Err(format!("{label}: separator.{field} must be nonempty text"));
            }
        }
    }
    let controls: Vec<Value> = match relation.get("explanatory_control_result_ids") {
        None => Vec::new(),
        Some(Value::Array(items)) if items.iter().all(Value::is_string) && distinct(items) => {
            items.clone()
        }
        Some(_) => {
            return Err(format!(
                "{label}: explanatory controls must be distinct result IDs"
            ));
        }
    };
    let selected = controls
        .iter()
        .chain(evidence.values())
        .chain(separator.and_then(|s| s.get("result_id")));
    for rid in selected {
        let Some((rid, result)) = rid
            .as_str()
            .and_then(|rid| results.get(rid).map(|result| (rid, result)))
        else {
            return Err(format!(
                "{label}: unknown evidence result {}",
                py_str(Some(rid))
            ));
        };
        if !arguments.contains_key(text(result, "argument_id")) {
            return Err(format!("{label}: result {rid} has no canonical argument"));
        }
        if !configs.get(rid).is_some_and(|config| {
            strings(config, "theorem_names").contains(&text(result, "theorem"))
        }) {
            return Err(format!(
                "{label}: result theorem is not a Comparator obligation: {rid}"
            ));
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Source-evidence bindings (`source_evidence.validate_bindings` without the
// per-kind manifest schema)

fn passage_kind(passage: &Obj) -> &str {
    string(passage, "kind").unwrap_or("")
}

fn prefixes(passage: &Obj) -> Vec<&str> {
    strings(passage, "claim_locator_prefixes")
}

fn load_passages(root: &Path) -> Res<Vec<Record>> {
    let mut passages = Vec::new();
    for path in json_paths(&root.join("corpus").join("passages")) {
        let manifest = read_object(root, &path)?;
        let rel = relative(root, &path);
        let snapshot = manifest.get("snapshot").and_then(Value::as_object);
        let entries = manifest
            .get("passages")
            .and_then(Value::as_array)
            .filter(|entries| !entries.is_empty());
        let (Some(snapshot), Some(entries)) = (snapshot, entries) else {
            return Err(format!(
                "{rel}: expected snapshot object and non-empty passages list"
            ));
        };
        for entry in entries {
            let entry = entry
                .as_object()
                .ok_or_else(|| format!("{rel}: passages entries must be objects"))?;
            let mut merged = snapshot.clone();
            merged.extend(entry.iter().map(|(k, v)| (k.clone(), v.clone())));
            passages.push(Record {
                path: rel.clone(),
                fields: merged,
            });
        }
    }
    Ok(passages)
}

fn validate_bindings(root: &Path, sources: &[Record], claims: &[Record]) -> Res<usize> {
    let source_index = index_by_id(sources, "source")?;
    let passages = load_passages(root)?;
    let passage_index = index_by_id(&passages, "passage")?;
    // IDs are unique now, so the index order is the load order.
    let ordered: Vec<&Record> = passages.iter().collect();
    let is_web = |p: &Obj| passage_kind(p) == "web_snapshot";
    let is_media = |p: &Obj| passage_kind(p) == "media_span";
    let is_bib = |p: &Obj| passage_kind(p) == "bibliographic_span";
    let is_translation = |p: &Obj| (is_web(p) || is_bib(p)) && get(p, "translation").is_some();
    let is_unavailable = |p: &Obj| is_web(p) && p.contains_key("unavailable");
    let mut seen_prefixes: HashMap<(&str, &str), &str> = HashMap::new();
    for record in &ordered {
        let (path, passage) = (&record.path, &record.fields);
        let source_id = text(passage, "source_id");
        let Some(source) = source_index.get(source_id).map(|i| &sources[*i]) else {
            return Err(format!(
                "{path}: unknown source_id {}",
                py_str(passage.get("source_id"))
            ));
        };
        let id = text(passage, "id");
        let source_kind = string(&source.fields, "kind");
        if is_media(passage) {
            if source_kind != Some("media_recording") {
                return Err(format!(
                    "{path}: media span {id} needs a media_recording source"
                ));
            }
            if source.fields.get("youtube_id") != passage.get("youtube_id") {
                return Err(format!(
                    "{path}: media span {id} youtube_id disagrees with source {source_id}"
                ));
            }
        } else if is_web(passage) || is_bib(passage) {
            if source_kind == Some("media_recording") {
                return Err(format!(
                    "{path}: {} {id} cannot cite a media_recording source",
                    passage_kind(passage).replace('_', " ")
                ));
            }
        } else {
            if source_kind == Some("media_recording") {
                return Err(format!(
                    "{path}: text witness {id} cannot cite a media_recording source"
                ));
            }
            let listed = match source.fields.get("edition_urns") {
                None => Vec::new(),
                Some(Value::Array(items)) => items.iter().filter_map(Value::as_str).collect(),
                Some(_) => {
                    return Err(format!(
                        "{}: edition_urns must be a list when present",
                        source.path
                    ));
                }
            };
            let work_urn = string(&source.fields, "work_urn");
            let edition = text(passage, "edition_urn");
            if !work_urn.is_some_and(|work| {
                edition.starts_with(&format!("{work}.")) || listed.contains(&edition)
            }) {
                return Err(format!(
                    "{path}: edition_urn is not an edition of {}",
                    py_str(source.fields.get("work_urn"))
                ));
            }
        }
        for prefix in prefixes(passage) {
            if let Some(other) = seen_prefixes.get(&(source_id, prefix)) {
                return Err(format!(
                    "{path}: locator prefix {} overlaps with passage {other}",
                    quote(prefix)
                ));
            }
            seen_prefixes.insert((source_id, prefix), id);
        }
    }
    let overlap = |left: &[&str], right: &[&str]| {
        left.iter()
            .any(|a| right.iter().any(|b| a.starts_with(b) || b.starts_with(a)))
    };
    for record in &ordered {
        let passage = &record.fields;
        if !is_web(passage) {
            continue;
        }
        for witness in ordered.iter().map(|r| &r.fields) {
            if !is_web(witness)
                && !is_media(witness)
                && !is_bib(witness)
                && text(witness, "source_id") == text(passage, "source_id")
                && overlap(&prefixes(passage), &prefixes(witness))
            {
                return Err(format!(
                    "{}: web snapshot {} overlaps pinned witness {}; cite the pinned witness (upgrade its claims) instead",
                    record.path,
                    text(passage, "id"),
                    text(witness, "id")
                ));
            }
        }
    }
    for record in &ordered {
        let passage = &record.fields;
        if !is_bib(passage) {
            continue;
        }
        for witness in ordered.iter().map(|r| &r.fields) {
            if !is_bib(witness)
                && !is_media(witness)
                && text(witness, "source_id") == text(passage, "source_id")
                && overlap(&prefixes(passage), &prefixes(witness))
            {
                return Err(format!(
                    "{}: bibliographic span {} overlaps pinned witness {}; a bibliographic citation is allowed only where no pinnable witness exists, so cite the pinned witness instead",
                    record.path,
                    text(passage, "id"),
                    text(witness, "id")
                ));
            }
        }
    }
    let mut bound: HashMap<&str, &Obj> = HashMap::new();
    for claim in claims {
        let (path, fields) = (&claim.path, &claim.fields);
        require(fields, &["id", "source_id", "locator"], path)?;
        let locator = text(fields, "locator");
        let matches: Vec<&Obj> = ordered
            .iter()
            .map(|r| &r.fields)
            .filter(|p| {
                p.get("source_id") == fields.get("source_id")
                    && prefixes(p).iter().any(|prefix| locator.starts_with(prefix))
            })
            .collect();
        if matches.len() != 1 {
            let ids: Vec<&str> = matches.iter().map(|p| text(p, "id")).collect();
            let ids = if ids.is_empty() {
                "none".to_owned()
            } else {
                ids.join(", ")
            };
            return Err(format!(
                "{path}: claim must resolve to exactly one source passage; matched {} ({ids})",
                matches.len()
            ));
        }
        bound.insert(text(fields, "id"), matches[0]);
    }
    let claim_by_id: HashMap<&str, &Obj> = claims
        .iter()
        .map(|c| (text(&c.fields, "id"), &c.fields))
        .collect();
    for claim in claims {
        let (path, fields) = (&claim.path, &claim.fields);
        let passage = bound[text(fields, "id")];
        let basis = get(fields, "basis");
        if is_translation(passage) {
            if basis.and_then(Value::as_str) != Some("translation") {
                return Err(format!(
                    "{path}: claim on translated web snapshot {} needs basis: 'translation'",
                    text(passage, "id")
                ));
            }
        } else if let Some(basis) = basis {
            return Err(format!(
                "{path}: basis {} is only for claims on a translated web snapshot",
                py_repr(Some(basis))
            ));
        }
        let parent = string(fields, "interpretation_of");
        if basis.and_then(Value::as_str) == Some("translation")
            && let Some(parent) = parent.filter(|p| claim_by_id.contains_key(p))
            && !is_translation(bound[parent])
        {
            return Err(format!(
                "{path}: a translation-based claim cannot be an alternative reading of {parent}, which is read from an original-language witness"
            ));
        }
    }
    for claim in claims {
        let (path, fields) = (&claim.path, &claim.fields);
        let passage = bound[text(fields, "id")];
        let witness = get(fields, "witness");
        let expected = if is_bib(passage) {
            Some(("bibliographic", "bibliographic span"))
        } else if is_unavailable(passage) {
            Some(("unavailable", "permanently unavailable web snapshot"))
        } else {
            None
        };
        match (expected, witness) {
            (Some((expected, what)), witness)
                if witness.and_then(Value::as_str) != Some(expected) =>
            {
                return Err(format!(
                    "{path}: claim on {what} {} needs witness: {} (not byte-verified)",
                    text(passage, "id"),
                    quote(expected)
                ));
            }
            (None, Some(witness)) => {
                return Err(format!(
                    "{path}: witness {} is only for claims on a bibliographic span or a permanently unavailable web snapshot; remove it when the passage is upgraded to a pinned, available witness",
                    py_repr(Some(witness))
                ));
            }
            _ => {}
        }
    }
    Ok(passage_index.len())
}

// ---------------------------------------------------------------------------
// validate()

fn ids_of(records: &[Record]) -> HashMap<&str, &Obj> {
    records
        .iter()
        .map(|record| (text(&record.fields, "id"), &record.fields))
        .collect()
}

fn strength_matches(argument: Option<&&Obj>, strong: &str, weak: &str) -> bool {
    argument.is_some_and(|argument| {
        strings(argument, "premise_statement_ids") == [strong]
            && argument
                .get("premise_statement_ids")
                .and_then(Value::as_array)
                .map(Vec::len)
                == Some(1)
            && text(argument, "conclusion_statement_id") == weak
            && !truthy(argument.get("commitment_statement_ids"))
    })
}

/// The records `check_warnings` reads again.
struct Loaded {
    statements: Vec<Record>,
    claims: Vec<Record>,
    arguments: Vec<Record>,
    relations: Vec<Record>,
    results: Vec<Record>,
    definitions: Vec<Record>,
    attempts: Vec<Record>,
    inferences: Vec<Record>,
}

fn validate(
    root: &Path,
    lean_paths: &[(Vec<String>, PathBuf)],
) -> Res<(Loaded, Vec<(&'static str, usize)>)> {
    let load = |name| load_dir(root, name);
    let sources = load("sources")?;
    let statements = load("statements")?;
    let claims = load("claims")?;
    let inferences = load("inferences")?;
    let arguments = load("arguments")?;
    let relations = load("relations")?;
    let candidates = load("candidates")?;
    let results = load("results")?;
    let definitions = load("definitions")?;
    let disambiguations = load("disambiguations")?;
    let attempts = load("attempts")?;

    let source_index = index_by_id(&sources, "source")?;
    let statement_index = index_by_id(&statements, "statement")?;
    let claim_index = index_by_id(&claims, "claim")?;
    let inference_index = index_by_id(&inferences, "inference")?;
    let argument_index = index_by_id(&arguments, "argument")?;
    let relation_index = index_by_id(&relations, "relation")?;
    let candidate_index = index_by_id(&candidates, "candidate")?;
    let result_index = index_by_id(&results, "result")?;
    let definition_index = index_by_id(&definitions, "definition")?;
    let disambiguation_index = index_by_id(&disambiguations, "disambiguation")?;
    let attempt_index = index_by_id(&attempts, "attempt")?;

    let statement_by_id = ids_of(&statements);
    let result_by_id = ids_of(&results);
    let argument_by_id = ids_of(&arguments);
    let checker = Checker {
        root,
        imports: Default::default(),
    };

    // registered_models
    let models = load("models")?;
    index_by_id(&models, "model")?;
    for model in &models {
        validate_model(&model.fields, &statement_by_id, root)
            .map_err(|error| format!("{}: {error}", model.path))?;
    }

    // registered_configurations
    let configurations = load("configurations")?;
    index_by_id(&configurations, "configuration")?;
    let selected: BTreeSet<&str> = configurations
        .iter()
        .flat_map(|case| {
            strings(&case.fields, "incompatibility_result_ids")
                .into_iter()
                .chain(strings(&case.fields, "implication_result_ids"))
        })
        .collect();
    for rid in selected {
        if let Some(result) = result_by_id.get(rid) {
            checker.result_config(
                &format!("corpus/results/{rid}.json"),
                result,
                &argument_index,
            )?;
        }
    }
    if configurations
        .iter()
        .any(|case| truthy(case.fields.get("implication_result_ids")))
    {
        let refs: Vec<&Obj> = results.iter().map(|result| &result.fields).collect();
        let transcriptions = thickness::transcription_kinds(root, &refs);
        for case in &configurations {
            let mut rejected: Vec<&str> = strings(&case.fields, "implication_result_ids")
                .into_iter()
                .filter(|rid| transcriptions.contains_key(*rid))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            rejected.sort();
            if !rejected.is_empty() {
                return Err(format!(
                    "{}: transcriptions cannot supply deductions: {}",
                    case.path,
                    str_list_repr(&rejected)
                ));
            }
        }
    }
    let model_by_id: BTreeMap<&str, &Obj> = models
        .iter()
        .map(|model| (text(&model.fields, "id"), &model.fields))
        .collect();
    let case_context = CaseContext {
        statements: &statement_by_id,
        results: &result_by_id,
        arguments: &argument_by_id,
        models: &model_by_id,
        root,
    };
    for case in &configurations {
        validate_case(&case.fields, &case_context)
            .map_err(|error| format!("{}: {error}", case.path))?;
    }

    let statement_ids: HashSet<&str> = statement_index.keys().map(String::as_str).collect();
    let claim_ids: HashSet<&str> = claim_index.keys().map(String::as_str).collect();
    let result_ids: HashSet<&str> = result_index.keys().map(String::as_str).collect();
    let definition_ids: HashSet<&str> = definition_index.keys().map(String::as_str).collect();
    let disambiguation_ids: HashSet<&str> =
        disambiguation_index.keys().map(String::as_str).collect();
    let citable: HashSet<&str> = statement_ids
        .iter()
        .chain(&definition_ids)
        .chain(&disambiguation_ids)
        .copied()
        .collect();
    let evidence: HashSet<&str> = result_ids.union(&claim_ids).copied().collect();
    for attempt in &attempts {
        validate_attempt(&attempt.fields, &statement_ids, &evidence)
            .map_err(|error| format!("{}: {error}", attempt.path))?;
        validate_prose_ids(
            &attempt.path,
            &attempt.fields,
            &["summary", "blocker"],
            &citable,
        )?;
    }
    let mut used_definitions: HashSet<&str> = HashSet::new();

    for path in json_paths(&root.join("corpus").join("sources")) {
        let record = read_object(root, &path)?;
        if let Some(Value::Array(items)) = record.get("edition_urns") {
            let values: Vec<&str> = items.iter().filter_map(Value::as_str).collect();
            let mut sorted = values.clone();
            sorted.sort();
            if values != sorted {
                return Err(format!(
                    "{}: edition_urns must be sorted; run python3 scripts/corpus.py sort-lists",
                    relative(root, &path)
                ));
            }
        }
    }

    for source in &sources {
        require(
            &source.fields,
            &[
                "id",
                "kind",
                "author",
                "work",
                "citation_system",
                "work_urn",
                "catalog_url",
            ],
            &source.path,
        )?;
    }

    let passage_count = validate_bindings(root, &sources, &claims)?;

    let lean = LeanText::load(lean_paths);

    let mut declared_by: HashMap<&str, &str> = HashMap::new();
    for statement in &statements {
        let (path, fields) = (statement.path.as_str(), &statement.fields);
        require(fields, &["id", "paraphrase"], path)?;
        if let Some(declaration) = get(fields, "lean_declaration") {
            lean_tail_exists(path, Some(declaration), &lean)?;
            let declaration = declaration.as_str().unwrap_or_default();
            let id = text(fields, "id");
            let other = *declared_by.entry(declaration).or_insert(id);
            if other != id {
                return Err(format!(
                    "{path}: lean_declaration {declaration} is already the declaration of statement {other}; each statement needs its own"
                ));
            }
        }
        validate_self_evident(path, fields, &claim_ids, &result_ids, &statement_ids)?;
        validate_settlement_actions(fields).map_err(|error| format!("{path}: {error}"))?;
        used_definitions.extend(validate_term_links(
            path,
            fields,
            &definition_ids,
            &disambiguation_ids,
        )?);
    }

    for definition in &definitions {
        let (path, fields) = (definition.path.as_str(), &definition.fields);
        require(fields, &["id", "term", "definition", "basis"], path)?;
        if !text(fields, "id").starts_with("DEF-") {
            return Err(format!("{path}: definition id must start with DEF-"));
        }
        let basis = string(fields, "basis").filter(|b| matches!(*b, "sourced" | "stipulative"));
        let Some(basis) = basis else {
            return Err(format!("{path}: basis must be one of sourced, stipulative"));
        };
        if fields.contains_key("claim_ids") || basis == "sourced" {
            for claim in require_string_list(fields, "claim_ids", path, basis != "sourced")? {
                if !claim_ids.contains(claim) {
                    return Err(format!("{path}: unknown claim id {claim}"));
                }
            }
        }
        if basis == "stipulative" && !truthy(fields.get("note")) {
            return Err(format!(
                "{path}: a stipulative definition needs a note saying why it is stipulated and what would source it"
            ));
        }
        if fields.contains_key("lean_declaration") {
            lean_tail_exists(path, fields.get("lean_declaration"), &lean)?;
        }
        validate_prose_ids(path, fields, &["definition", "note"], &citable)?;
    }
    for disambiguation in &disambiguations {
        let (path, fields) = (disambiguation.path.as_str(), &disambiguation.fields);
        require(fields, &["id", "term", "resolution"], path)?;
        if !text(fields, "id").starts_with("DISAMB-") {
            return Err(format!("{path}: disambiguation id must start with DISAMB-"));
        }
        let senses = require_string_list(fields, "sense_definition_ids", path, false)?;
        if senses.iter().collect::<HashSet<_>>().len() < 2 {
            return Err(format!(
                "{path}: a disambiguation needs at least two distinct senses"
            ));
        }
        for sense in &senses {
            if !definition_ids.contains(sense) {
                return Err(format!("{path}: unknown sense definition id {sense}"));
            }
        }
        validate_prose_ids(path, fields, &["resolution"], &citable)?;
        used_definitions.extend(senses);
    }

    for claim in &claims {
        let (path, fields) = (claim.path.as_str(), &claim.fields);
        require(
            fields,
            &[
                "id",
                "statement_id",
                "source_id",
                "locator",
                "interpretation",
                "status",
            ],
            path,
        )?;
        if !statement_ids.contains(text(fields, "statement_id")) {
            return Err(format!(
                "{path}: unknown statement_id {}",
                py_str(fields.get("statement_id"))
            ));
        }
        if !source_index.contains_key(text(fields, "source_id")) {
            return Err(format!(
                "{path}: unknown source_id {}",
                py_str(fields.get("source_id"))
            ));
        }
        if string(fields, "status") != Some("formalized") {
            return Err(format!(
                "{path}: claim status must be 'formalized' in the MVP"
            ));
        }
        if let Some(attribution) = fields.get("attribution")
            && !attribution.as_str().is_some_and(|a| {
                a.starts_with(ATTRIBUTION_PREFIX)
                    && a.trim().chars().count() >= MIN_ATTRIBUTION_CHARS
            })
        {
            return Err(format!(
                "{path}: attribution must be one sentence starting {} that says what the passage states and that it is the premise (at least {MIN_ATTRIBUTION_CHARS} characters)",
                quote(ATTRIBUTION_PREFIX)
            ));
        }
        if let Some(parent) = get(fields, "interpretation_of")
            && !parent.as_str().is_some_and(|p| claim_ids.contains(p))
        {
            return Err(format!(
                "{path}: unknown interpretation_of claim {}",
                py_str(Some(parent))
            ));
        }
        used_definitions.extend(validate_term_links(
            path,
            fields,
            &definition_ids,
            &disambiguation_ids,
        )?);
    }

    for inference in &inferences {
        let (path, fields) = (inference.path.as_str(), &inference.fields);
        require(
            fields,
            &["id", "output_statement_id", "rule", "meaning"],
            path,
        )?;
        let inputs = require_string_list(fields, "input_statement_ids", path, true)?;
        let assumptions = require_string_list(fields, "assumption_statement_ids", path, true)?;
        let discharges = require_string_list(fields, "discharged_statement_ids", path, true)?;
        for sid in inputs
            .iter()
            .chain(&assumptions)
            .chain(&discharges)
            .copied()
            .chain(std::iter::once(text(fields, "output_statement_id")))
        {
            if !statement_ids.contains(sid) {
                let shown = if sid.is_empty() {
                    py_str(fields.get("output_statement_id"))
                } else {
                    sid.to_owned()
                };
                return Err(format!("{path}: unknown statement id {shown}"));
            }
        }
        if discharges.iter().any(|d| !assumptions.contains(d)) {
            return Err(format!(
                "{path}: discharged assumptions must also be listed as scoped assumptions"
            ));
        }
    }

    let inference_by_id = ids_of(&inferences);
    for argument in &arguments {
        let (path, fields) = (argument.path.as_str(), &argument.fields);
        require(
            fields,
            &["id", "conclusion_statement_id", "inference_ids", "meaning"],
            path,
        )?;
        let commitments = if fields.contains_key("commitment_statement_ids") {
            require_string_list(fields, "commitment_statement_ids", path, true)?
        } else {
            Vec::new()
        };
        let premises = require_string_list(fields, "premise_statement_ids", path, true)?;
        let inference_ids = require_string_list(fields, "inference_ids", path, false)?;
        let conclusion = text(fields, "conclusion_statement_id");
        for sid in premises
            .iter()
            .chain(&commitments)
            .copied()
            .chain(std::iter::once(conclusion))
        {
            if !statement_ids.contains(sid) {
                let shown = if sid.is_empty() {
                    py_str(fields.get("conclusion_statement_id"))
                } else {
                    sid.to_owned()
                };
                return Err(format!("{path}: unknown statement id {shown}"));
            }
        }
        for id in &inference_ids {
            if !inference_index.contains_key(*id) {
                return Err(format!("{path}: unknown inference id {id}"));
            }
        }
        validate_argument_derivation(path, fields, &inference_by_id)?;
        used_definitions.extend(validate_term_links(
            path,
            fields,
            &definition_ids,
            &disambiguation_ids,
        )?);
        // validate_argument_senses
        let mut senses: HashSet<&str> = strings(fields, "definition_ids").into_iter().collect();
        for sid in std::iter::once(conclusion)
            .chain(premises.iter().copied())
            .chain(commitments.iter().copied())
        {
            senses.extend(strings(statement_by_id[sid], "definition_ids"));
        }
        let linked = strings(fields, "disambiguation_ids");
        for disambiguation in &disambiguations {
            let mut used: Vec<&str> = strings(&disambiguation.fields, "sense_definition_ids")
                .into_iter()
                .filter(|sense| senses.contains(sense))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            used.sort();
            let id = text(&disambiguation.fields, "id");
            if used.len() > 1 && !linked.contains(&id) {
                return Err(format!(
                    "{path}: uses senses {} of '{}' but does not link {id}",
                    used.join(", "),
                    py_str(disambiguation.fields.get("term"))
                ));
            }
        }
    }

    for relation in &relations {
        let (path, fields) = (relation.path.as_str(), &relation.fields);
        require(
            fields,
            &[
                "id",
                "subject_kind",
                "subject_id",
                "predicate",
                "object_kind",
                "object_id",
            ],
            path,
        )?;
        for side in ["subject", "object"] {
            let kind = text(fields, &format!("{side}_kind"));
            let id = text(fields, &format!("{side}_id"));
            if !ENTITY_KINDS.contains(&kind) {
                return Err(format!(
                    "{path}: unknown {side}_kind {}",
                    py_str(fields.get(&format!("{side}_kind")))
                ));
            }
            let index = match kind {
                "source" => &source_index,
                "statement" => &statement_index,
                "claim" => &claim_index,
                "inference" => &inference_index,
                _ => &argument_index,
            };
            if !index.contains_key(id) {
                return Err(format!(
                    "{path}: unknown {side} {kind} id {}",
                    py_str(fields.get(&format!("{side}_id")))
                ));
            }
        }
        validate_premise_program_relation(path, fields)?;
        if text(fields, "predicate") == "root_route" {
            let routed = text(
                argument_by_id[text(fields, "subject_id")],
                "conclusion_statement_id",
            );
            if routed != text(fields, "object_id") {
                return Err(format!(
                    "{path}: root_route argument {} concludes {routed}, not {}",
                    text(fields, "subject_id"),
                    text(fields, "object_id")
                ));
            }
        }
    }

    for candidate in &candidates {
        let (path, fields) = (candidate.path.as_str(), &candidate.fields);
        require(
            fields,
            &[
                "id",
                "source_id",
                "locator",
                "priority",
                "goal",
                "reason",
                "status",
            ],
            path,
        )?;
        if !source_index.contains_key(text(fields, "source_id")) {
            return Err(format!(
                "{path}: unknown source_id {}",
                py_str(fields.get("source_id"))
            ));
        }
        if string(fields, "status") != Some("candidate") {
            return Err(format!("{path}: candidate status must be 'candidate'"));
        }
        if !fields
            .get("priority")
            .is_some_and(|p| p.is_i64() || p.is_u64() || p.is_boolean())
        {
            return Err(format!("{path}: priority must be an integer"));
        }
    }

    let mut configs: HashMap<String, Obj> = HashMap::new();
    for result in &results {
        let config = checker.result_config(&result.path, &result.fields, &argument_index)?;
        configs.insert(text(&result.fields, "id").to_owned(), config);
    }

    for result in &results {
        let (path, fields) = (result.path.as_str(), &result.fields);
        validate_case_split(fields, &statement_ids, &result_ids)
            .map_err(|error| format!("{path}: {error}"))?;
        for case in get(fields, "case_split")
            .and_then(|split| split.get("cases"))
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .filter_map(Value::as_object)
        {
            lean_tail_exists(path, case.get("lean_declaration"), &lean)?;
        }
    }

    for relation in &relations {
        let (path, fields) = (relation.path.as_str(), &relation.fields);
        let predicate = text(fields, "predicate");
        if predicate == "instance_of_schema" {
            require(
                fields,
                &[
                    "verification_result_id",
                    "instance_theorem",
                    "schema_theorem",
                    "note",
                ],
                path,
            )?;
            if !string(fields, "note").is_some_and(|note| !note.trim().is_empty()) {
                return Err(format!(
                    "{path}: schema registration note must be nonempty text"
                ));
            }
            let Some(result_id) =
                string(fields, "verification_result_id").filter(|id| result_by_id.contains_key(id))
            else {
                return Err(format!(
                    "{path}: unknown verification_result_id {}",
                    py_str(fields.get("verification_result_id"))
                ));
            };
            for field in ["instance_theorem", "schema_theorem"] {
                if !string(fields, field).is_some_and(|theorem| {
                    strings(&configs[result_id], "theorem_names").contains(&theorem)
                }) {
                    return Err(format!(
                        "{path}: {field} must name an obligation in {result_id}'s Comparator config"
                    ));
                }
            }
        }
        if predicate == "strengthens" {
            require(fields, &["verification_result_id", "note"], path)?;
            if !string(fields, "note").is_some_and(|note| !note.trim().is_empty()) {
                return Err(format!("{path}: strengthens note must be nonempty text"));
            }
            let (strong, weak) = (text(fields, "subject_id"), text(fields, "object_id"));
            if strong == weak {
                return Err(format!("{path}: strengthens relates {strong} to itself"));
            }
            let result_id = fields.get("verification_result_id");
            let Some((result_id, result)) = result_id
                .and_then(Value::as_str)
                .and_then(|id| result_by_id.get(id).map(|result| (id, result)))
            else {
                return Err(format!(
                    "{path}: strengthens needs a verified result proving the entailment; unknown verification_result_id {}",
                    py_str(result_id)
                ));
            };
            if !strength_matches(
                argument_by_id.get(text(result, "argument_id")),
                strong,
                weak,
            ) {
                return Err(format!(
                    "{path}: {result_id} does not prove the entailment: its argument must have exactly the premise {strong} and the conclusion {weak}"
                ));
            }
            if let Some(strictness) = get(fields, "strictness_result_id") {
                let argument = strictness
                    .as_str()
                    .and_then(|id| result_by_id.get(id))
                    .filter(|result| !result.is_empty())
                    .and_then(|result| argument_by_id.get(text(result, "argument_id")));
                if !argument.is_some_and(|argument| !truthy(argument.get("premise_statement_ids")))
                {
                    return Err(format!(
                        "{path}: strictness_result_id {} must name a verified premise-free result",
                        py_str(Some(strictness))
                    ));
                }
            }
        }
        if predicate == "strength_comparison" {
            validate_strength_comparison(
                fields,
                &statement_by_id,
                &result_by_id,
                &argument_by_id,
                &configs,
            )
            .map_err(|error| format!("{path}: {error}"))?;
        }
    }

    // validate_strength_order
    let mut by_id: Vec<&Record> = relations.iter().collect();
    by_id.sort_by_key(|relation| text(&relation.fields, "id"));
    let mut pairs: HashMap<(&str, &str), &str> = HashMap::new();
    let mut backing: HashMap<&str, &str> = HashMap::new();
    for relation in &by_id {
        let (path, fields) = (relation.path.as_str(), &relation.fields);
        if text(fields, "predicate") != "strengthens" {
            continue;
        }
        let pair = (text(fields, "subject_id"), text(fields, "object_id"));
        if let Some(other) = pairs.get(&pair) {
            return Err(format!(
                "{path}: {other} already registers {} strengthens {}",
                pair.0, pair.1
            ));
        }
        if let Some(other) = pairs.get(&(pair.1, pair.0)) {
            return Err(format!(
                "{path}: {other} registers the reverse strength order; record equivalent versions with logically_equivalent_to"
            ));
        }
        let id = text(fields, "id");
        pairs.insert(pair, id);
        let result_id = text(fields, "verification_result_id");
        if let Some(other) = backing.get(result_id) {
            return Err(format!("{path}: {result_id} already backs {other}"));
        }
        backing.insert(result_id, id);
    }
    let strong_versions: HashSet<&str> = relations
        .iter()
        .filter(|relation| text(&relation.fields, "predicate") == "strengthens")
        .map(|relation| text(&relation.fields, "subject_id"))
        .collect();
    for argument in &arguments {
        let (path, fields) = (argument.path.as_str(), &argument.fields);
        let Some(needed) = get(fields, "strong_version_needed") else {
            continue;
        };
        let needed = needed
            .as_object()
            .filter(|needed| !needed.is_empty())
            .ok_or_else(|| format!("{path}: strong_version_needed must be a nonempty object"))?;
        let premises = strings(fields, "premise_statement_ids");
        for (sid, reason) in needed {
            if !premises.contains(&sid.as_str()) {
                return Err(format!(
                    "{path}: strong_version_needed names {sid}, which is not a premise"
                ));
            }
            if !strong_versions.contains(sid.as_str()) {
                return Err(format!(
                    "{path}: strong_version_needed names {sid}, which strengthens no statement"
                ));
            }
            if !reason.as_str().is_some_and(|r| !r.trim().is_empty()) {
                return Err(format!(
                    "{path}: strong_version_needed reason for {sid} must be nonempty text"
                ));
            }
        }
    }

    let mut unused: Vec<&str> = definition_ids
        .iter()
        .copied()
        .filter(|id| !used_definitions.contains(id))
        .collect();
    unused.sort();
    if !unused.is_empty() {
        return Err(format!(
            "definition(s) linked from no statement, claim or argument and not a sense of any disambiguation: {}",
            unused.join(", ")
        ));
    }
    let mut collisions: Vec<&str> = candidate_index
        .keys()
        .filter(|id| result_index.contains_key(*id))
        .map(String::as_str)
        .collect();
    collisions.sort();
    if !collisions.is_empty() {
        return Err(format!(
            "candidate/result id collision(s): {}",
            collisions.join(", ")
        ));
    }

    let counts = vec![
        ("sources", source_index.len()),
        ("passages", passage_count),
        ("statements", statement_index.len()),
        ("claims", claim_index.len()),
        ("inferences", inference_index.len()),
        ("arguments", argument_index.len()),
        ("relations", relation_index.len()),
        ("candidates", candidate_index.len()),
        ("results", result_index.len()),
        ("definitions", definition_index.len()),
        ("disambiguations", disambiguation_index.len()),
        ("attempts", attempt_index.len()),
        ("models", models.len()),
    ];
    Ok((
        Loaded {
            statements,
            claims,
            arguments,
            relations,
            results,
            definitions,
            attempts,
            inferences,
        },
        counts,
    ))
}

// ---------------------------------------------------------------------------
// check_warnings()

const CATEGORY_MARKER: &str = "category-constant: intended";

fn category_patterns() -> Vec<Regex> {
    let name = r"[A-Za-z_.]*(?:concrete|abstract)";
    let lambda = r"fun(?:\s+(?:[A-Za-z_][\w']*|\([^()]*\)|\{[^{}]*\}))+\s*=>\s*(True|False)(?=[ \t]*(?:$|[,})\]⟩]|--))";
    [
        format!(r"(?im)\b({name})\s*:=\s*{lambda}"),
        format!(r"(?im)\bdef\s+({name})\b[^:=]*:[^=]*:=\s*{lambda}"),
        format!(
            r"(?im)\bdef\s+({name})\s*(?:\([^)]*\)\s*|\{{[^}}]*\}}\s*)*:\s*Prop\s*:=\s*(True|False)(?=[ \t]*(?:$|--))"
        ),
    ]
    .iter()
    .map(|pattern| Regex::new(pattern).expect("category pattern"))
    .collect()
}

/// Python `_blank_lean_comments`: comments become spaces, newlines stay.
fn blank_lean_comments(text: &str) -> String {
    let chars: Vec<char> = text.chars().collect();
    let mut out = chars.clone();
    let (mut i, mut depth, n) = (0, 0usize, chars.len());
    let at = |i: usize, a: char, b: char| i + 1 < n && chars[i] == a && chars[i + 1] == b;
    while i < n {
        if depth == 0 && at(i, '-', '-') {
            while i < n && chars[i] != '\n' {
                out[i] = ' ';
                i += 1;
            }
            continue;
        }
        if at(i, '/', '-') {
            depth += 1;
            out[i] = ' ';
            out[i + 1] = ' ';
            i += 2;
            continue;
        }
        if depth > 0 && at(i, '-', '/') {
            depth -= 1;
            out[i] = ' ';
            out[i + 1] = ' ';
            i += 2;
            continue;
        }
        if depth > 0 && chars[i] != '\n' {
            out[i] = ' ';
        }
        i += 1;
    }
    out.into_iter().collect()
}

fn trivial_category_warnings(files: &[(Vec<String>, PathBuf)]) -> Vec<(String, usize, String)> {
    let patterns = category_patterns();
    let mut warnings = Vec::new();
    for (parts, path) in files {
        let source = fs::read_to_string(path).unwrap_or_default();
        // Every pattern needs a name ending in `concrete` or `abstract`
        // (case-insensitive); other files cannot match. `ſ` case-folds to `s`.
        let lower = source.to_lowercase();
        if !lower.contains("concrete") && !lower.contains("abstract") && !source.contains('ſ') {
            continue;
        }
        let code = blank_lean_comments(&source);
        let lines: Vec<&str> = source.split('\n').collect();
        let code_lines: Vec<&str> = code.split('\n').collect();
        let rel = parts.join("/");
        let mut seen = HashSet::new();
        for pattern in &patterns {
            for found in pattern.captures_iter(&code).flatten() {
                let whole = found.get(0).expect("match");
                let first = code[..whole.start()].matches('\n').count();
                let last = code[..whole.end()].matches('\n').count();
                if !seen.insert(first) {
                    continue;
                }
                let declares = (first..=last).any(|k| lines[k].contains(CATEGORY_MARKER)) || {
                    let mut k = first;
                    let mut found_marker = false;
                    while k > 0
                        && !lines[k - 1].trim().is_empty()
                        && code_lines[k - 1].trim().is_empty()
                    {
                        if lines[k - 1].contains(CATEGORY_MARKER) {
                            found_marker = true;
                            break;
                        }
                        k -= 1;
                    }
                    found_marker
                };
                if declares {
                    continue;
                }
                let name = found.get(1).map_or("", |m| m.as_str());
                let constant = found.get(2).map_or("", |m| m.as_str());
                warnings.push((
                    rel.clone(),
                    first + 1,
                    format!(
                        "{rel}:{}: category predicate {name} is constantly {constant}; declare '{CATEGORY_MARKER} (<reason>)' if the constant is the model's point or does no work, otherwise use a non-degenerate classification (#1103)",
                        first + 1
                    ),
                ));
            }
        }
    }
    warnings
}

fn check_warnings(root: &Path, loaded: &Loaded, files: &[(Vec<String>, PathBuf)]) -> Vec<String> {
    let records = thickness::Records {
        statements: loaded.statements.iter().map(|r| &r.fields).collect(),
        arguments: loaded.arguments.iter().map(|r| &r.fields).collect(),
        results: loaded.results.iter().map(|r| &r.fields).collect(),
        relations: loaded.relations.iter().map(|r| &r.fields).collect(),
        claims: loaded.claims.iter().map(|r| &r.fields).collect(),
        attempts: loaded.attempts.iter().map(|r| &r.fields).collect(),
        definitions: loaded.definitions.iter().map(|r| &r.fields).collect(),
        inferences: loaded.inferences.iter().map(|r| &r.fields).collect(),
    };
    let flags = crate::frontier::transcription_flags(root, &records);
    let frontier = thickness::frontier_inputs(thickness::DEFAULT_ROOT, &records, &flags);
    let transcription_results: HashSet<String> =
        frontier.transcription_results.keys().cloned().collect();
    let mut warnings = Vec::new();

    let registration = &frontier.registration_arguments;
    let argument_by_id: HashMap<&str, &Obj> = records
        .arguments
        .iter()
        .filter(|a| !registration.contains(text(a, "id")))
        .map(|a| (text(a, "id"), *a))
        .collect();
    let result_by_id: HashMap<&str, &Obj> = records
        .results
        .iter()
        .filter(|r| !registration.contains(text(r, "argument_id")))
        .map(|r| (text(r, "id"), *r))
        .collect();
    let verified: HashSet<&str> = result_by_id
        .values()
        .map(|r| text(r, "argument_id"))
        .collect();
    let mut relations: Vec<&Obj> = records.relations.clone();
    relations.sort_by_key(|relation| text(relation, "id"));
    let mut alternatives: HashMap<&str, BTreeSet<&str>> = HashMap::new();
    let mut refuting: HashMap<&str, HashSet<&str>> = HashMap::new();
    for relation in &records.relations {
        match text(relation, "predicate") {
            "alternative_to" => {
                alternatives
                    .entry(text(relation, "object_id"))
                    .or_default()
                    .insert(text(relation, "subject_id"));
            }
            "refutes" => {
                refuting
                    .entry(text(relation, "object_id"))
                    .or_default()
                    .insert(text(relation, "subject_id"));
            }
            _ => {}
        }
    }
    let established = &frontier.established;
    for relation in relations
        .iter()
        .filter(|r| text(r, "predicate") == "refutes")
    {
        let subject = text(relation, "subject_id");
        let argument = argument_by_id.get(subject);
        let premises: BTreeSet<&str> = argument
            .map(|a| strings(a, "premise_statement_ids").into_iter().collect())
            .unwrap_or_default();
        let unestablished: Vec<&str> = premises
            .iter()
            .copied()
            .filter(|p| !established.contains(*p))
            .collect();
        let is_verified = verified.contains(subject);
        if argument.is_some() && is_verified && unestablished.is_empty() {
            continue;
        }
        let reason = if !is_verified {
            "its argument has no verified result".to_owned()
        } else {
            format!(
                "it rests on unestablished premises {}",
                unestablished.join(", ")
            )
        };
        warnings.push(format!(
            "{}: refutation of {} does not count for closure rule (c): {reason}",
            text(relation, "id"),
            text(relation, "object_id")
        ));
    }

    for relation in &relations {
        if text(relation, "predicate") == "supports"
            && !string(relation, "note").is_some_and(|note| !note.trim().is_empty())
        {
            warnings.push(format!(
                "{}: supports relation has no note recording the gap between {} and {}",
                text(relation, "id"),
                text(relation, "subject_id"),
                text(relation, "object_id")
            ));
        }
    }

    let mut categories = trivial_category_warnings(files);
    categories.sort_by(|a, b| (&a.0, a.1).cmp(&(&b.0, b.1)));
    warnings.extend(categories.into_iter().map(|(_, _, warning)| warning));

    // strength_use_warnings
    let all_arguments: HashMap<&str, &Obj> = records
        .arguments
        .iter()
        .map(|a| (text(a, "id"), *a))
        .collect();
    let all_results: HashMap<&str, &Obj> = records
        .results
        .iter()
        .map(|r| (text(r, "id"), *r))
        .collect();
    let mut weak_of: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    let mut registrations: HashSet<&str> = HashSet::new();
    for relation in relations
        .iter()
        .filter(|r| text(r, "predicate") == "strengthens")
    {
        let argument = string(relation, "verification_result_id")
            .and_then(|id| all_results.get(id))
            .and_then(|result| all_arguments.get(text(result, "argument_id")));
        let (strong, weak) = (text(relation, "subject_id"), text(relation, "object_id"));
        if strength_matches(argument, strong, weak) {
            registrations.insert(text(argument.expect("matched"), "id"));
            weak_of.entry(strong).or_default().push(weak);
        }
    }
    let mut sorted_arguments: Vec<&Obj> = records.arguments.clone();
    sorted_arguments.sort_by_key(|a| text(a, "id"));
    let mut undeclared: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for argument in sorted_arguments {
        if registrations.contains(text(argument, "id")) {
            continue;
        }
        let needed = argument
            .get("strong_version_needed")
            .and_then(Value::as_object);
        for premise in strings(argument, "premise_statement_ids") {
            if weak_of.contains_key(premise) && !needed.is_some_and(|n| n.contains_key(premise)) {
                undeclared
                    .entry(premise)
                    .or_default()
                    .push(text(argument, "id"));
            }
        }
    }
    for (strong, users) in undeclared {
        let mut weak = weak_of[strong].clone();
        weak.sort();
        warnings.push(format!(
            "{strong}: used by {} argument(s) without strong_version_needed although its weak version {} is proved from it; use the weakest version that suffices or record why it does not (#1017): {}",
            users.len(),
            weak.join(", "),
            users.join(", ")
        ));
    }

    // Unmet floor markings (Python `floor_reasons`).
    let claim_statement: HashMap<&str, &str> = records
        .claims
        .iter()
        .map(|c| (text(c, "id"), text(c, "statement_id")))
        .collect();
    let refuted = &frontier.refuted;
    let mut markings: Vec<(&str, &Obj)> = records
        .statements
        .iter()
        .filter_map(|s| {
            get(s, "self_evident")
                .and_then(Value::as_object)
                .map(|m| (text(s, "id"), m))
        })
        .collect();
    markings.sort_by_key(|(id, _)| *id);
    for (statement, marking) in markings {
        let basis = string(marking, "basis")
            .filter(|b| !b.is_empty())
            .unwrap_or("legacy");
        let rivals: Vec<&str> = alternatives
            .get(statement)
            .map(|set| set.iter().copied().collect())
            .unwrap_or_default();
        let stale = || -> Vec<String> {
            let Some(disagreement) = get(marking, "disagreement") else {
                return Vec::new();
            };
            if basis == "common_ground" && get(marking, "owner_approval").is_none() {
                return Vec::new();
            }
            let listed: HashSet<&str> = disagreement
                .as_object()
                .map(|d| strings(d, "rival_statement_ids").into_iter().collect())
                .unwrap_or_default();
            let unlisted: Vec<&str> = rivals
                .iter()
                .copied()
                .filter(|r| !listed.contains(r))
                .collect();
            if unlisted.is_empty() {
                Vec::new()
            } else {
                vec![format!(
                    "disagreement record omits recorded rivals: {}",
                    unlisted.join(", ")
                )]
            }
        };
        let stale_reasons = stale();
        let reasons: Vec<String> = if get(marking, "owner_approval").is_some()
            || !stale_reasons.is_empty()
        {
            stale_reasons
        } else {
            match basis {
                "legacy" => Vec::new(),
                "retorsion" => {
                    let denial = get(marking, "denial_statement_id");
                    let denial_id = denial.and_then(Value::as_str).unwrap_or_default();
                    if !denial
                        .and_then(Value::as_str)
                        .is_some_and(|d| rivals.contains(&d))
                    {
                        vec![format!(
                            "denial {} is not recorded as alternative_to {statement}",
                            py_str(denial)
                        )]
                    } else {
                        let mut reasons = Vec::new();
                        let mut met = false;
                        for rid in strings(marking, "justification_ids") {
                            let argument = result_by_id
                                .get(rid)
                                .and_then(|r| argument_by_id.get(text(r, "argument_id")));
                            let Some(argument) = argument else {
                                reasons.push(format!("{rid} has no argument"));
                                continue;
                            };
                            let argument_id = text(argument, "id");
                            if transcription_results.contains(rid) {
                                reasons.push(format!("{rid} is a transcription"));
                            } else if !refuting
                                .get(denial_id)
                                .is_some_and(|s| s.contains(argument_id))
                            {
                                reasons.push(format!(
                                    "{argument_id} has no refutes relation to {denial_id}"
                                ));
                            } else {
                                let open: BTreeSet<&str> =
                                    strings(argument, "premise_statement_ids")
                                        .into_iter()
                                        .filter(|p| !established.contains(*p))
                                        .collect();
                                if open.is_empty() {
                                    met = true;
                                    break;
                                }
                                reasons.push(format!(
                                    "{rid} rests on unestablished premises {}",
                                    open.into_iter().collect::<Vec<_>>().join(", ")
                                ));
                            }
                        }
                        if met { Vec::new() } else { reasons }
                    }
                }
                "common_ground" => {
                    if !rivals.is_empty() {
                        vec![format!("recorded rivals deny it: {}", rivals.join(", "))]
                    } else {
                        let question = get(marking, "question_statement_id");
                        let question_id = question.and_then(Value::as_str).unwrap_or_default();
                        let question_rivals: Vec<&str> = alternatives
                            .get(question_id)
                            .map(|s| s.iter().copied().collect())
                            .unwrap_or_default();
                        if question_rivals.is_empty() {
                            vec![format!(
                                "no rival position recorded on {}",
                                py_str(question)
                            )]
                        } else {
                            let mut committed: HashMap<&str, usize> = HashMap::new();
                            for position in marking
                                .get("positions")
                                .and_then(Value::as_array)
                                .into_iter()
                                .flatten()
                                .filter_map(Value::as_object)
                            {
                                let stating = strings(position, "claim_ids")
                                    .into_iter()
                                    .filter(|c| claim_statement.get(c) == Some(&statement))
                                    .count();
                                *committed.entry(text(position, "statement_id")).or_default() +=
                                    stating;
                            }
                            let missing: Vec<&str> = std::iter::once(question_id)
                                .chain(question_rivals)
                                .filter(|p| committed.get(p).is_none_or(|c| *c == 0))
                                .collect();
                            if missing.is_empty() {
                                Vec::new()
                            } else {
                                vec![format!(
                                    "no proponent claim stating it for position {}",
                                    missing.join(", ")
                                )]
                            }
                        }
                    }
                }
                _ => {
                    let mut reasons = Vec::new();
                    if !strings(marking, "justification_ids")
                        .iter()
                        .any(|c| claim_statement.get(c) == Some(&statement))
                    {
                        reasons.push("no justification claim states it".to_owned());
                    }
                    let sceptical: HashSet<&str> = strings(marking, "sceptical_rival_ids")
                        .into_iter()
                        .collect();
                    let not_sceptical: Vec<&str> = rivals
                        .iter()
                        .copied()
                        .filter(|r| !sceptical.contains(r))
                        .collect();
                    if !not_sceptical.is_empty() {
                        reasons.push(format!(
                            "rivals not recorded as global sceptical positions: {}",
                            not_sceptical.join(", ")
                        ));
                    }
                    let unrefuted: Vec<&str> = rivals
                        .iter()
                        .copied()
                        .filter(|r| sceptical.contains(r) && !refuted.contains(*r))
                        .collect();
                    if !unrefuted.is_empty() {
                        reasons.push(format!(
                            "sceptical rivals not refuted: {}",
                            unrefuted.join(", ")
                        ));
                    }
                    reasons
                }
            }
        };
        if !reasons.is_empty() {
            warnings.push(format!(
                "{statement}: self_evident basis {basis} is not met, so the marking closes nothing: {}",
                reasons.join("; ")
            ));
        }
    }
    warnings
}

/// Run the ported part of `corpus.py check`: the first error, or the counts
/// and warnings.
pub fn check(root: &Path) -> Result<Outcome, String> {
    let files = lean_files(root);
    let (loaded, counts) = validate(root, &files)?;
    let warnings = check_warnings(root, &loaded, &files);
    Ok(Outcome { counts, warnings })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prose_ids_follow_python_word_boundaries() {
        assert_eq!(prose_ids("see STMT-A-B, DEF-X."), ["STMT-A-B", "DEF-X"]);
        assert_eq!(prose_ids("STMT-FOO-BARx"), ["STMT-FOO"]);
        assert!(prose_ids("STMT-FOOx xSTMT-A STMT-").is_empty());
        assert!(prose_ids("(DISAMB-Ä1)").is_empty());
    }

    #[test]
    fn python_repr_and_dates() {
        assert_eq!(quote("it's"), "\"it's\"");
        assert_eq!(
            py_repr(Some(&serde_json::json!(["a", 1, null]))),
            "['a', 1, None]"
        );
        assert!(iso_date("2024-02-29"));
        assert!(!iso_date("2023-02-29"));
        assert!(!iso_date("2023-2-01"));
    }

    #[test]
    fn lean_imports_match_the_python_pattern() {
        let text =
            "import A\npublic import B.C\n  import D\n-- import E\npublic\n  import F\nimport\n G";
        assert_eq!(lean_imports(text), ["A", "B.C", "F", "G"]);
    }

    #[test]
    fn comments_are_blanked_with_newlines_kept() {
        assert_eq!(
            blank_lean_comments("a -- b\n/- c\n -/d"),
            "a     \n    \n   d"
        );
    }

    #[test]
    fn profile_types_and_terms() {
        assert!(profile_type("W → I → Prop"));
        assert!(!profile_type("Nat 2"));
        assert!(lean_term("Foo.bar.0"));
        assert!(!lean_term("0.Foo"));
    }
}
