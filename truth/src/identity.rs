//! Opaque corpus identity (owner decision 2026-11-07), ported from
//! `scripts/corpus_ids.py` and `scripts/identity_check.py`.
//!
//! Every record id is a uuid. A record converted from a readable id keeps it
//! as `legacy_id`, and its id is `uuid5(NAMESPACE, "<kind>:<legacy_id>")`.
//! Every record has a display `label`. Input accepts a uuid, a legacy id or a
//! label ([`Aliases::resolve`]); text output prints `label [uuid8]`
//! ([`Aliases::show`]); JSON keeps full uuids.

use fancy_regex::Regex;
use serde_json::{Map, Value};
use std::{
    collections::{BTreeSet, HashMap, HashSet},
    fs,
    path::{Path, PathBuf},
    sync::OnceLock,
};

type Obj = Map<String, Value>;

/// `corpus_ids.NAMESPACE`: fixed for the lifetime of the corpus.
const NAMESPACE: &str = "d140b0b2-f5a2-4598-9bf7-f3380fb20491";
/// `corpus_ids.LABEL_MAX` (Unicode code points, as Python `len`).
pub const LABEL_MAX: usize = 100;
/// `identity_check.CLEANUP`: the allowlist of the sense-tag rule.
const CLEANUP: &str = "docs/notes/label-cleanup.json";

/// Corpus directory -> record kind (the string hashed into the uuid5 name),
/// in `corpus_ids.KIND_DIRS` order.
pub const KIND_DIRS: &[(&str, &str)] = &[
    ("sources", "source"),
    ("statements", "statement"),
    ("claims", "claim"),
    ("inferences", "inference"),
    ("arguments", "argument"),
    ("relations", "relation"),
    ("candidates", "candidate"),
    ("results", "result"),
    ("definitions", "definition"),
    ("disambiguations", "disambiguation"),
    ("attempts", "attempt"),
    ("models", "model"),
    ("configurations", "configuration"),
    ("passages", "passage"),
];

// ---------------------------------------------------------------------------
// SHA-1 and uuid5 (RFC 4122 name-based ids; SHA-1 is used for identity, not
// for security, exactly as Python's `uuid.uuid5`).

fn sha1(message: &[u8]) -> [u8; 20] {
    let mut h: [u32; 5] = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0];
    let mut data = message.to_vec();
    data.push(0x80);
    while data.len() % 64 != 56 {
        data.push(0);
    }
    data.extend_from_slice(&((message.len() as u64) * 8).to_be_bytes());
    for chunk in data.chunks(64) {
        let mut w = [0u32; 80];
        for (i, word) in chunk.chunks(4).enumerate() {
            w[i] = u32::from_be_bytes([word[0], word[1], word[2], word[3]]);
        }
        for i in 16..80 {
            w[i] = (w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16]).rotate_left(1);
        }
        let [mut a, mut b, mut c, mut d, mut e] = h;
        for (i, &word) in w.iter().enumerate() {
            let (f, k) = match i {
                0..=19 => ((b & c) | (!b & d), 0x5A827999),
                20..=39 => (b ^ c ^ d, 0x6ED9EBA1),
                40..=59 => ((b & c) | (b & d) | (c & d), 0x8F1BBCDC),
                _ => (b ^ c ^ d, 0xCA62C1D6),
            };
            let next = a
                .rotate_left(5)
                .wrapping_add(f)
                .wrapping_add(e)
                .wrapping_add(k)
                .wrapping_add(word);
            e = d;
            d = c;
            c = b.rotate_left(30);
            b = a;
            a = next;
        }
        for (slot, value) in h.iter_mut().zip([a, b, c, d, e]) {
            *slot = slot.wrapping_add(value);
        }
    }
    let mut out = [0u8; 20];
    for (i, word) in h.iter().enumerate() {
        out[4 * i..4 * i + 4].copy_from_slice(&word.to_be_bytes());
    }
    out
}

fn uuid5(namespace: &str, name: &str) -> String {
    let hex: String = namespace.chars().filter(|c| *c != '-').collect();
    let mut input: Vec<u8> = (0..16)
        .map(|i| u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).expect("namespace is a uuid"))
        .collect();
    input.extend_from_slice(name.as_bytes());
    let mut bytes = sha1(&input);
    bytes[6] = (bytes[6] & 0x0f) | 0x50;
    bytes[8] = (bytes[8] & 0x3f) | 0x80;
    let hex: String = bytes[..16].iter().map(|b| format!("{b:02x}")).collect();
    format!(
        "{}-{}-{}-{}-{}",
        &hex[..8],
        &hex[8..12],
        &hex[12..16],
        &hex[16..20],
        &hex[20..32]
    )
}

/// `corpus_ids.legacy_uuid`: the id of the record of `kind` (singular) whose
/// legacy id is `legacy_id`.
pub fn legacy_uuid(kind: &str, legacy_id: &str) -> String {
    uuid5(NAMESPACE, &format!("{kind}:{legacy_id}"))
}

/// `corpus_ids.is_uuid`: a lower-case hyphenated uuid.
pub fn is_uuid(text: &str) -> bool {
    text.len() == 36
        && text.bytes().enumerate().all(|(i, b)| match i {
            8 | 13 | 18 | 23 => b == b'-',
            _ => b.is_ascii_digit() || (b'a'..=b'f').contains(&b),
        })
}

fn regex(cell: &'static OnceLock<Regex>, pattern: &str) -> &'static Regex {
    cell.get_or_init(|| Regex::new(pattern).expect("valid pattern"))
}

/// `corpus_ids.PROSE_UUID_RE`: uuids cited in prose.
pub fn prose_uuids(text: &str) -> Vec<&str> {
    static CELL: OnceLock<Regex> = OnceLock::new();
    let pattern = regex(
        &CELL,
        r"\b[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\b",
    );
    pattern
        .find_iter(text)
        .filter_map(Result::ok)
        .map(|found| found.as_str())
        .collect()
}

/// `corpus_ids.idlike_text`: readable-id-like or uuid-like text in a label.
pub fn idlike_text(label: &str) -> Vec<&str> {
    static CELL: OnceLock<Regex> = OnceLock::new();
    let pattern = regex(
        &CELL,
        r"\b[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)+\b|[0-9a-f]{8}-[0-9a-f]{4}",
    );
    pattern
        .find_iter(label)
        .filter_map(Result::ok)
        .map(|found| found.as_str())
        .collect()
}

/// Python `str.isspace` for one character.
fn py_space(c: char) -> bool {
    c.is_whitespace() || ('\u{1c}'..='\u{1f}').contains(&c)
}

/// `corpus_ids.sense_head`: the word(s) a definition's `term` names.
pub fn sense_head(term: &str) -> Option<String> {
    let before = term.split(['(', ':', ';', ',']).next().unwrap_or_default();
    let head = before
        .trim_matches(py_space)
        .trim_matches(['\'', '"', '‘', '’', '“', '”'])
        .to_lowercase();
    let words = head.split(py_space).filter(|w| !w.is_empty()).count();
    if head.is_empty() || words > 3 || !head.bytes().any(|b| b.is_ascii_lowercase()) {
        return None;
    }
    Some(head)
}

/// Python `repr` of a string (the subset labels and ids need).
fn repr(text: &str) -> String {
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
            c if (c as u32) < 0x20 || (0x7f..=0xa0).contains(&(c as u32)) => {
                out.push_str(&format!("\\x{:02x}", c as u32))
            }
            c => out.push(c),
        }
    }
    out.push(delimiter);
    out
}

fn value_repr(value: Option<&Value>) -> String {
    match value {
        None | Some(Value::Null) => "None".into(),
        Some(Value::String(text)) => repr(text),
        Some(Value::Bool(true)) => "True".into(),
        Some(Value::Bool(false)) => "False".into(),
        Some(other) => other.to_string(),
    }
}

/// Python `str` of a JSON value, for the few non-string fields a message prints.
fn value_str(value: Option<&Value>) -> String {
    match value {
        Some(Value::String(text)) => text.clone(),
        other => value_repr(other),
    }
}

// ---------------------------------------------------------------------------
// Senses

/// `corpus_ids.SenseIndex`: which disambiguated sense each definition is.
struct SenseIndex<'a> {
    definitions: &'a HashMap<String, &'a Obj>,
    senses_of: HashMap<String, Vec<(String, usize)>>,
    statements: HashMap<&'a str, &'a Obj>,
    arguments: HashMap<&'a str, &'a Obj>,
}

impl<'a> SenseIndex<'a> {
    fn new(
        definitions: &'a HashMap<String, &'a Obj>,
        disambiguations: &[(String, &Obj)],
        records: &'a [Entry],
    ) -> Self {
        let mut ordered: Vec<&(String, &Obj)> = disambiguations.iter().collect();
        ordered.sort_by(|a, b| {
            let key = |entry: &(String, &Obj)| {
                entry
                    .1
                    .get("legacy_id")
                    .and_then(Value::as_str)
                    .unwrap_or(&entry.0)
                    .to_owned()
            };
            key(a).cmp(&key(b))
        });
        let mut senses_of: HashMap<String, Vec<(String, usize)>> = HashMap::new();
        for (disambiguation_id, disambiguation) in ordered {
            let ids: Vec<Value> = match disambiguation.get("senses").and_then(Value::as_array) {
                Some(senses) if !senses.is_empty() => senses
                    .iter()
                    .filter_map(Value::as_object)
                    .map(|sense| sense.get("definition_id").cloned().unwrap_or(Value::Null))
                    .collect(),
                _ => disambiguation
                    .get("sense_definition_ids")
                    .and_then(Value::as_array)
                    .cloned()
                    .unwrap_or_default(),
            };
            let distinct = ids
                .iter()
                .enumerate()
                .filter(|(i, id)| !ids[..*i].contains(id))
                .count();
            if distinct < 2 {
                continue;
            }
            for (index, definition_id) in ids.iter().enumerate() {
                if let Some(definition_id) = definition_id.as_str() {
                    senses_of
                        .entry(definition_id.to_owned())
                        .or_default()
                        .push((disambiguation_id.clone(), index + 1));
                }
            }
        }
        Self {
            definitions,
            senses_of,
            statements: records
                .iter()
                .filter(|e| e.kind == "statement")
                .filter_map(|e| {
                    e.record
                        .get("id")
                        .and_then(Value::as_str)
                        .map(|id| (id, &e.record))
                })
                .collect(),
            arguments: records
                .iter()
                .filter(|e| e.kind == "argument")
                .filter_map(|e| {
                    e.record
                        .get("id")
                        .and_then(Value::as_str)
                        .map(|id| (id, &e.record))
                })
                .collect(),
        }
    }

    fn record_definitions<'b>(&'b self, record: &'b Obj, with_argument: bool) -> Vec<&'b str> {
        let list = |field| {
            record
                .get(field)
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .collect::<Vec<_>>()
        };
        let mut definitions = list("definition_ids");
        if record.contains_key("definition") && record.contains_key("term") {
            definitions.extend(record.get("id").and_then(Value::as_str));
        }
        if let Some(statement) = record
            .get("statement_id")
            .and_then(Value::as_str)
            .and_then(|id| self.statements.get(id))
        {
            definitions.extend(
                statement
                    .get("definition_ids")
                    .and_then(Value::as_array)
                    .into_iter()
                    .flatten()
                    .filter_map(Value::as_str),
            );
        }
        if with_argument
            && let Some(argument) = record
                .get("argument_id")
                .and_then(Value::as_str)
                .and_then(|id| self.arguments.get(id))
        {
            definitions.extend(self.record_definitions(argument, false));
        }
        if record.contains_key("conclusion_statement_id") {
            let mut ids = list("premise_statement_ids");
            ids.extend(list("commitment_statement_ids"));
            ids.extend(
                record
                    .get("conclusion_statement_id")
                    .and_then(Value::as_str),
            );
            for id in ids {
                if let Some(statement) = self.statements.get(id) {
                    definitions.extend(
                        statement
                            .get("definition_ids")
                            .and_then(Value::as_array)
                            .into_iter()
                            .flatten()
                            .filter_map(Value::as_str),
                    );
                }
            }
        }
        definitions
    }

    /// Heads of the disambiguated senses the record links.
    fn linked_heads(&self, _kind: &str, record: &Obj) -> Vec<String> {
        let linked = self.record_definitions(record, true);
        let mut heads = Vec::new();
        for definition_id in linked {
            if !self.senses_of.contains_key(definition_id) {
                continue;
            }
            let Some(definition) = self.definitions.get(definition_id) else {
                continue;
            };
            if let Some(head) = sense_head(&value_str(definition.get("term"))) {
                heads.push(head);
            }
        }
        heads
    }

    /// `SenseIndex.untagged`: linked-sense terms in `label` without their tag.
    fn untagged(&self, kind: &str, label: &str, record: &Obj) -> Vec<String> {
        if kind == "disambiguation" {
            return Vec::new();
        }
        let mut missing = BTreeSet::new();
        for head in self.linked_heads(kind, record) {
            let pattern = format!(r"(?i)(?<!\w){}(?!\w)", fancy_regex::escape(&head));
            if Regex::new(&pattern).is_ok_and(|re| re.is_match(label).unwrap_or(false)) {
                missing.insert(head);
            }
        }
        missing.into_iter().collect()
    }
}

// ---------------------------------------------------------------------------
// Identity rules

/// One record as `corpus_ids.iter_records` yields it: passages come from
/// their files, without the snapshot fields.
struct Entry {
    kind: &'static str,
    path: String,
    record: Obj,
}

fn json_files(directory: &Path) -> Vec<PathBuf> {
    let mut paths: Vec<PathBuf> = fs::read_dir(directory)
        .into_iter()
        .flatten()
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|ext| ext == "json") && path.is_file())
        .collect();
    paths.sort();
    paths
}

fn entries(root: &Path) -> Vec<Entry> {
    let mut out = Vec::new();
    for &(directory, kind) in KIND_DIRS {
        for path in json_files(&root.join("corpus").join(directory)) {
            let Ok(Value::Object(data)) =
                serde_json::from_str::<Value>(&fs::read_to_string(&path).unwrap_or_default())
            else {
                continue;
            };
            let relative = path
                .strip_prefix(root)
                .unwrap_or(&path)
                .to_string_lossy()
                .into_owned();
            if kind == "passage" {
                for passage in data
                    .get("passages")
                    .and_then(Value::as_array)
                    .into_iter()
                    .flatten()
                    .filter_map(Value::as_object)
                {
                    out.push(Entry {
                        kind,
                        path: relative.clone(),
                        record: passage.clone(),
                    });
                }
            } else {
                out.push(Entry {
                    kind,
                    path: relative,
                    record: data,
                });
            }
        }
    }
    out
}

/// `identity_check.sense_allowlist`.
fn sense_allowlist(root: &Path) -> HashSet<String> {
    let Ok(text) = fs::read_to_string(root.join(CLEANUP)) else {
        return HashSet::new();
    };
    let Ok(Value::Array(entries)) = serde_json::from_str::<Value>(&text) else {
        return HashSet::new();
    };
    entries
        .iter()
        .filter(|entry| {
            entry["flags"]
                .as_array()
                .is_some_and(|flags| flags.iter().any(|flag| flag == "untagged-sense"))
        })
        .filter_map(|entry| entry["id"].as_str().map(str::to_owned))
        .collect()
}

/// Case-insensitive label key. Python uses `str.casefold`; this lower-cases,
/// which differs only for characters whose case folding is not their
/// lower-case form (for example `ß`, folded to `ss`).
fn fold(label: &str) -> String {
    label.to_lowercase()
}

/// `identity_check._scan`: (errors, warnings), in Python's order.
pub fn scan(root: &Path) -> (Vec<String>, Vec<String>) {
    let mut errors = Vec::new();
    let mut warnings = Vec::new();
    let records = entries(root);
    let mut seen: HashMap<&str, &str> = HashMap::new();
    let mut legacy: HashMap<(&str, &str), &str> = HashMap::new();
    let mut labels: HashMap<(&str, String), &str> = HashMap::new();
    let mut definitions: HashMap<String, &Obj> = HashMap::new();
    let mut disambiguations: Vec<(String, &Obj)> = Vec::new();
    for entry in &records {
        let (kind, where_, record) = (entry.kind, entry.path.as_str(), &entry.record);
        let Some(record_id) = record
            .get("id")
            .and_then(Value::as_str)
            .filter(|id| is_uuid(id))
        else {
            errors.push(format!(
                "{where_}: {kind} id {} is not a uuid; ids are opaque uuids (python3 scripts/new_id.py), readable names go in label",
                value_repr(record.get("id"))
            ));
            continue;
        };
        if let Some(first) = seen.get(record_id) {
            errors.push(format!(
                "{where_}: id {record_id} is also the id of a record in {first}"
            ));
        }
        seen.insert(record_id, where_);
        match kind {
            "definition" => {
                definitions.insert(record_id.to_owned(), record);
            }
            "disambiguation" => match disambiguations.iter_mut().find(|(id, _)| id == record_id) {
                Some(slot) => slot.1 = record,
                None => disambiguations.push((record_id.to_owned(), record)),
            },
            _ => {}
        }
        match record.get("legacy_id") {
            None | Some(Value::Null) => {}
            Some(alias) => match alias.as_str() {
                Some(alias) if !alias.is_empty() && legacy_uuid(kind, alias) == record_id => {
                    if let Some(first) = legacy.get(&(kind, alias)) {
                        errors.push(format!(
                            "{where_}: legacy_id {alias} is also used by {first}"
                        ));
                    } else {
                        legacy.insert((kind, alias), where_);
                    }
                }
                _ => errors.push(format!(
                    "{where_}: legacy_id {} is not the alias {record_id} was made from",
                    value_repr(Some(alias))
                )),
            },
        }
        let Some(label) = record
            .get("label")
            .and_then(Value::as_str)
            .filter(|label| !label.trim_matches(py_space).is_empty())
        else {
            errors.push(format!("{where_}: {kind} {record_id} has no label"));
            continue;
        };
        if label.chars().count() > LABEL_MAX {
            errors.push(format!(
                "{where_}: label is longer than {LABEL_MAX} characters"
            ));
        }
        if label != label.trim_matches(py_space) {
            errors.push(format!("{where_}: label has surrounding whitespace"));
        }
        let found = idlike_text(label);
        if !found.is_empty() {
            errors.push(format!(
                "{where_}: label contains id-like text {}; labels name the thing",
                found.join(", ")
            ));
        }
        match labels.get(&(kind, fold(label))) {
            Some(first) => errors.push(format!(
                "{where_}: label {} is also the label of {first}; labels are unique per kind",
                repr(label)
            )),
            None => {
                labels.insert((kind, fold(label)), where_);
            }
        }
    }
    let senses = SenseIndex::new(&definitions, &disambiguations, &records);
    let allowed = sense_allowlist(root);
    for entry in &records {
        let record = &entry.record;
        let (Some(label), Some(record_id)) = (
            record.get("label").and_then(Value::as_str),
            record
                .get("id")
                .and_then(Value::as_str)
                .filter(|id| is_uuid(id)),
        ) else {
            continue;
        };
        let missing = senses.untagged(entry.kind, label, record);
        if missing.is_empty() {
            continue;
        }
        let message = format!(
            "{}: label {} uses {} without its sense tag (e.g. PRIOR_1) although the record links a disambiguated sense",
            entry.path,
            repr(label),
            missing.join(", ")
        );
        let migrated = record.get("legacy_id").is_some_and(|alias| match alias {
            Value::Null | Value::Bool(false) => false,
            Value::String(text) => !text.is_empty(),
            Value::Array(items) => !items.is_empty(),
            Value::Object(items) => !items.is_empty(),
            Value::Number(number) => number.as_f64() != Some(0.0),
            Value::Bool(true) => true,
        });
        if migrated && allowed.contains(record_id) {
            warnings.push(format!(
                "{message} (allowlisted in docs/notes/label-cleanup.json)"
            ));
        } else {
            errors.push(message);
        }
    }
    (errors, warnings)
}

/// `identity_check.validate_identity`: the first error, with a count of the rest.
pub fn validate(root: &Path) -> Result<(), String> {
    let (errors, _) = scan(root);
    match errors.as_slice() {
        [] => Ok(()),
        [only] => Err(only.clone()),
        [first, rest @ ..] => Err(format!("{first} (and {} more identity errors)", rest.len())),
    }
}

/// `label_cleanup.passing`: entries that have become safe to remove from the
/// mechanical-label exception list. Keep their warning order equal to the JSON list.
fn passing_cleanup_warnings(root: &Path) -> Vec<String> {
    let Ok(contents) = fs::read_to_string(root.join(CLEANUP)) else {
        return Vec::new();
    };
    let Ok(Value::Array(cleanup)) = serde_json::from_str::<Value>(&contents) else {
        return Vec::new();
    };
    let records = entries(root);
    let mut by_id: HashMap<&str, (&str, &Obj)> = HashMap::new();
    let mut definitions: HashMap<String, &Obj> = HashMap::new();
    let mut disambiguations: Vec<(String, &Obj)> = Vec::new();
    for entry in &records {
        let Some(id) = entry.record.get("id").and_then(Value::as_str) else {
            continue;
        };
        by_id.insert(id, (entry.kind, &entry.record));
        match entry.kind {
            "definition" => {
                definitions.insert(id.to_owned(), &entry.record);
            }
            "disambiguation" => disambiguations.push((id.to_owned(), &entry.record)),
            _ => {}
        }
    }
    let senses = SenseIndex::new(&definitions, &disambiguations, &records);
    let mut warnings = Vec::new();
    for entry in cleanup {
        let (Some(id), Some(kind)) = (
            entry.get("id").and_then(Value::as_str),
            entry.get("kind").and_then(Value::as_str),
        ) else {
            continue;
        };
        let reason = match by_id.get(id) {
            None => Some("the record no longer exists"),
            Some((record_kind, record)) => {
                let label = record.get("label").and_then(Value::as_str).unwrap_or("");
                let rewritten = entry.get("label").and_then(Value::as_str) != Some(label);
                let only_sense = match entry.get("flags") {
                    None => true,
                    Some(Value::Array(flags)) => flags.iter().all(|flag| flag == "untagged-sense"),
                    _ => false,
                };
                if senses.untagged(record_kind, label, record).is_empty()
                    && (rewritten || only_sense)
                {
                    if rewritten {
                        Some("label rewritten")
                    } else {
                        Some("sense tags complete")
                    }
                } else {
                    None
                }
            }
        };
        if let Some(reason) = reason {
            warnings.push(format!(
                "{kind} {id}: label clean-up entry passes ({reason}); remove it from {CLEANUP}"
            ));
        }
    }
    warnings
}

/// `identity_check.identity_warnings`.
pub fn warnings(root: &Path) -> Vec<String> {
    let mut warnings = scan(root).1;
    warnings.extend(passing_cleanup_warnings(root));
    warnings
}

// ---------------------------------------------------------------------------
// Aliases

/// uuid / legacy id / label -> uuid lookup over loaded records
/// (`corpus_ids.Aliases`). Kinds are corpus directory names.
#[derive(Default)]
pub struct Aliases {
    kinds_of: HashMap<String, BTreeSet<String>>,
    label_of: HashMap<String, String>,
    legacy_of: HashMap<String, String>,
    by_legacy: HashMap<String, Vec<(String, String)>>,
    by_label: HashMap<String, Vec<(String, String)>>,
    by_folded_label: HashMap<String, Vec<(String, String)>>,
}

/// A lookup that names no record, or more than one.
#[derive(Debug)]
pub enum Unresolved {
    Unknown,
    Ambiguous(Vec<(String, String)>),
}

impl Aliases {
    pub fn add(&mut self, kind: &str, record: &Obj) {
        let Some(id) = record.get("id").and_then(Value::as_str) else {
            return;
        };
        self.kinds_of
            .entry(id.to_owned())
            .or_default()
            .insert(kind.to_owned());
        let pair = (kind.to_owned(), id.to_owned());
        if let Some(legacy) = record
            .get("legacy_id")
            .and_then(Value::as_str)
            .filter(|s| !s.is_empty())
        {
            self.legacy_of.insert(id.to_owned(), legacy.to_owned());
            self.by_legacy
                .entry(legacy.to_owned())
                .or_default()
                .push(pair.clone());
        }
        if let Some(label) = record
            .get("label")
            .and_then(Value::as_str)
            .filter(|s| !s.is_empty())
        {
            self.label_of.insert(id.to_owned(), label.to_owned());
            self.by_label
                .entry(label.to_owned())
                .or_default()
                .push(pair.clone());
            self.by_folded_label
                .entry(fold(label))
                .or_default()
                .push(pair);
        }
    }

    /// (kind, uuid) pairs `token` names, by the first rule that matches:
    /// uuid, legacy id, exact label, case-insensitive label.
    pub fn candidates(&self, token: &str, kinds: Option<&[&str]>) -> Vec<(String, String)> {
        let keep = |pairs: &mut dyn Iterator<Item = (String, String)>| -> Vec<(String, String)> {
            pairs
                .filter(|(kind, _)| kinds.is_none_or(|kinds| kinds.contains(&kind.as_str())))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect()
        };
        if let Some(found) = self.kinds_of.get(token) {
            let found = keep(&mut found.iter().map(|kind| (kind.clone(), token.to_owned())));
            if !found.is_empty() {
                return found;
            }
        }
        for found in [
            self.by_legacy.get(token),
            self.by_label.get(token),
            self.by_folded_label.get(&fold(token)),
        ]
        .into_iter()
        .flatten()
        {
            let found = keep(&mut found.iter().cloned());
            if !found.is_empty() {
                return found;
            }
        }
        Vec::new()
    }

    /// The uuid `token` names.
    pub fn resolve(&self, token: &str, kinds: Option<&[&str]>) -> Result<String, Unresolved> {
        let found = self.candidates(token, kinds);
        let ids: BTreeSet<&String> = found.iter().map(|(_, id)| id).collect();
        match ids.len() {
            0 => Err(Unresolved::Unknown),
            1 => Ok(ids.into_iter().next().expect("one id").clone()),
            _ => Err(Unresolved::Ambiguous(found)),
        }
    }

    /// Text form: `label [uuid8]`; an unknown or non-uuid id prints as itself.
    pub fn show(&self, id: &str) -> String {
        match self.label_of.get(id).or_else(|| self.legacy_of.get(id)) {
            Some(label) if is_uuid(id) => format!("{label} [{}]", &id[..8]),
            _ => id.to_owned(),
        }
    }

    /// The legacy id of `id`, or `id` itself (`Aliases.legacy`).
    pub fn legacy<'a>(&'a self, id: &'a str) -> &'a str {
        self.legacy_of.get(id).map_or(id, String::as_str)
    }

    pub fn label(&self, id: &str) -> Option<&str> {
        self.label_of.get(id).map(String::as_str)
    }

    /// `corpus.humanize`: every uuid in `text` as `label [uuid8]`, except a
    /// uuid that is a command argument (`materialize <uuid>`); unknown uuids
    /// stay as they are.
    pub fn humanize(&self, text: &str) -> String {
        static CELL: OnceLock<Regex> = OnceLock::new();
        let pattern = regex(
            &CELL,
            r"(?<!materialize )\b[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\b",
        );
        let mut out = String::with_capacity(text.len());
        let mut last = 0;
        for found in pattern.find_iter(text).flatten() {
            out.push_str(&text[last..found.start()]);
            out.push_str(&self.show(found.as_str()));
            last = found.end();
        }
        out.push_str(&text[last..]);
        out
    }

    /// The candidates of an ambiguous lookup, for a message.
    pub fn describe(&self, candidates: &[(String, String)]) -> String {
        candidates
            .iter()
            .map(|(kind, id)| format!("{kind} {}", self.show(id)))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uuid5_matches_python() {
        assert_eq!(
            legacy_uuid("statement", "STMT-CATHOLICISM-TRUE"),
            "53964cbe-5831-5812-af33-4d87896d47a7"
        );
        assert_eq!(
            legacy_uuid("statement", "STMT-EXCLUDED-MIDDLE"),
            "ee4ab504-c8fe-59bc-bc96-7cbeefed6410"
        );
        let hex: String = sha1(b"abc").iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(hex, "a9993e364706816aba3e25717850c26c9cd0d89d");
        assert!(is_uuid("53964cbe-5831-5812-af33-4d87896d47a7"));
        assert!(!is_uuid("53964CBE-5831-5812-af33-4d87896d47a7"));
    }

    #[test]
    fn labels_and_heads() {
        assert_eq!(
            idlike_text("from STMT-FOO and Q11-OLD"),
            ["STMT-FOO", "Q11-OLD"]
        );
        assert_eq!(idlike_text("see 53964cbe-5831 here"), ["53964cbe-5831"]);
        assert!(idlike_text("self-evident truth").is_empty());
        assert_eq!(sense_head("Prior (in nature): x").as_deref(), Some("prior"));
        assert_eq!(sense_head("“Being”").as_deref(), Some("being"));
        assert_eq!(sense_head("a b c d"), None);
        assert_eq!(sense_head("ABC 12"), Some("abc 12".into()));
        assert_eq!(sense_head("12"), None);
    }

    #[test]
    fn aliases_resolve_in_order() {
        let mut aliases = Aliases::default();
        let record = |id: &str, legacy: &str, label: &str| {
            serde_json::json!({"id": id, "legacy_id": legacy, "label": label})
                .as_object()
                .cloned()
                .unwrap()
        };
        let a = legacy_uuid("statement", "STMT-A");
        let b = legacy_uuid("argument", "A");
        aliases.add("statements", &record(&a, "STMT-A", "Alpha"));
        aliases.add("arguments", &record(&b, "A", "alpha"));
        assert_eq!(aliases.resolve(&a, None).unwrap(), a);
        assert_eq!(aliases.resolve("STMT-A", None).unwrap(), a);
        assert_eq!(aliases.resolve("Alpha", None).unwrap(), a);
        assert_eq!(aliases.resolve("alpha", None).unwrap(), b);
        assert!(matches!(
            aliases.resolve("ALPHA", None),
            Err(Unresolved::Ambiguous(_))
        ));
        assert_eq!(aliases.resolve("ALPHA", Some(&["statements"])).unwrap(), a);
        assert!(matches!(
            aliases.resolve("nothing", None),
            Err(Unresolved::Unknown)
        ));
        assert_eq!(aliases.show(&a), format!("Alpha [{}]", &a[..8]));
        assert_eq!(aliases.show("other"), "other");
        assert_eq!(
            aliases.humanize(&format!("x {a}, materialize {a}, {b}0")),
            format!("x Alpha [{}], materialize {a}, {b}0", &a[..8])
        );
    }
}
