//! Argument context packs, ported from `scripts/argument_context.py`
//! (`context_pack`, `format_context`, `resolve_target`) and `scripts/corpus.py
//! context`.
//!
//! The frozen Lean statement text is read from each result's Challenge module
//! and import closures from the Solution modules' `import` lines, as Python
//! does. Closure, depth and routes come from the frontier report
//! ([`FrontierView`]); the related ranking from [`crate::related`]. Navigation
//! only: nothing is stored or certified.

use crate::{
    Corpus,
    dossier::{FrontierView, configuration_statements},
    pyfmt,
    related::Match,
};
use serde::Serialize;
use serde_json::{Map, Value, json};
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    path::{Path, PathBuf},
};

pub const DEFAULT_LIMIT: i64 = 6;
pub const DEFAULT_RELATED: i64 = 8;
const WIDTH: usize = 150;
const OVERFLOW: usize = 40;

type Record = Map<String, Value>;

fn text<'a>(record: &'a Record, field: &str) -> &'a str {
    record
        .get(field)
        .and_then(Value::as_str)
        .unwrap_or_default()
}

fn list<'a>(record: &'a Record, field: &str) -> Vec<&'a str> {
    record
        .get(field)
        .and_then(Value::as_array)
        .map(|items| items.iter().filter_map(Value::as_str).collect())
        .unwrap_or_default()
}

fn get(record: &Record, field: &str) -> Value {
    record.get(field).cloned().unwrap_or(Value::Null)
}

/// `TruthCore.A.B` -> `TruthCore/A/B.lean`.
pub fn module_path(module: &str) -> PathBuf {
    PathBuf::from(format!("{}.lean", module.replace('.', "/")))
}

fn is_line_start(text: &str, index: usize) -> bool {
    index == 0 || text.as_bytes()[index - 1] == b'\n'
}

fn skip_space(text: &str, index: usize) -> usize {
    index
        + text[index..]
            .char_indices()
            .find(|(_, c)| !pyfmt::is_space(*c))
            .map_or(text.len() - index, |(offset, _)| offset)
}

/// Match `word\s+` (at least one whitespace character) at `index`.
fn word_space(text: &str, index: usize, word: &str) -> Option<usize> {
    let rest = text.get(index..)?.strip_prefix(word)?;
    let after = text.len() - rest.len();
    let end = skip_space(text, after);
    (end > after).then_some(end)
}

fn non_space(text: &str, index: usize) -> Option<(usize, usize)> {
    let end = text[index..]
        .char_indices()
        .find(|(_, c)| pyfmt::is_space(*c))
        .map_or(text.len(), |(offset, _)| index + offset);
    (end > index).then_some((index, end))
}

/// Python `IMPORT.findall` (`^(?:public\s+)?import\s+(\S+)`, multiline).
pub fn import_names(text: &str) -> Vec<String> {
    let mut names = Vec::new();
    let mut index = 0;
    while index < text.len() {
        if is_line_start(text, index) {
            let body = word_space(text, index, "public")
                .and_then(|after| word_space(text, after, "import"))
                .or_else(|| word_space(text, index, "import"));
            if let Some((start, end)) = body.and_then(|body| non_space(text, body)) {
                names.push(text[start..end].to_owned());
                index = end;
                continue;
            }
        }
        index += text[index..].chars().next().map_or(1, char::len_utf8);
    }
    names
}

const BOUNDARIES: &[&str] = &[
    "/--",
    "@[",
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "structure",
    "inductive",
    "instance",
    "end",
    "namespace",
    "section",
    "open",
    "variable",
    "noncomputable",
    "private",
    "public",
    "protected",
    "--",
];

fn boundary_at(text: &str, index: usize) -> bool {
    let rest = &text[index..];
    BOUNDARIES.iter().any(|word| {
        if matches!(*word, "/--" | "@[" | "--") {
            rest.starts_with(word)
        } else {
            rest.strip_prefix(word)
                .and_then(|after| after.chars().next())
                .is_some_and(pyfmt::is_space)
        }
    })
}

/// Python `DECLARATION` at a line start: the declared name's span.
fn declaration_at(text: &str, index: usize) -> Option<(usize, usize)> {
    let mut starts = vec![index];
    if text[index..].starts_with("@[")
        && let Some(close) = text[index + 2..].find(']')
    {
        starts.insert(0, skip_space(text, index + 2 + close + 1));
    }
    starts.into_iter().find_map(|start| {
        let modifiers = ["private", "public", "protected"]
            .iter()
            .filter_map(|word| word_space(text, start, word))
            .chain([start]);
        modifiers.into_iter().find_map(|at| {
            ["theorem", "lemma"]
                .iter()
                .find_map(|word| word_space(text, at, word))
                .and_then(|name| non_space(text, name))
        })
    })
}

/// A theorem's verbatim statement text up to `:=` (Python `theorem_blocks`).
#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct TheoremBlock {
    pub name: String,
    pub line: usize,
    pub statement: String,
}

pub fn theorem_blocks_in(text: &str) -> Vec<TheoremBlock> {
    let mut blocks = Vec::new();
    let mut index = 0;
    while index < text.len() {
        if is_line_start(text, index)
            && let Some((name_start, name_end)) = declaration_at(text, index)
        {
            let stop = text[name_end..].find(":=").map(|offset| name_end + offset);
            // A declaration boundary on a later line before `:=` ends the search.
            let bounded = stop.is_some_and(|stop| {
                text[name_end..stop]
                    .match_indices('\n')
                    .any(|(offset, _)| boundary_at(text, name_end + offset + 1))
            });
            if let Some(stop) = stop
                && !bounded
            {
                blocks.push(TheoremBlock {
                    name: text[name_start..name_end].to_owned(),
                    line: text[..index].matches('\n').count() + 1,
                    statement: pyfmt::rstrip(&text[index..stop]).to_owned(),
                });
            }
            index = name_end;
            continue;
        }
        index += text[index..].chars().next().map_or(1, char::len_utf8);
    }
    blocks
}

/// Lean source reads, cached per module for one pack.
struct Lean<'a> {
    root: &'a Path,
    imports: RefCell<HashMap<String, Vec<String>>>,
}

impl<'a> Lean<'a> {
    fn read(&self, module: &str) -> Option<String> {
        let path = self.root.join(module_path(module));
        path.is_file()
            .then(|| std::fs::read_to_string(path).ok())
            .flatten()
    }

    fn imports(&self, module: &str) -> Vec<String> {
        if let Some(found) = self.imports.borrow().get(module) {
            return found.clone();
        }
        let found = self
            .read(module)
            .map_or_else(Vec::new, |text| import_names(&text));
        self.imports
            .borrow_mut()
            .insert(module.to_owned(), found.clone());
        found
    }

    /// Repository modules transitively imported, with BFS depth, in discovery order.
    fn closure(&self, module: &str) -> Vec<(String, usize)> {
        let mut seen: Vec<(String, usize)> = Vec::new();
        let mut known: HashSet<String> = HashSet::new();
        let mut frontier = vec![module.to_owned()];
        let mut depth = 0;
        while !frontier.is_empty() {
            depth += 1;
            let mut following = Vec::new();
            for current in &frontier {
                for imported in self.imports(current) {
                    if imported.starts_with("TruthCore")
                        && imported != module
                        && known.insert(imported.clone())
                    {
                        seen.push((imported.clone(), depth));
                        following.push(imported);
                    }
                }
            }
            frontier = following;
        }
        seen
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct ResultSummary {
    pub result_id: String,
    pub argument_id: String,
    pub theorem: Value,
    pub status: Value,
    pub transcription: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct ConcludedBy {
    pub argument_id: String,
    pub premise_statement_ids: Value,
    pub results: Vec<ResultSummary>,
}

#[derive(Debug, Clone, Serialize)]
pub struct StatementEntry {
    pub statement_id: String,
    pub paraphrase: Value,
    pub lean_declaration: Value,
    pub closed: Option<String>,
    pub open_depth: Value,
    pub established: bool,
    pub reaches_root: bool,
    pub concluded_by: Vec<ConcludedBy>,
}

#[derive(Debug, Clone, Serialize)]
pub struct ReusedResult {
    pub module: String,
    pub depth: usize,
    #[serde(flatten)]
    pub result: ResultSummary,
    pub graph_linked: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct Companion {
    #[serde(flatten)]
    pub block: TheoremBlock,
    pub comparator_checked: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct LeanEntry {
    pub result_id: String,
    pub theorem: String,
    pub status: Value,
    pub transcription: bool,
    pub challenge_path: String,
    pub solution_path: String,
    pub advertised_statement: Option<TheoremBlock>,
    pub companion_theorems: Vec<Companion>,
    pub permitted_axioms: Value,
    pub direct_imports: Vec<String>,
    pub reused_results: Vec<ReusedResult>,
    pub lean_consumers: Vec<String>,
    pub lean_consumers_depth2: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Neighbour {
    #[serde(flatten)]
    pub result: ResultSummary,
    pub shared_modules: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Inference {
    pub inference_id: String,
    pub rule: Value,
    pub input_statement_ids: Value,
    pub assumption_statement_ids: Value,
    pub discharged_statement_ids: Value,
    pub output_statement_id: Value,
}

#[derive(Debug, Clone, Serialize)]
pub struct Downstream {
    pub argument_id: String,
    pub conclusion_statement_id: Value,
    pub results: Vec<ResultSummary>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Sibling {
    pub argument_id: String,
    pub shared_premise_statement_ids: Vec<String>,
    pub conclusion_statement_id: Value,
    pub results: Vec<ResultSummary>,
}

#[derive(Debug, Clone, Serialize)]
pub struct RelatedStatement {
    pub statement_id: String,
    pub reasons: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct ModelEntry {
    pub model_id: String,
    pub statement_id: String,
    pub value: Value,
    pub theorem: Value,
    pub role: &'static str,
}

#[derive(Debug, Clone, Serialize)]
pub struct RivalRelation {
    pub relation_id: String,
    pub subject_id: Value,
    pub predicate: Value,
    pub object_id: Value,
    pub note: Value,
}

#[derive(Debug, Clone, Serialize)]
pub struct ConfigurationEntry {
    pub configuration_id: String,
    pub semantics_id: Value,
    pub statement_ids: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct AttemptEntry {
    pub attempt_id: String,
    pub date: Value,
    pub kind: Value,
    pub outcome: Value,
    pub statement_ids: Vec<String>,
    pub summary: Value,
    pub blocker: Value,
}

#[derive(Debug, Clone, Serialize)]
pub struct CandidateEntry {
    pub candidate_id: String,
    pub status: Value,
    pub priority: Value,
    pub mentions: Vec<String>,
    pub goal: Value,
}

#[derive(Debug, Clone, Serialize)]
pub struct Unresolved {
    pub open_premise_statement_ids: Vec<String>,
    pub open_premises_without_other_route: Vec<String>,
    pub blocked_or_failed_attempt_ids: Vec<String>,
    pub transcription_result_ids: Vec<String>,
    pub unchecked_companion_theorems: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Term {
    pub id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub definition: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub resolution: Option<Value>,
}

/// One argument's context pack; field order follows Python `context_pack`.
#[derive(Debug, Clone, Serialize)]
pub struct ContextPack {
    pub argument_id: String,
    pub meaning: Value,
    pub root: Option<String>,
    pub conclusion: StatementEntry,
    pub premises: Vec<StatementEntry>,
    pub commitments: Vec<StatementEntry>,
    pub inferences: Vec<Inference>,
    pub lean: Vec<LeanEntry>,
    pub downstream_arguments: Vec<Downstream>,
    pub premise_sibling_arguments: Vec<Sibling>,
    pub lean_neighbours: Vec<Neighbour>,
    pub related_statements: Vec<RelatedStatement>,
    pub same_bundle_argument_ids: Vec<String>,
    pub routes: Vec<Value>,
    pub models: Vec<ModelEntry>,
    pub rival_relations: Vec<RivalRelation>,
    pub configurations: Vec<ConfigurationEntry>,
    pub attempts: Vec<AttemptEntry>,
    pub candidates: Vec<CandidateEntry>,
    pub unresolved: Unresolved,
    pub route_open_leaves: Vec<String>,
    pub attempt_cited_ids: Vec<String>,
    pub definitions: Vec<Term>,
    pub disambiguations: Vec<Term>,
}

/// Why a target does not name exactly one argument.
#[derive(Debug, PartialEq, Eq)]
pub enum TargetError {
    Unknown(String),
    Ambiguous(String),
}

impl TargetError {
    pub fn message(&self) -> &str {
        match self {
            Self::Unknown(message) | Self::Ambiguous(message) => message,
        }
    }
}

/// An argument ID, a result ID, or a statement concluded by exactly one argument.
pub fn resolve_target(corpus: &Corpus, target: &str) -> Result<String, TargetError> {
    if corpus.get("arguments", target).is_some() {
        return Ok(target.to_owned());
    }
    if let Some(result) = corpus.get("results", target) {
        return Ok(text(&result.fields, "argument_id").to_owned());
    }
    let concluding: Vec<&str> = corpus
        .records_by_id("arguments")
        .filter(|(_, record)| text(&record.fields, "conclusion_statement_id") == target)
        .map(|(id, _)| id)
        .collect();
    match concluding.as_slice() {
        [one] => Ok((*one).to_owned()),
        [] => Err(TargetError::Unknown(format!(
            "unknown argument, result or concluded statement: {target}"
        ))),
        several => Err(TargetError::Ambiguous(format!(
            "{target} is concluded by several arguments; choose one: {}",
            several.join(", ")
        ))),
    }
}

/// Run of `[A-Za-z0-9-]` characters in which Python `ID_TOKEN` matches.
fn id_tokens(value: &str) -> BTreeSet<String> {
    let in_run = |c: char| c.is_ascii_alphanumeric() || c == '-';
    value
        .split(|c: char| !in_run(c))
        .filter(|run| {
            let mut parts = run.split('-');
            let first = parts.next().unwrap_or_default();
            let rest: Vec<&str> = parts.collect();
            first.starts_with(|c: char| c.is_ascii_uppercase())
                && first
                    .chars()
                    .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit())
                && !rest.is_empty()
                && rest.iter().all(|part| {
                    !part.is_empty()
                        && part
                            .chars()
                            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit())
                })
        })
        .map(str::to_owned)
        .collect()
}

/// Python's candidate pattern: any of `ids` not adjoining `[A-Z0-9-]`, longest first.
fn mentions(value: &str, ids: &[&str]) -> Vec<String> {
    let blocked = |c: u8| c.is_ascii_uppercase() || c.is_ascii_digit() || c == b'-';
    let bytes = value.as_bytes();
    let mut found = BTreeSet::new();
    let mut index = 0;
    while index < bytes.len() {
        if (index == 0 || !blocked(bytes[index - 1]))
            && let Some(id) = ids.iter().find(|id| {
                value[index..].starts_with(**id)
                    && bytes
                        .get(index + id.len())
                        .is_none_or(|next| !blocked(*next))
            })
        {
            found.insert((*id).to_owned());
            index += id.len();
            continue;
        }
        index += 1;
        while index < bytes.len() && !value.is_char_boundary(index) {
            index += 1;
        }
    }
    found.into_iter().collect()
}

fn role(sid: &str, premises: &[&str], conclusion: &str) -> &'static str {
    if sid == conclusion {
        "conclusion"
    } else if premises.contains(&sid) {
        "premise"
    } else {
        "commitment"
    }
}

/// Python `context_pack` without proof-term inspection.
pub fn context_pack(
    root: &Path,
    corpus: &Corpus,
    report: &FrontierView,
    argument_id: &str,
    related: &[Match],
) -> ContextPack {
    let lean_files = Lean {
        root,
        imports: RefCell::new(HashMap::new()),
    };
    let statements: HashMap<&str, &Record> = corpus
        .records("statements")
        .into_iter()
        .map(|r| (text(r, "id"), r))
        .collect();
    let arguments_in_order = corpus.records("arguments");
    let arguments: BTreeMap<&str, &Record> = arguments_in_order
        .iter()
        .map(|r| (text(r, "id"), *r))
        .collect();
    let all_results = corpus.records("results");
    let mut results_by_argument: HashMap<&str, Vec<&Record>> = HashMap::new();
    for result in &all_results {
        results_by_argument
            .entry(text(result, "argument_id"))
            .or_default()
            .push(result);
    }
    let argument = arguments[argument_id];
    let conclusion = text(argument, "conclusion_statement_id");
    let premises = list(argument, "premise_statement_ids");
    let commitments = list(argument, "commitment_statement_ids");
    let focus: BTreeSet<&str> = premises
        .iter()
        .chain(&commitments)
        .copied()
        .chain([conclusion])
        .collect();
    let transcriptions = &report.transcription_results;

    let summary = |result: &Record| ResultSummary {
        result_id: text(result, "id").to_owned(),
        argument_id: text(result, "argument_id").to_owned(),
        theorem: get(result, "theorem"),
        status: get(result, "status"),
        transcription: transcriptions.contains_key(text(result, "id")),
    };
    let summaries = |aid: &str| -> Vec<ResultSummary> {
        results_by_argument
            .get(aid)
            .into_iter()
            .flatten()
            .map(|r| summary(r))
            .collect()
    };
    let concluded_by = |sid: &str| -> Vec<ConcludedBy> {
        arguments
            .iter()
            .filter(|(aid, other)| {
                text(other, "conclusion_statement_id") == sid && **aid != argument_id
            })
            .map(|(aid, other)| ConcludedBy {
                argument_id: (*aid).to_owned(),
                premise_statement_ids: get(other, "premise_statement_ids"),
                results: summaries(aid),
            })
            .collect()
    };
    let statement_entry = |sid: &str| {
        let record = statements.get(sid);
        let closed = report.closed_statements.get(sid).cloned();
        let open_depth = match (report.item(sid), &closed) {
            (Some(item), None) => item["depth"].clone(),
            (Some(item), Some(closure)) if closure.is_empty() => item["depth"].clone(),
            _ => Value::Null,
        };
        StatementEntry {
            statement_id: sid.to_owned(),
            paraphrase: record.map_or(Value::Null, |r| get(r, "paraphrase")),
            lean_declaration: record.map_or(Value::Null, |r| get(r, "lean_declaration")),
            closed,
            open_depth,
            established: report.established_statements.contains(sid),
            reaches_root: report.reaching_root_statements.contains(sid),
            concluded_by: concluded_by(sid),
        }
    };

    // Lean: authoritative type, companions and import reuse.
    let results: Vec<&Record> = results_by_argument
        .get(argument_id)
        .cloned()
        .unwrap_or_default();
    let mut module_to_result: HashMap<&str, &Record> = HashMap::new();
    for result in &all_results {
        for key in ["solution_module", "challenge_module"] {
            if pyfmt::truthy(result.get(key)) {
                module_to_result.insert(text(result, key), result);
            }
        }
    }
    let premise_set: HashSet<&str> = premises.iter().chain(&commitments).copied().collect();
    let mut lean = Vec::new();
    for result in &results {
        let theorem = text(result, "theorem");
        let challenge = text(result, "challenge_module");
        let solution = text(result, "solution_module");
        let blocks = lean_files
            .read(challenge)
            .map_or_else(Vec::new, |source| theorem_blocks_in(&source));
        let short_name = theorem.rsplit('.').next().unwrap_or_default();
        let advertised = blocks
            .iter()
            .find(|block| block.name == short_name)
            .cloned();
        let comparator: Record = if pyfmt::truthy(result.get("comparator_config")) {
            std::fs::read(root.join(text(result, "comparator_config")))
                .ok()
                .and_then(|bytes| serde_json::from_slice(&bytes).ok())
                .unwrap_or_default()
        } else {
            Record::new()
        };
        let checked: HashSet<&str> = list(&comparator, "theorem_names")
            .into_iter()
            .map(|name| name.rsplit('.').next().unwrap_or_default())
            .collect();
        let closure = if solution.is_empty() {
            Vec::new()
        } else {
            lean_files.closure(solution)
        };
        let mut reused: Vec<ReusedResult> = closure
            .iter()
            .filter_map(|(module, depth)| {
                let other = module_to_result.get(module.as_str())?;
                (text(other, "id") != text(result, "id")).then(|| ReusedResult {
                    module: module.clone(),
                    depth: *depth,
                    result: summary(other),
                    graph_linked: arguments
                        .get(text(other, "argument_id"))
                        .is_some_and(|a| premise_set.contains(text(a, "conclusion_statement_id"))),
                })
            })
            .collect();
        reused.sort_by(|a, b| (a.depth, &a.result.result_id).cmp(&(b.depth, &b.result.result_id)));
        let consumers: BTreeSet<String> = all_results
            .iter()
            .filter(|other| {
                text(other, "id") != text(result, "id")
                    && pyfmt::truthy(other.get("solution_module"))
                    && !solution.is_empty()
                    && lean_files
                        .imports(text(other, "solution_module"))
                        .iter()
                        .any(|imported| imported == solution)
            })
            .map(|other| text(other, "id").to_owned())
            .collect();
        let consumer_modules: HashSet<&str> = all_results
            .iter()
            .filter(|r| consumers.contains(text(r, "id")))
            .map(|r| text(r, "solution_module"))
            .collect();
        let consumers_depth2: BTreeSet<String> = all_results
            .iter()
            .filter(|other| {
                text(other, "id") != text(result, "id")
                    && !consumers.contains(text(other, "id"))
                    && pyfmt::truthy(other.get("solution_module"))
                    && lean_files
                        .imports(text(other, "solution_module"))
                        .iter()
                        .any(|imported| consumer_modules.contains(imported.as_str()))
            })
            .map(|other| text(other, "id").to_owned())
            .collect();
        lean.push(LeanEntry {
            result_id: text(result, "id").to_owned(),
            theorem: theorem.to_owned(),
            status: get(result, "status"),
            transcription: transcriptions.contains_key(text(result, "id")),
            challenge_path: module_path(challenge).to_string_lossy().into_owned(),
            solution_path: module_path(solution).to_string_lossy().into_owned(),
            companion_theorems: blocks
                .iter()
                .filter(|block| block.name != short_name)
                .map(|block| Companion {
                    comparator_checked: checked.contains(block.name.as_str()),
                    block: block.clone(),
                })
                .collect(),
            advertised_statement: advertised,
            permitted_axioms: comparator
                .get("permitted_axioms")
                .cloned()
                .unwrap_or_else(|| json!([])),
            direct_imports: lean_files.imports(solution),
            reused_results: reused,
            lean_consumers: consumers.into_iter().collect(),
            lean_consumers_depth2: consumers_depth2.into_iter().collect(),
        });
    }

    // Lean neighbours: Solutions directly importing a shared non-result module.
    let own_vocabulary: HashSet<&str> = lean
        .iter()
        .flat_map(|entry| &entry.direct_imports)
        .map(String::as_str)
        .filter(|module| !module_to_result.contains_key(module))
        .collect();
    let own_results: HashSet<&str> = results.iter().map(|r| text(r, "id")).collect();
    let mut lean_neighbours = Vec::new();
    if !own_vocabulary.is_empty() {
        let mut sorted = all_results.clone();
        sorted.sort_by_key(|r| text(r, "id"));
        for other in sorted {
            if own_results.contains(text(other, "id"))
                || !pyfmt::truthy(other.get("solution_module"))
            {
                continue;
            }
            let shared: BTreeSet<String> = lean_files
                .imports(text(other, "solution_module"))
                .into_iter()
                .filter(|module| own_vocabulary.contains(module.as_str()))
                .collect();
            if !shared.is_empty() {
                lean_neighbours.push(Neighbour {
                    result: summary(other),
                    shared_modules: shared.into_iter().collect(),
                });
            }
        }
        lean_neighbours.sort_by(|a, b| {
            b.shared_modules
                .len()
                .cmp(&a.shared_modules.len())
                .then_with(|| a.result.result_id.cmp(&b.result.result_id))
        });
    }

    // Graph neighbourhood.
    let mut premise_siblings: Vec<Sibling> = arguments_in_order
        .iter()
        .filter(|other| text(other, "id") != argument_id)
        .filter_map(|other| {
            let shared: BTreeSet<&str> = list(other, "premise_statement_ids")
                .into_iter()
                .filter(|id| premise_set.contains(id))
                .collect();
            (!shared.is_empty()).then(|| Sibling {
                argument_id: text(other, "id").to_owned(),
                shared_premise_statement_ids: shared.into_iter().map(str::to_owned).collect(),
                conclusion_statement_id: get(other, "conclusion_statement_id"),
                results: summaries(text(other, "id")),
            })
        })
        .collect();
    premise_siblings.sort_by(|a, b| {
        b.shared_premise_statement_ids
            .len()
            .cmp(&a.shared_premise_statement_ids.len())
            .then_with(|| a.argument_id.cmp(&b.argument_id))
    });
    let downstream: Vec<Downstream> = arguments
        .iter()
        .filter(|(_, other)| list(other, "premise_statement_ids").contains(&conclusion))
        .map(|(aid, other)| Downstream {
            argument_id: (*aid).to_owned(),
            conclusion_statement_id: get(other, "conclusion_statement_id"),
            results: summaries(aid),
        })
        .collect();
    let own_premises: BTreeSet<&str> = premises.iter().copied().collect();
    let same_bundle: Vec<String> = arguments
        .iter()
        .filter(|(aid, other)| {
            **aid != argument_id
                && text(other, "conclusion_statement_id") == conclusion
                && list(other, "premise_statement_ids")
                    .into_iter()
                    .collect::<BTreeSet<_>>()
                    == own_premises
        })
        .map(|(aid, _)| (*aid).to_owned())
        .collect();
    let route_ids = |route: &Value| -> Vec<String> {
        route["open_premise_statement_ids"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .map(str::to_owned)
            .collect()
    };
    let routes: Vec<Value> = report
        .routes()
        .iter()
        .filter(|route| {
            route["argument_id"].as_str() == Some(argument_id)
                || route_ids(route)
                    .iter()
                    .any(|id| focus.contains(id.as_str()))
        })
        .cloned()
        .collect();

    // Countermodels, rivals and unresolved work.
    let mut models_sorted = corpus.records("models");
    models_sorted.sort_by_key(|r| text(r, "id"));
    let mut models: Vec<ModelEntry> = models_sorted
        .iter()
        .flat_map(|model| {
            model
                .get("evaluations")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .filter_map(Value::as_object)
                .filter(|evaluation| focus.contains(text(evaluation, "statement_id")))
                .map(|evaluation| ModelEntry {
                    model_id: text(model, "id").to_owned(),
                    statement_id: text(evaluation, "statement_id").to_owned(),
                    value: get(evaluation, "value"),
                    theorem: get(evaluation, "theorem"),
                    role: role(text(evaluation, "statement_id"), &premises, conclusion),
                })
        })
        .collect();
    models.sort_by_key(|m| {
        (
            m.value != "violates",
            m.role != "premise",
            m.model_id.clone(),
        )
    });
    let mut relations_sorted = corpus.records("relations");
    relations_sorted.sort_by_key(|r| text(r, "id"));
    let rival_relations: Vec<RivalRelation> = relations_sorted
        .iter()
        .filter(|relation| {
            matches!(
                text(relation, "predicate"),
                "alternative_to" | "attacks" | "refutes"
            ) && (focus.contains(text(relation, "subject_id"))
                || focus.contains(text(relation, "object_id"))
                || text(relation, "subject_id") == argument_id)
        })
        .map(|relation| RivalRelation {
            relation_id: text(relation, "id").to_owned(),
            subject_id: get(relation, "subject_id"),
            predicate: get(relation, "predicate"),
            object_id: get(relation, "object_id"),
            note: if pyfmt::truthy(relation.get("note")) {
                get(relation, "note")
            } else {
                get(relation, "basis")
            },
        })
        .collect();
    let ids: BTreeSet<&str> = focus
        .iter()
        .copied()
        .chain([argument_id])
        .chain(results.iter().map(|r| text(r, "id")))
        .collect();
    let mut attempts_sorted = corpus.records("attempts");
    attempts_sorted
        .sort_by(|a, b| (text(b, "date"), text(b, "id")).cmp(&(text(a, "date"), text(a, "id"))));
    let scoped_attempts: Vec<&Record> = attempts_sorted
        .into_iter()
        .filter(|attempt| {
            list(attempt, "statement_ids")
                .iter()
                .any(|id| focus.contains(id))
                || list(attempt, "evidence").iter().any(|id| ids.contains(id))
        })
        .collect();
    let attempts: Vec<AttemptEntry> = scoped_attempts
        .iter()
        .map(|attempt| AttemptEntry {
            attempt_id: text(attempt, "id").to_owned(),
            date: get(attempt, "date"),
            kind: get(attempt, "kind"),
            outcome: get(attempt, "outcome"),
            statement_ids: list(attempt, "statement_ids")
                .into_iter()
                .filter(|id| focus.contains(id))
                .map(str::to_owned)
                .collect(),
            summary: get(attempt, "summary"),
            blocker: get(attempt, "blocker"),
        })
        .collect();
    let mut by_length: Vec<&str> = ids.iter().copied().collect();
    by_length.sort_by_key(|id| std::cmp::Reverse(id.len()));
    let mut candidates_sorted = corpus.records("candidates");
    candidates_sorted.sort_by_key(|r| text(r, "id"));
    let candidates: Vec<CandidateEntry> = candidates_sorted
        .iter()
        .filter_map(|candidate| {
            let prose = ["goal", "reason"]
                .iter()
                .map(|field| candidate.get(*field).map_or_else(String::new, pyfmt::text))
                .collect::<Vec<_>>()
                .join(" ");
            let found = mentions(&prose, &by_length);
            (!found.is_empty()).then(|| CandidateEntry {
                candidate_id: text(candidate, "id").to_owned(),
                status: get(candidate, "status"),
                priority: get(candidate, "priority"),
                mentions: found,
                goal: get(candidate, "goal"),
            })
        })
        .collect();
    let mut configurations_sorted = corpus.records("configurations");
    configurations_sorted.sort_by_key(|r| text(r, "id"));
    let configurations: Vec<ConfigurationEntry> = configurations_sorted
        .iter()
        .filter_map(|case| {
            let touched: BTreeSet<&str> = configuration_statements(case)
                .into_iter()
                .filter(|id| focus.contains(id))
                .collect();
            (!touched.is_empty()).then(|| ConfigurationEntry {
                configuration_id: text(case, "id").to_owned(),
                semantics_id: case
                    .get("semantics")
                    .and_then(|s| s.get("id"))
                    .cloned()
                    .unwrap_or(Value::Null),
                statement_ids: touched.into_iter().map(str::to_owned).collect(),
            })
        })
        .collect();
    let mut route_leaves: BTreeMap<String, usize> = BTreeMap::new();
    for route in &routes {
        for sid in route_ids(route) {
            if !focus.contains(sid.as_str()) {
                *route_leaves.entry(sid).or_default() += 1;
            }
        }
    }
    let known: HashSet<&str> = statements
        .keys()
        .copied()
        .chain(arguments.keys().copied())
        .chain(all_results.iter().map(|r| text(r, "id")))
        .chain(corpus.records("models").iter().map(|r| text(r, "id")))
        .collect();
    let mut cited: BTreeMap<String, usize> = BTreeMap::new();
    for attempt in &scoped_attempts {
        let prose = format!(
            "{} {}",
            text(attempt, "summary"),
            attempt
                .get("blocker")
                .filter(|v| pyfmt::truthy(Some(v)))
                .map_or_else(String::new, pyfmt::text)
        );
        let mut tokens = id_tokens(&prose);
        tokens.extend(list(attempt, "evidence").into_iter().map(str::to_owned));
        for token in tokens {
            if known.contains(token.as_str()) && !ids.contains(token.as_str()) {
                *cited.entry(token).or_default() += 1;
            }
        }
    }
    let by_count = |counts: BTreeMap<String, usize>| -> Vec<String> {
        let mut entries: Vec<(String, usize)> = counts.into_iter().collect();
        entries.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
        entries.into_iter().map(|(id, _)| id).collect()
    };
    let open_premises: Vec<String> = premises
        .iter()
        .chain(&commitments)
        .filter(|sid| {
            report
                .closed_statements
                .get(**sid)
                .is_none_or(String::is_empty)
        })
        .map(|sid| (*sid).to_owned())
        .collect();
    let unresolved = Unresolved {
        open_premises_without_other_route: open_premises
            .iter()
            .filter(|sid| concluded_by(sid).is_empty())
            .cloned()
            .collect(),
        open_premise_statement_ids: open_premises,
        blocked_or_failed_attempt_ids: attempts
            .iter()
            .filter(|a| matches!(a.outcome.as_str(), Some("blocked" | "failed")))
            .map(|a| a.attempt_id.clone())
            .collect(),
        transcription_result_ids: results
            .iter()
            .map(|r| text(r, "id"))
            .filter(|id| transcriptions.contains_key(*id))
            .map(str::to_owned)
            .collect(),
        unchecked_companion_theorems: lean
            .iter()
            .flat_map(|entry| {
                entry
                    .companion_theorems
                    .iter()
                    .filter(|c| !c.comparator_checked)
                    .map(|c| format!("{}:{}", entry.result_id, c.block.name))
            })
            .collect(),
    };
    let inferences: HashMap<&str, &Record> = corpus
        .records("inferences")
        .into_iter()
        .map(|r| (text(r, "id"), r))
        .collect();
    let terms = |kind: &str, field: &str, link: &str| -> Vec<Term> {
        list(argument, link)
            .into_iter()
            .filter_map(|id| corpus.get(kind, id))
            .map(|record| {
                let value = Some(get(&record.fields, field));
                Term {
                    id: text(&record.fields, "id").to_owned(),
                    definition: if field == "definition" {
                        value.clone()
                    } else {
                        None
                    },
                    resolution: if field == "resolution" { value } else { None },
                }
            })
            .collect()
    };
    ContextPack {
        argument_id: argument_id.to_owned(),
        meaning: get(argument, "meaning"),
        root: report.root.clone(),
        conclusion: statement_entry(conclusion),
        premises: premises.iter().map(|sid| statement_entry(sid)).collect(),
        commitments: commitments.iter().map(|sid| statement_entry(sid)).collect(),
        inferences: list(argument, "inference_ids")
            .into_iter()
            .filter_map(|iid| inferences.get(iid).map(|inference| (iid, inference)))
            .map(|(iid, inference)| Inference {
                inference_id: iid.to_owned(),
                rule: get(inference, "rule"),
                input_statement_ids: get(inference, "input_statement_ids"),
                assumption_statement_ids: inference
                    .get("assumption_statement_ids")
                    .cloned()
                    .unwrap_or_else(|| json!([])),
                discharged_statement_ids: inference
                    .get("discharged_statement_ids")
                    .cloned()
                    .unwrap_or_else(|| json!([])),
                output_statement_id: get(inference, "output_statement_id"),
            })
            .collect(),
        lean,
        downstream_arguments: downstream,
        premise_sibling_arguments: premise_siblings,
        lean_neighbours,
        related_statements: related
            .iter()
            .map(|m| RelatedStatement {
                statement_id: m.statement_id.clone(),
                reasons: m
                    .reasons
                    .iter()
                    .map(|reason| reason.kind().to_owned())
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect(),
            })
            .collect(),
        same_bundle_argument_ids: same_bundle,
        routes,
        models,
        rival_relations,
        configurations,
        attempts,
        candidates,
        unresolved,
        route_open_leaves: by_count(route_leaves),
        attempt_cited_ids: by_count(cited),
        definitions: terms("definitions", "definition", "definition_ids"),
        disambiguations: terms("disambiguations", "resolution", "disambiguation_ids"),
    }
}

fn str_list(value: &Value) -> Vec<String> {
    value
        .as_array()
        .into_iter()
        .flatten()
        .map(pyfmt::text)
        .collect()
}

fn joined_or(items: &[String], empty: &str) -> String {
    if items.is_empty() {
        empty.into()
    } else {
        items.join(", ")
    }
}

fn overflowing(items: &[String]) -> String {
    let shown = items.len().min(OVERFLOW);
    let extra = if items.len() > OVERFLOW {
        format!(" +{}", items.len() - OVERFLOW)
    } else {
        String::new()
    };
    format!("{}{extra}", items[..shown].join(", "))
}

/// Python `format_context`: compact text; `--json` keeps every entry.
pub fn format_context(pack: &ContextPack, limit: i64) -> String {
    let mut lines: Vec<String> = Vec::new();
    fn capped<T>(
        lines: &mut Vec<String>,
        limit: i64,
        entries: &[T],
        render: impl Fn(&T) -> Vec<String>,
        ids: impl Fn(&T) -> Vec<String>,
    ) {
        let end = pyfmt::slice_end(entries.len(), limit);
        for entry in &entries[..end] {
            lines.extend(render(entry));
        }
        let start = if limit >= 0 {
            end
        } else {
            entries.len().saturating_sub(limit.unsigned_abs() as usize)
        };
        let hidden = &entries[start.min(entries.len())..];
        if !hidden.is_empty() {
            let mut names: Vec<String> = Vec::new();
            for name in hidden.iter().flat_map(&ids) {
                if !names.contains(&name) {
                    names.push(name);
                }
            }
            if names.is_empty() {
                lines.push(format!("  … {} more (see --json)", hidden.len()));
            } else {
                lines.push(format!(
                    "  … {} more: {} (see --json)",
                    hidden.len(),
                    overflowing(&names)
                ));
            }
        }
        if entries.is_empty() {
            lines.push("  none recorded".into());
        }
    }
    let none = |_: &_| Vec::<String>::new();
    let status = |entry: &StatementEntry| match &entry.closed {
        Some(closed) if !closed.is_empty() => format!("closed ({closed})"),
        _ if pyfmt::truthy(Some(&entry.open_depth)) => {
            format!("open ({})", pyfmt::text(&entry.open_depth))
        }
        _ => "not a frontier premise".into(),
    };
    let routes_of = |entry: &StatementEntry| {
        let others = &entry.concluded_by;
        if others.is_empty() {
            return "no other argument concludes it".to_owned();
        }
        let shown: Vec<String> = others
            .iter()
            .take(3)
            .map(|other| {
                let tags: BTreeSet<String> = other
                    .results
                    .iter()
                    .map(|r| {
                        let status = if pyfmt::truthy(Some(&r.status)) {
                            pyfmt::text(&r.status)
                        } else {
                            "?".into()
                        };
                        format!(
                            "{status}{}",
                            if r.transcription {
                                "/transcription"
                            } else {
                                ""
                            }
                        )
                    })
                    .collect();
                let tags = if tags.is_empty() {
                    "no result".to_owned()
                } else {
                    tags.into_iter().collect::<Vec<_>>().join(",")
                };
                format!("{} [{tags}]", other.argument_id)
            })
            .collect();
        let more = if others.len() > 3 {
            format!(
                " +{}",
                others
                    .iter()
                    .skip(3)
                    .take(OVERFLOW)
                    .map(|o| o.argument_id.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        } else {
            String::new()
        };
        format!("also concluded by {}{more}", shown.join("; "))
    };
    let root = pack.root.as_deref().unwrap_or("None");
    lines.push(format!(
        "Argument {} (derived context; navigation only, not verification)",
        pack.argument_id
    ));
    lines.push(format!(
        "  {}",
        pyfmt::short(pack.meaning.as_str(), WIDTH * 2)
    ));
    let c = &pack.conclusion;
    lines.push(format!(
        "\nConclusion {}: {}; reaches {root}: {}",
        c.statement_id,
        status(c),
        c.reaches_root
    ));
    lines.push(format!(
        "  {} [Lean {}]",
        pyfmt::short(c.paraphrase.as_str(), WIDTH),
        pyfmt::text(&c.lean_declaration)
    ));
    lines.push(format!("  {}", routes_of(c)));
    for (label, entries, commitments) in [
        ("Premises", &pack.premises, false),
        ("Commitments", &pack.commitments, true),
    ] {
        if commitments && entries.is_empty() {
            continue;
        }
        lines.push(if entries.is_empty() {
            format!("\n{label}: none")
        } else {
            format!(
                "\n{label} ({}; every one is required jointly):",
                entries.len()
            )
        });
        for entry in entries {
            lines.push(format!(
                "  {}: {}; {}",
                entry.statement_id,
                status(entry),
                routes_of(entry)
            ));
            lines.push(format!(
                "    {} [Lean {}]",
                pyfmt::short(entry.paraphrase.as_str(), WIDTH),
                pyfmt::text(&entry.lean_declaration)
            ));
        }
    }

    lines.push("\nLean (authoritative; text copied from the frozen Challenge module):".into());
    for entry in &pack.lean {
        let flag = if entry.transcription {
            "; TRANSCRIPTION"
        } else {
            ""
        };
        let axioms = if pyfmt::truthy(Some(&entry.permitted_axioms)) {
            pyfmt::repr(&entry.permitted_axioms)
        } else {
            "none".into()
        };
        lines.push(format!(
            "  result {} [{}{flag}] axioms {axioms}",
            entry.result_id,
            pyfmt::text(&entry.status)
        ));
        let line = entry
            .advertised_statement
            .as_ref()
            .map_or_else(|| "?".to_owned(), |block| block.line.to_string());
        lines.push(format!(
            "  {}:{line}  solution {}",
            entry.challenge_path, entry.solution_path
        ));
        match &entry.advertised_statement {
            Some(block) => lines.extend(
                pyfmt::splitlines(&block.statement)
                    .into_iter()
                    .map(|line| format!("    {line}")),
            ),
            None => lines.push(format!(
                "    theorem {} not found in the Challenge source",
                entry.theorem
            )),
        }
        let companions = &entry.companion_theorems;
        if !companions.is_empty() {
            lines.push(
                "  companion theorems in the same Challenge (often countermodels/independence):"
                    .into(),
            );
            for companion in &companions[..pyfmt::slice_end(companions.len(), limit)] {
                let head = pyfmt::collapse(&companion.block.statement);
                let checked = if companion.comparator_checked {
                    "comparator-checked"
                } else {
                    "NOT in comparator theorem_names"
                };
                lines.push(format!(
                    "    L{} {} [{checked}]",
                    companion.block.line,
                    pyfmt::short(Some(&head), WIDTH)
                ));
            }
            if (companions.len() as i64) > limit {
                lines.push(format!("    … {} more", companions.len() as i64 - limit));
            }
        }
        lines.push(
            "  reuses results through Lean imports (depth 1 = direct; not proof use):".into(),
        );
        capped(
            &mut lines,
            limit,
            &entry.reused_results,
            |r| {
                vec![format!(
                    "    {} d{} [{}; {}] {}",
                    r.result.result_id,
                    r.depth,
                    pyfmt::text(&r.result.status),
                    if r.graph_linked {
                        "graph-linked"
                    } else {
                        "import only, not an argument premise"
                    },
                    pyfmt::text(&r.result.theorem)
                )]
            },
            |r| vec![r.result.result_id.clone()],
        );
        lines.push(format!(
            "  results whose Solution imports this Solution: {}",
            joined_or(&entry.lean_consumers, "none")
        ));
        if !entry.lean_consumers_depth2.is_empty() {
            lines.push(format!(
                "  … and whose Solution imports one of those: {}",
                overflowing(&entry.lean_consumers_depth2)
            ));
        }
    }
    if pack.lean.is_empty() {
        lines.push("  no result record: the argument has no checked Lean theorem".into());
    }

    lines.push("\nInference steps:".into());
    capped(
        &mut lines,
        limit,
        &pack.inferences,
        |i| {
            let inputs = str_list(&i.input_statement_ids);
            let assumptions = str_list(&i.assumption_statement_ids);
            vec![format!(
                "  {} ({}): {} ⊢ {}{}",
                i.inference_id,
                pyfmt::text(&i.rule),
                if inputs.is_empty() {
                    "—".into()
                } else {
                    inputs.join(", ")
                },
                pyfmt::text(&i.output_statement_id),
                if assumptions.is_empty() {
                    String::new()
                } else {
                    format!("; assumes {}", assumptions.join(", "))
                }
            )]
        },
        none,
    );
    lines.push("\nDownstream arguments using the conclusion as a premise:".into());
    capped(
        &mut lines,
        limit,
        &pack.downstream_arguments,
        |d| {
            vec![format!(
                "  {} ⊢ {}",
                d.argument_id,
                pyfmt::text(&d.conclusion_statement_id)
            )]
        },
        |d| {
            vec![
                d.argument_id.clone(),
                pyfmt::text(&d.conclusion_statement_id),
            ]
        },
    );
    lines.push("Arguments sharing a premise (most shared first):".into());
    capped(
        &mut lines,
        limit,
        &pack.premise_sibling_arguments,
        |d| {
            let tags: BTreeSet<String> = d
                .results
                .iter()
                .map(|r| {
                    if pyfmt::truthy(Some(&r.status)) {
                        pyfmt::text(&r.status)
                    } else {
                        "?".into()
                    }
                })
                .collect();
            let tags = if tags.is_empty() {
                "no result".to_owned()
            } else {
                tags.into_iter().collect::<Vec<_>>().join(",")
            };
            vec![format!(
                "  {} [{tags}] shares {} ⊢ {}",
                d.argument_id,
                d.shared_premise_statement_ids.join(", "),
                pyfmt::text(&d.conclusion_statement_id)
            )]
        },
        |d| {
            vec![
                d.argument_id.clone(),
                pyfmt::text(&d.conclusion_statement_id),
            ]
        },
    );
    lines.push(
        "Lean neighbours (Solutions importing the same vocabulary modules; proximity, not entailment):"
            .into(),
    );
    capped(
        &mut lines,
        limit,
        &pack.lean_neighbours,
        |n| {
            vec![format!(
                "  {} [{}] via {}",
                n.result.result_id,
                pyfmt::text(&n.result.status),
                n.shared_modules
                    .iter()
                    .map(|m| m.rsplit('.').next().unwrap_or_default())
                    .collect::<Vec<_>>()
                    .join(", ")
            )]
        },
        |n| vec![n.result.result_id.clone()],
    );
    if !pack.related_statements.is_empty() {
        let ids: Vec<&str> = pack
            .related_statements
            .iter()
            .take(OVERFLOW)
            .map(|r| r.statement_id.as_str())
            .collect();
        lines.push(format!(
            "Related to the conclusion (research-index ranking; discovery only): {}",
            ids.join(", ")
        ));
    }
    if !pack.same_bundle_argument_ids.is_empty() {
        lines.push(format!(
            "Same premise bundle and conclusion (possible duplicate): {}",
            pack.same_bundle_argument_ids.join(", ")
        ));
    }
    lines.push(format!(
        "\nRoutes to {root} touching this argument (cost = open leaves):"
    ));
    capped(
        &mut lines,
        limit,
        &pack.routes,
        |r| {
            vec![format!(
                "  {}: cost {}",
                pyfmt::text(&r["argument_id"]),
                pyfmt::text(&r["cost"])
            )]
        },
        |r| vec![pyfmt::text(&r["argument_id"])],
    );
    if !pack.route_open_leaves.is_empty() {
        lines.push(format!(
            "  other open leaves on these routes (most routes first): {}",
            overflowing(&pack.route_open_leaves)
        ));
    }

    lines.push("\nCountermodels and rivals (formal interpretations; no premise closure):".into());
    let mut values: BTreeMap<String, usize> = BTreeMap::new();
    for model in &pack.models {
        *values.entry(pyfmt::text(&model.value)).or_default() += 1;
    }
    let counts: Vec<String> = values
        .iter()
        .map(|(value, count)| format!("{count} {value}"))
        .collect();
    lines.push(format!(
        "  model evaluations: {}",
        joined_or(&counts, "none registered")
    ));
    let violating: Vec<&ModelEntry> = pack
        .models
        .iter()
        .filter(|m| m.value == "violates")
        .collect();
    if !violating.is_empty() {
        capped(
            &mut lines,
            limit,
            &violating,
            |m| {
                vec![format!(
                    "  {} violates {} {} ({})",
                    m.model_id,
                    m.role,
                    m.statement_id,
                    pyfmt::text(&m.theorem)
                )]
            },
            |m| vec![m.model_id.clone()],
        );
    }
    lines.push("  rival relations (alternative_to / attacks / refutes):".into());
    capped(
        &mut lines,
        limit,
        &pack.rival_relations,
        |r| {
            vec![format!(
                "    {}: {} {} {}",
                r.relation_id,
                pyfmt::text(&r.subject_id),
                pyfmt::text(&r.predicate),
                pyfmt::text(&r.object_id)
            )]
        },
        |r| vec![pyfmt::text(&r.subject_id), pyfmt::text(&r.object_id)],
    );
    if !pack.configurations.is_empty() {
        let cases: Vec<String> = pack
            .configurations
            .iter()
            .map(|c| format!("{} ({})", c.configuration_id, pyfmt::text(&c.semantics_id)))
            .collect();
        lines.push(format!("  configuration cases: {}", cases.join(", ")));
    }

    lines.push("\nAttempts on these statements, newest first (outcomes establish nothing):".into());
    capped(
        &mut lines,
        limit,
        &pack.attempts,
        |a| {
            let mut rendered = vec![format!(
                "  {} [{}; {}; {}]: {}",
                a.attempt_id,
                pyfmt::text(&a.date),
                pyfmt::text(&a.kind),
                pyfmt::text(&a.outcome),
                pyfmt::short(a.summary.as_str(), WIDTH)
            )];
            if pyfmt::truthy(Some(&a.blocker)) {
                rendered.push(format!(
                    "    blocker: {}",
                    pyfmt::short(a.blocker.as_str(), WIDTH)
                ));
            }
            rendered
        },
        |a| vec![a.attempt_id.clone()],
    );
    if !pack.attempt_cited_ids.is_empty() {
        lines.push(format!(
            "  IDs these attempts cite (most cited first; discovery only): {}",
            overflowing(&pack.attempt_cited_ids)
        ));
    }
    lines.push("\nCandidates mentioning these IDs:".into());
    capped(
        &mut lines,
        limit,
        &pack.candidates,
        |c| {
            vec![format!(
                "  {} [{}; p{}] mentions {}: {}",
                c.candidate_id,
                pyfmt::text(&c.status),
                pyfmt::text(&c.priority),
                c.mentions.join(", "),
                pyfmt::short(c.goal.as_str(), WIDTH)
            )]
        },
        |c| vec![c.candidate_id.clone()],
    );

    let u = &pack.unresolved;
    lines.push("\nUnresolved:".into());
    lines.push(format!(
        "  open premises: {}",
        joined_or(&u.open_premise_statement_ids, "none")
    ));
    lines.push(format!(
        "  open with no other recorded argument: {}",
        joined_or(&u.open_premises_without_other_route, "none")
    ));
    lines.push(format!(
        "  blocked/failed attempts: {}",
        joined_or(&u.blocked_or_failed_attempt_ids, "none")
    ));
    if !u.transcription_result_ids.is_empty() {
        lines.push(format!(
            "  transcription results (close nothing by themselves): {}",
            u.transcription_result_ids.join(", ")
        ));
    }
    if !u.unchecked_companion_theorems.is_empty() {
        lines.push(format!(
            "  companion theorems not checked by Comparator: {}",
            u.unchecked_companion_theorems.join(", ")
        ));
    }
    lines.push("\nTerms linked by the argument (IDs; read with research_index.py show):".into());
    let terms: Vec<String> = pack
        .definitions
        .iter()
        .chain(&pack.disambiguations)
        .map(|t| t.id.clone())
        .collect();
    lines.push(format!("  {}", joined_or(&terms, "none")));
    lines.push(
        "\nNext: corpus.py dossier <open premise>; corpus.py related <conclusion>; scripts/verify-result.sh <result> after lake build."
            .into(),
    );
    lines.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lean_text_scanners_follow_python_patterns() {
        let source = "module\npublic import TruthCore.A\nimport Mathlib.B\n-- import X\n";
        assert_eq!(import_names(source), vec!["TruthCore.A", "Mathlib.B"]);
        let source = "/-- doc -/\ntheorem t (h : P) :\n    P := h\n\n@[simp] private lemma u : Q := q\ntheorem broken : R\ndef x := 1\n";
        let blocks = theorem_blocks_in(source);
        assert_eq!(blocks.len(), 2);
        assert_eq!(blocks[0].name, "t");
        assert_eq!(blocks[0].line, 2);
        assert_eq!(blocks[0].statement, "theorem t (h : P) :\n    P");
        assert_eq!(blocks[1].name, "u");
        assert_eq!(blocks[1].statement, "@[simp] private lemma u : Q");
    }

    #[test]
    fn id_tokens_and_mentions() {
        assert_eq!(
            id_tokens("see STMT-A-1, not STMT-a or X-Y-z; ARG-B."),
            ["ARG-B", "STMT-A-1"]
                .into_iter()
                .map(str::to_owned)
                .collect()
        );
        assert_eq!(
            mentions("STMT-AB and STMT-A-X and xSTMT-A", &["STMT-AB", "STMT-A"]),
            vec!["STMT-A", "STMT-AB"]
        );
    }
}
