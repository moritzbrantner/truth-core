//! Derivational thickness and its derivation worklist, ported from
//! `scripts/corpus.py` (`thickness_report`, `thickness_queue` and the parts of
//! `frontier_report` they read). Presentation only: nothing here closes a
//! statement or changes a route cost, and the Python frontier stays the
//! authority for closure.
//!
//! The frontier inputs (transcription kinds, reaching-root statements,
//! source depths, upward walks and counted refutations) come from
//! `crate::frontier`, the port of `frontier_report`.

use crate::Corpus;
use crate::frontier::Frontier;
use crate::transcription::Flag;
use serde_json::{Map, Value, json};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

pub const DEFAULT_ROOT: &str = "STMT-CATHOLICISM-TRUE";
const QUEUE_CANDIDATE_LIMIT: usize = 5;
const QUEUE_TEXT_ATTEMPT_LIMIT: usize = 5;

pub(crate) type Record = Map<String, Value>;

pub(crate) fn text<'a>(record: &'a Record, field: &str) -> &'a str {
    record
        .get(field)
        .and_then(Value::as_str)
        .unwrap_or_default()
}

pub(crate) fn list<'a>(record: &'a Record, field: &str) -> Vec<&'a str> {
    record
        .get(field)
        .and_then(Value::as_array)
        .map(|items| items.iter().filter_map(Value::as_str).collect())
        .unwrap_or_default()
}

pub(crate) fn truthy(value: Option<&Value>) -> bool {
    match value {
        None | Some(Value::Null) => false,
        Some(Value::Bool(value)) => *value,
        Some(Value::String(value)) => !value.is_empty(),
        Some(Value::Array(value)) => !value.is_empty(),
        Some(Value::Object(value)) => !value.is_empty(),
        Some(Value::Number(value)) => value.as_f64() != Some(0.0),
    }
}

/// A declared or heuristic transcription kind of one result.
pub struct TranscriptionKind {
    pub kind: String,
    pub declared: bool,
}

/// What `thickness` reads from the frontier.
pub struct FrontierInputs {
    pub root: String,
    pub transcription_results: BTreeMap<String, TranscriptionKind>,
    pub reaching_root: BTreeSet<String>,
    pub statement_depths: HashMap<String, &'static str>,
    pub premise_dependent_arguments: HashMap<String, usize>,
    /// `(refuting argument, refuted statement)` -> counted, last relation by ID wins.
    pub counted_refutations: HashMap<(String, String), bool>,
}

/// Records by kind in file order, as Python `load_dir` lists them.
pub struct Records<'a> {
    pub statements: Vec<&'a Record>,
    pub arguments: Vec<&'a Record>,
    pub results: Vec<&'a Record>,
    pub relations: Vec<&'a Record>,
    pub claims: Vec<&'a Record>,
    pub attempts: Vec<&'a Record>,
    pub definitions: Vec<&'a Record>,
    pub inferences: Vec<&'a Record>,
}

impl<'a> Records<'a> {
    pub fn from_corpus(corpus: &'a Corpus) -> Self {
        Self {
            statements: corpus.records("statements"),
            arguments: corpus.records("arguments"),
            results: corpus.records("results"),
            relations: corpus.records("relations"),
            claims: corpus.records("claims"),
            attempts: corpus.records("attempts"),
            definitions: corpus.records("definitions"),
            inferences: corpus.records("inferences"),
        }
    }
}

/// The frontier quantities `thickness` and `thickness --queue` read, taken
/// from the one frontier computation (`crate::frontier`), so thickness and
/// frontier cannot disagree on closure, depths or walks.
pub fn frontier_inputs(root: &str, records: &Records, flags: &[Flag]) -> FrontierInputs {
    let report = Frontier::new(root, records, flags).report(false);
    let strings = |value: &Value| -> Vec<String> {
        value
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .map(str::to_owned)
            .collect()
    };
    let transcription_results = report["transcription_results"]
        .as_object()
        .into_iter()
        .flatten()
        .map(|(id, kind)| {
            (
                id.clone(),
                TranscriptionKind {
                    kind: kind["kind"].as_str().unwrap_or_default().to_owned(),
                    declared: kind["declared"] == true,
                },
            )
        })
        .collect();
    let statement_depths = report["statement_depths"]
        .as_object()
        .into_iter()
        .flatten()
        .map(|(id, depth)| {
            let depth = match depth.as_str() {
                Some("stated") => "stated",
                Some("supported") => "supported",
                _ => "bare",
            };
            (id.clone(), depth)
        })
        .collect();
    let premise_dependent_arguments = report["premise_dependents"]
        .as_object()
        .into_iter()
        .flatten()
        .map(|(id, walk)| (id.clone(), walk["arguments"].as_array().map_or(0, Vec::len)))
        .collect();
    // Refutations come in relation-ID order: the last one for a pair wins.
    let counted_refutations = report["refutations"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|refutation| {
            (
                (
                    refutation["argument_id"]
                        .as_str()
                        .unwrap_or_default()
                        .to_owned(),
                    refutation["statement_id"]
                        .as_str()
                        .unwrap_or_default()
                        .to_owned(),
                ),
                refutation["counted"] == true,
            )
        })
        .collect();
    FrontierInputs {
        root: root.to_owned(),
        transcription_results,
        reaching_root: strings(&report["reaching_root_statements"])
            .into_iter()
            .collect(),
        statement_depths,
        premise_dependent_arguments,
        counted_refutations,
    }
}

/// Python `thickness_report`: verified non-transcription derivations of every
/// statement reaching the root.
pub fn thickness_report(frontier: &FrontierInputs, records: &Records) -> Value {
    let verified: HashSet<&str> = records
        .results
        .iter()
        .filter(|result| {
            !frontier
                .transcription_results
                .contains_key(text(result, "id"))
        })
        .map(|result| text(result, "argument_id"))
        .collect();
    let mut derivations: HashMap<&str, Vec<&str>> = HashMap::new();
    for argument in &records.arguments {
        if verified.contains(text(argument, "id")) {
            derivations
                .entry(text(argument, "conclusion_statement_id"))
                .or_default()
                .push(text(argument, "id"));
        }
    }
    let mut per_statement = Map::new();
    let (mut derived, mut multiple, mut total) = (0, 0, 0);
    for statement in &frontier.reaching_root {
        let mut ids = derivations
            .get(statement.as_str())
            .cloned()
            .unwrap_or_default();
        ids.sort_unstable();
        derived += usize::from(!ids.is_empty());
        multiple += usize::from(ids.len() >= 2);
        total += ids.len();
        per_statement.insert(statement.clone(), json!(ids));
    }
    json!({
        "root": frontier.root,
        "statement_count": frontier.reaching_root.len(),
        "derived_statement_count": derived,
        "multiply_derived_statement_count": multiple,
        "derivation_count": total,
        "derivations": per_statement,
    })
}

/// Python `thickness_queue`: every statement reaching the root without a
/// verified non-transcription derivation, with what is known about it.
pub fn thickness_queue(frontier: &FrontierInputs, report: &Value, records: &Records) -> Vec<Value> {
    let statements: HashMap<&str, &Record> = records
        .statements
        .iter()
        .map(|statement| (text(statement, "id"), *statement))
        .collect();
    let mut results_by_argument: HashMap<&str, Vec<&str>> = HashMap::new();
    for result in &records.results {
        results_by_argument
            .entry(text(result, "argument_id"))
            .or_default()
            .push(text(result, "id"));
    }
    let mut concluding: HashMap<&str, Vec<&str>> = HashMap::new();
    let mut used: HashSet<&str> = HashSet::new();
    for argument in &records.arguments {
        let conclusion = text(argument, "conclusion_statement_id");
        concluding
            .entry(conclusion)
            .or_default()
            .push(text(argument, "id"));
        used.insert(conclusion);
        used.extend(list(argument, "premise_statement_ids"));
        used.extend(list(argument, "commitment_statement_ids"));
    }
    let mut supports: HashMap<&str, Vec<(&str, &str, &str)>> = HashMap::new();
    let mut rivals: HashMap<&str, BTreeSet<&str>> = HashMap::new();
    let mut refuters: HashMap<&str, Vec<&str>> = HashMap::new();
    for relation in &records.relations {
        let (subject, object) = (text(relation, "subject_id"), text(relation, "object_id"));
        match text(relation, "predicate") {
            "supports" => supports.entry(object).or_default().push((
                text(relation, "id"),
                text(relation, "subject_kind"),
                subject,
            )),
            "alternative_to" => {
                rivals.entry(object).or_default().insert(subject);
            }
            "refutes" => refuters.entry(object).or_default().push(subject),
            _ => {}
        }
    }
    let mut attempts_by_statement: HashMap<&str, Vec<(&str, &str)>> = HashMap::new();
    for attempt in &records.attempts {
        for statement in list(attempt, "statement_ids") {
            attempts_by_statement
                .entry(statement)
                .or_default()
                .push((text(attempt, "id"), text(attempt, "outcome")));
        }
    }
    let claim_statement: HashMap<&str, &str> = records
        .claims
        .iter()
        .filter(|claim| truthy(claim.get("statement_id")))
        .map(|claim| (text(claim, "id"), text(claim, "statement_id")))
        .collect();
    let unused_defined: BTreeSet<&str> = records
        .definitions
        .iter()
        .flat_map(|definition| list(definition, "claim_ids"))
        .filter_map(|claim| claim_statement.get(claim).copied())
        .filter(|statement| !used.contains(statement) && statements.contains_key(statement))
        .collect();
    let definition_ids = |statement: &str| -> BTreeSet<&str> {
        statements
            .get(statement)
            .map(|record| list(record, "definition_ids").into_iter().collect())
            .unwrap_or_default()
    };
    let argument_status = |argument_id: &str| -> String {
        let result_ids = results_by_argument
            .get(argument_id)
            .map(Vec::as_slice)
            .unwrap_or_default();
        match result_ids.first() {
            None => "no result".into(),
            Some(_)
                if result_ids
                    .iter()
                    .any(|id| !frontier.transcription_results.contains_key(*id)) =>
            {
                "verified".into()
            }
            Some(first) => format!(
                "transcription ({})",
                frontier.transcription_results[*first].kind
            ),
        }
    };

    let mut entries = Vec::new();
    for (statement_id, derivations) in report["derivations"].as_object().into_iter().flatten() {
        if derivations.as_array().is_some_and(|ids| !ids.is_empty()) {
            continue;
        }
        let statement_id = statement_id.as_str();
        let definitions = definition_ids(statement_id);
        let mut candidates: Vec<(Vec<&str>, &str)> = Vec::new();
        if !definitions.is_empty() {
            for other in &unused_defined {
                let shared: Vec<&str> = definitions
                    .intersection(&definition_ids(other))
                    .copied()
                    .collect();
                if *other != statement_id && !shared.is_empty() {
                    candidates.push((shared, other));
                }
            }
            candidates.sort_by(|a, b| b.0.len().cmp(&a.0.len()).then(a.1.cmp(b.1)));
        }
        let mut attempts = attempts_by_statement
            .get(statement_id)
            .cloned()
            .unwrap_or_default();
        attempts.sort_by(|a, b| (a.1 != "rejected", a.0).cmp(&(b.1 != "rejected", b.0)));
        let mut argument_ids = concluding.get(statement_id).cloned().unwrap_or_default();
        argument_ids.sort_unstable();
        let mut statement_supports = supports.get(statement_id).cloned().unwrap_or_default();
        statement_supports.sort_by_key(|support| support.0);
        let record = statements.get(statement_id);
        entries.push(json!({
            "statement_id": statement_id,
            "depth": frontier.statement_depths.get(statement_id),
            "lean_declaration": record.and_then(|record| record.get("lean_declaration")),
            "argument_dependents": frontier.premise_dependent_arguments.get(statement_id).copied().unwrap_or(0),
            "examined": attempts.iter().any(|(_, outcome)| *outcome == "rejected"),
            "arguments": argument_ids.iter().map(|id| json!({
                "argument_id": id, "status": argument_status(id),
            })).collect::<Vec<_>>(),
            "supports": statement_supports.iter().map(|(relation_id, kind, id)| json!({
                "kind": kind, "id": id, "relation_id": relation_id,
            })).collect::<Vec<_>>(),
            "rivals": rivals.get(statement_id).into_iter().flatten().map(|rival| {
                let mut refuting = refuters.get(rival).cloned().unwrap_or_default();
                refuting.sort_unstable();
                json!({
                    "statement_id": rival,
                    "refutations": refuting.iter().map(|argument_id| json!({
                        "argument_id": argument_id,
                        "counted": frontier.counted_refutations
                            .get(&((*argument_id).to_owned(), (*rival).to_owned()))
                            .copied().unwrap_or(false),
                    })).collect::<Vec<_>>(),
                })
            }).collect::<Vec<_>>(),
            "attempts": attempts.iter().map(|(id, outcome)| json!({
                "id": id, "outcome": outcome,
            })).collect::<Vec<_>>(),
            "definition_linked_unused": candidates.iter().take(QUEUE_CANDIDATE_LIMIT).map(|(shared, id)| json!({
                "statement_id": id, "shared_definition_ids": shared,
            })).collect::<Vec<_>>(),
        }));
    }
    entries.sort_by(|a, b| {
        let key = |entry: &Value| {
            (
                entry["examined"].as_bool().unwrap_or(false),
                std::cmp::Reverse(entry["argument_dependents"].as_u64().unwrap_or(0)),
                entry["statement_id"]
                    .as_str()
                    .unwrap_or_default()
                    .to_owned(),
            )
        };
        key(a).cmp(&key(b))
    });
    entries
}

fn python_repr(value: &Value) -> String {
    match value {
        Value::Null => "None".into(),
        Value::String(text) => text.clone(),
        other => other.to_string(),
    }
}

/// Python `format_thickness` without a base.
pub fn format_thickness(report: &Value) -> String {
    let mut lines = vec![
        format!(
            "derivational thickness for {} (presentation only; closes nothing)",
            python_repr(&report["root"])
        ),
        format!(
            "statements reaching the root: {}",
            report["statement_count"]
        ),
        format!(
            "  with a verified non-transcription derivation: {}",
            report["derived_statement_count"]
        ),
        format!(
            "  with two or more: {}",
            report["multiply_derived_statement_count"]
        ),
        format!("derivations in total: {}", report["derivation_count"]),
    ];
    for (statement, ids) in report["derivations"].as_object().into_iter().flatten() {
        let count = ids.as_array().map_or(0, Vec::len);
        lines.push(format!("  {count:2}  {statement}"));
    }
    lines.join("\n")
}

/// Python `format_thickness_queue`.
pub fn format_thickness_queue(root: &str, queue: &[Value]) -> String {
    let examined = queue
        .iter()
        .filter(|entry| entry["examined"] == true)
        .count();
    let mut lines = vec![
        format!("derivation worklist for {root} (presentation only; closes nothing)"),
        format!(
            "statements reaching the root without a verified non-transcription derivation: {} ({examined} examined: a rejected-outcome attempt names them)",
            queue.len()
        ),
    ];
    let items = |entry: &Value, field: &str| entry[field].as_array().cloned().unwrap_or_default();
    for entry in queue {
        let mark = if entry["examined"] == true {
            "examined"
        } else {
            "unexamined"
        };
        lines.push(format!(
            "{} [{}; {} dependent arguments; {mark}]",
            python_repr(&entry["statement_id"]),
            python_repr(&entry["depth"]),
            entry["argument_dependents"]
        ));
        let lean = entry["lean_declaration"]
            .as_str()
            .filter(|lean| !lean.is_empty())
            .unwrap_or("-");
        lines.push(format!("  lean: {lean}"));
        for argument in items(entry, "arguments") {
            lines.push(format!(
                "  argument {}: {}",
                python_repr(&argument["argument_id"]),
                python_repr(&argument["status"])
            ));
        }
        for support in items(entry, "supports") {
            lines.push(format!(
                "  supported by {} {}",
                python_repr(&support["kind"]),
                python_repr(&support["id"])
            ));
        }
        for rival in items(entry, "rivals") {
            let refutations = items(&rival, "refutations");
            let text = if refutations.is_empty() {
                "no refutes relation".to_owned()
            } else {
                refutations
                    .iter()
                    .map(|item| {
                        let counted = if item["counted"] == true {
                            "counted"
                        } else {
                            "not counted"
                        };
                        format!("{} ({counted})", python_repr(&item["argument_id"]))
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            lines.push(format!(
                "  rival {}: {text}",
                python_repr(&rival["statement_id"])
            ));
        }
        let attempts = items(entry, "attempts");
        for attempt in attempts.iter().take(QUEUE_TEXT_ATTEMPT_LIMIT) {
            lines.push(format!(
                "  attempt {}: {}",
                python_repr(&attempt["id"]),
                python_repr(&attempt["outcome"])
            ));
        }
        if attempts.len() > QUEUE_TEXT_ATTEMPT_LIMIT {
            lines.push(format!(
                "  (+{} more attempts; --json lists all)",
                attempts.len() - QUEUE_TEXT_ATTEMPT_LIMIT
            ));
        }
        for candidate in items(entry, "definition_linked_unused") {
            let shared: Vec<String> = items(&candidate, "shared_definition_ids")
                .iter()
                .map(python_repr)
                .collect();
            lines.push(format!(
                "  unused definition-linked {} via {}",
                python_repr(&candidate["statement_id"]),
                shared.join(", ")
            ));
        }
    }
    lines.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn records(values: Vec<Value>) -> Vec<Record> {
        values
            .into_iter()
            .map(|value| value.as_object().cloned().unwrap_or_default())
            .collect()
    }

    fn argument(id: &str, premises: &[&str], conclusion: &str) -> Value {
        json!({"id": id, "premise_statement_ids": premises, "conclusion_statement_id": conclusion})
    }

    fn relation(id: &str, subject: &str, predicate: &str, object: &str) -> Value {
        json!({"id": id, "subject_kind": "argument", "subject_id": subject,
               "predicate": predicate, "object_kind": "statement", "object_id": object})
    }

    struct Fixture {
        statements: Vec<Record>,
        arguments: Vec<Record>,
        results: Vec<Record>,
        relations: Vec<Record>,
        claims: Vec<Record>,
        attempts: Vec<Record>,
    }

    impl Fixture {
        fn new() -> Self {
            let ids = ["ROOT", "A", "B", "C", "D", "E", "W", "S", "R", "X"];
            Self {
                statements: records(ids.iter().map(|id| json!({"id": id})).collect()),
                arguments: records(vec![
                    argument("ARG-ROOT", &["A", "B"], "ROOT"),
                    argument("ARG-ROOT-UNROUTED", &["E"], "ROOT"),
                    argument("ARG-A", &["C"], "A"),
                    argument("ARG-A-TRANSCRIBED", &["D"], "A"),
                    argument("ARG-B", &["W"], "B"),
                    argument("ARG-STRENGTH", &["S"], "W"),
                    argument("ARG-REFUTE-R", &[], "X"),
                ]),
                results: records(vec![
                    json!({"id": "RES-ROOT", "argument_id": "ARG-ROOT"}),
                    json!({"id": "RES-ROOT-UNROUTED", "argument_id": "ARG-ROOT-UNROUTED"}),
                    json!({"id": "RES-A", "argument_id": "ARG-A"}),
                    json!({"id": "RES-A-T", "argument_id": "ARG-A-TRANSCRIBED",
                           "transcription": "single_application"}),
                    json!({"id": "RES-STRENGTH", "argument_id": "ARG-STRENGTH"}),
                    json!({"id": "RES-REFUTE", "argument_id": "ARG-REFUTE-R"}),
                ]),
                relations: records(vec![
                    relation("REL-ROUTE", "ARG-ROOT", "root_route", "ROOT"),
                    json!({"id": "REL-STRENGTH", "subject_kind": "statement", "subject_id": "S",
                           "predicate": "strengthens", "object_kind": "statement", "object_id": "W",
                           "verification_result_id": "RES-STRENGTH"}),
                    relation("REL-ALT", "R", "alternative_to", "C")
                        .as_object()
                        .map(|object| {
                            let mut object = object.clone();
                            object.insert("subject_kind".into(), json!("statement"));
                            Value::Object(object)
                        })
                        .unwrap_or_default(),
                    relation("REL-REFUTE", "ARG-REFUTE-R", "refutes", "R"),
                    relation("REL-SUPPORT", "SRC", "supports", "B"),
                ]),
                claims: records(vec![json!({"id": "CLAIM-D", "statement_id": "D"})]),
                attempts: records(vec![
                    json!({"id": "ATT-2", "outcome": "inconclusive", "statement_ids": ["B"]}),
                    json!({"id": "ATT-1", "outcome": "rejected", "statement_ids": ["B"]}),
                ]),
            }
        }

        fn records(&self) -> Records<'_> {
            Records {
                statements: self.statements.iter().collect(),
                arguments: self.arguments.iter().collect(),
                results: self.results.iter().collect(),
                relations: self.relations.iter().collect(),
                claims: self.claims.iter().collect(),
                attempts: self.attempts.iter().collect(),
                definitions: Vec::new(),
                inferences: Vec::new(),
            }
        }
    }

    #[test]
    fn reaching_root_honors_routes_and_strength_registrations() {
        let fixture = Fixture::new();
        let records = fixture.records();
        let frontier = frontier_inputs("ROOT", &records, &[]);
        // E enters only through the undesignated route; S only through the
        // strength registration, which is set aside.
        let reached: Vec<&str> = frontier.reaching_root.iter().map(String::as_str).collect();
        assert_eq!(reached, ["A", "B", "C", "D", "ROOT", "W"]);
        assert_eq!(frontier.statement_depths["D"], "stated");
        assert_eq!(frontier.statement_depths["B"], "supported");
        assert_eq!(frontier.statement_depths["C"], "bare");
        // C is used by ARG-A, which concludes A, which the routed ARG-ROOT uses.
        assert_eq!(frontier.premise_dependent_arguments["C"], 2);
        // E's dependent argument is counted although it does not enter ROOT.
        assert_eq!(frontier.premise_dependent_arguments["E"], 1);
        // A premise-free verified refutation counts; it defends C.
        assert!(frontier.counted_refutations[&("ARG-REFUTE-R".into(), "R".into())]);
    }

    #[test]
    fn report_counts_non_transcription_derivations_and_queues_the_rest() {
        let fixture = Fixture::new();
        let records = fixture.records();
        let frontier = frontier_inputs("ROOT", &records, &[]);
        let report = thickness_report(&frontier, &records);
        assert_eq!(report["statement_count"], 6);
        assert_eq!(report["derivations"]["A"], json!(["ARG-A"]));
        // The strength registration is still a verified derivation of W here,
        // as in Python, which counts over all records.
        assert_eq!(report["derivations"]["W"], json!(["ARG-STRENGTH"]));
        assert_eq!(report["derivation_count"], 4);
        let queue = thickness_queue(&frontier, &report, &records);
        let order: Vec<&str> = queue
            .iter()
            .map(|entry| entry["statement_id"].as_str().unwrap_or_default())
            .collect();
        // Unexamined first, then by dependents descending, then by ID.
        assert_eq!(order, ["C", "D", "B"]);
        assert_eq!(queue[2]["examined"], true);
        assert_eq!(queue[2]["attempts"][0]["id"], "ATT-1");
        assert_eq!(
            queue[2]["arguments"],
            json!([{"argument_id": "ARG-B", "status": "no result"}])
        );
        assert_eq!(queue[2]["supports"][0]["relation_id"], "REL-SUPPORT");
        assert_eq!(
            queue[0]["rivals"],
            json!([{"statement_id": "R", "refutations": [
                {"argument_id": "ARG-REFUTE-R", "counted": true}]}])
        );
        let text = format_thickness_queue("ROOT", &queue);
        assert!(text.contains("B [supported; 1 dependent arguments; examined]"));
    }
}
