//! Derivational thickness and its derivation worklist, ported from
//! `scripts/corpus.py` (`thickness_report`, `thickness_queue` and the parts of
//! `frontier_report` they read). Presentation only: nothing here closes a
//! statement or changes a route cost, and the Python frontier stays the
//! authority for closure.
//!
//! Ported frontier inputs: the strength order (#1017) and the set-aside of its
//! registration arguments, transcription kinds (declared, plus the Lean-text
//! single-application and assembly heuristics), the least fixpoint of
//! `established`/`refuted` (floor bases, defended statements, verified steps,
//! strength propagation) that decides whether a refutation counts, source
//! depths, the route-aware upward walk (`premise_dependents`) and the
//! reaching-root walk honoring `root_route` relations.

use crate::{Corpus, transcription};
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    path::Path,
};

pub const DEFAULT_ROOT: &str = "STMT-CATHOLICISM-TRUE";
const QUEUE_CANDIDATE_LIMIT: usize = 5;
const QUEUE_TEXT_ATTEMPT_LIMIT: usize = 5;

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

/// Vendored from rust-kernels `graph-kernels` (`traversal::breadth_first`,
/// MIT, github.com/moritzbrantner/rust-kernels at d8a68f92), copied rather
/// than depended on (invariant 19). Visits every node reachable from `start`.
fn breadth_first<N, I, Neighbors>(start: N, mut neighbors: Neighbors) -> Vec<N>
where
    N: Clone + Eq + std::hash::Hash,
    I: IntoIterator<Item = N>,
    Neighbors: FnMut(&N) -> I,
{
    let mut order = Vec::new();
    let mut seen = HashSet::new();
    let mut frontier = std::collections::VecDeque::new();
    seen.insert(start.clone());
    frontier.push_back(start);
    while let Some(node) = frontier.pop_front() {
        for next in neighbors(&node) {
            if seen.insert(next.clone()) {
                frontier.push_back(next);
            }
        }
        order.push(node);
    }
    order
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
        }
    }
}

struct StrengthEntry<'a> {
    strong: &'a str,
    weak: &'a str,
    argument_id: &'a str,
}

fn strength_order<'a>(records: &Records<'a>) -> Vec<StrengthEntry<'a>> {
    let results: HashMap<&str, &Record> = records
        .results
        .iter()
        .map(|result| (text(result, "id"), *result))
        .collect();
    let arguments: HashMap<&str, &Record> = records
        .arguments
        .iter()
        .map(|argument| (text(argument, "id"), *argument))
        .collect();
    let mut relations: Vec<&Record> = records.relations.clone();
    relations.sort_by_key(|relation| text(relation, "id"));
    let mut order = Vec::new();
    for relation in relations {
        if text(relation, "predicate") != "strengthens" {
            continue;
        }
        let argument = relation
            .get("verification_result_id")
            .and_then(Value::as_str)
            .and_then(|id| results.get(id))
            .and_then(|result| arguments.get(text(result, "argument_id")));
        let Some(argument) = argument else { continue };
        if list(argument, "premise_statement_ids") != [text(relation, "subject_id")]
            || text(argument, "conclusion_statement_id") != text(relation, "object_id")
            || truthy(argument.get("commitment_statement_ids"))
        {
            continue;
        }
        order.push(StrengthEntry {
            strong: text(relation, "subject_id"),
            weak: text(relation, "object_id"),
            argument_id: text(argument, "id"),
        });
    }
    order
}

/// Declared kinds win over heuristic ones (Python `transcription_kinds`).
pub fn transcription_kinds(
    checkout: &Path,
    results: &[&Record],
) -> BTreeMap<String, TranscriptionKind> {
    let mut kinds = BTreeMap::new();
    for result in results {
        let heuristic = transcription::classify_result(
            checkout,
            text(result, "solution_module"),
            text(result, "theorem"),
        );
        let kind = match heuristic {
            Some(transcription::Heuristic::SingleApplication) => "single_application",
            Some(transcription::Heuristic::Assembly) => "assembly",
            None => continue,
        };
        kinds.insert(
            text(result, "id").to_owned(),
            TranscriptionKind {
                kind: kind.into(),
                declared: false,
            },
        );
    }
    for result in results {
        if let Some(declared) = result.get("transcription").filter(|v| truthy(Some(v))) {
            kinds.insert(
                text(result, "id").to_owned(),
                TranscriptionKind {
                    kind: declared.as_str().unwrap_or_default().to_owned(),
                    declared: true,
                },
            );
        }
    }
    kinds
}

/// The frontier quantities `thickness` and `thickness --queue` read.
pub fn frontier_inputs(
    root: &str,
    records: &Records,
    transcription_results: BTreeMap<String, TranscriptionKind>,
) -> FrontierInputs {
    let order = strength_order(records);
    let registration: HashSet<&str> = order.iter().map(|entry| entry.argument_id).collect();
    let arguments: Vec<&Record> = records
        .arguments
        .iter()
        .copied()
        .filter(|argument| !registration.contains(text(argument, "id")))
        .collect();
    let results: Vec<&Record> = records
        .results
        .iter()
        .copied()
        .filter(|result| !registration.contains(text(result, "argument_id")))
        .collect();
    let statement_by_id: HashMap<&str, &Record> = records
        .statements
        .iter()
        .map(|statement| (text(statement, "id"), *statement))
        .collect();
    let argument_by_id: HashMap<&str, &Record> = arguments
        .iter()
        .map(|argument| (text(argument, "id"), *argument))
        .collect();
    let result_by_id: HashMap<&str, &Record> = results
        .iter()
        .map(|result| (text(result, "id"), *result))
        .collect();
    let verified_arguments: HashSet<&str> = results
        .iter()
        .map(|result| text(result, "argument_id"))
        .collect();

    let mut dependents: HashMap<&str, BTreeSet<&str>> = HashMap::new();
    for argument in &arguments {
        for premise in list(argument, "premise_statement_ids") {
            dependents
                .entry(premise)
                .or_default()
                .insert(text(argument, "id"));
        }
    }
    let mut alternatives: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    let mut refutations: Vec<&Record> = Vec::new();
    let mut support: HashMap<&str, HashSet<&str>> = HashMap::new();
    let mut routes: HashMap<&str, HashSet<&str>> = HashMap::new();
    for relation in &records.relations {
        let (subject, object) = (text(relation, "subject_id"), text(relation, "object_id"));
        match text(relation, "predicate") {
            "alternative_to" => {
                alternatives.entry(object).or_default().insert(subject);
            }
            "refutes" => refutations.push(relation),
            "supports" => {
                support.entry(object).or_default().insert(subject);
            }
            "root_route" => {
                routes.entry(object).or_default().insert(subject);
            }
            _ => {}
        }
    }
    refutations.sort_by_key(|relation| text(relation, "id"));
    let mut refuting_arguments: HashMap<&str, HashSet<&str>> = HashMap::new();
    for relation in &refutations {
        refuting_arguments
            .entry(text(relation, "object_id"))
            .or_default()
            .insert(text(relation, "subject_id"));
    }
    let claim_statement: HashMap<&str, &str> = records
        .claims
        .iter()
        .map(|claim| (text(claim, "id"), text(claim, "statement_id")))
        .collect();
    let floor_markings: BTreeMap<&str, &Record> = statement_by_id
        .iter()
        .filter_map(|(id, statement)| {
            statement
                .get("self_evident")
                .and_then(Value::as_object)
                .map(|marking| (*id, marking))
        })
        .collect();

    let mut established: HashSet<&str> = HashSet::new();
    let mut refuted: HashSet<&str> = HashSet::new();
    let floor = Floor {
        alternatives: &alternatives,
        claim_statement: &claim_statement,
        result_by_id: &result_by_id,
        argument_by_id: &argument_by_id,
        refuting_arguments: &refuting_arguments,
        transcription_results: &transcription_results,
    };
    let refutation_counts = |relation: &Record, established: &HashSet<&str>| {
        let subject = text(relation, "subject_id");
        argument_by_id.get(subject).is_some_and(|argument| {
            verified_arguments.contains(subject)
                && list(argument, "premise_statement_ids")
                    .iter()
                    .all(|premise| established.contains(premise))
        })
    };
    let defended = |statement: &str, refuted: &HashSet<&str>| {
        alternatives.get(statement).is_some_and(|recorded| {
            !recorded.is_empty() && recorded.iter().all(|rival| refuted.contains(rival))
        })
    };
    let verified_steps: Vec<&Record> = results
        .iter()
        .filter_map(|result| argument_by_id.get(text(result, "argument_id")).copied())
        .collect();
    let mut changed = true;
    while changed {
        changed = false;
        for (statement, marking) in &floor_markings {
            if !established.contains(statement)
                && floor.met(statement, marking, &established, &refuted)
            {
                established.insert(statement);
                changed = true;
            }
        }
        for relation in &refutations {
            let object = text(relation, "object_id");
            if !refuted.contains(object) && refutation_counts(relation, &established) {
                refuted.insert(object);
                changed = true;
            }
        }
        for statement in alternatives.keys() {
            if !established.contains(statement) && defended(statement, &refuted) {
                established.insert(statement);
                changed = true;
            }
        }
        for argument in &verified_steps {
            let conclusion = text(argument, "conclusion_statement_id");
            if !established.contains(conclusion)
                && list(argument, "premise_statement_ids")
                    .iter()
                    .all(|premise| established.contains(premise))
            {
                established.insert(conclusion);
                changed = true;
            }
        }
        for entry in &order {
            if established.contains(entry.strong) && established.insert(entry.weak) {
                changed = true;
            }
            if refuted.contains(entry.weak) && refuted.insert(entry.strong) {
                changed = true;
            }
        }
    }
    let counted_refutations = refutations
        .iter()
        .map(|relation| {
            (
                (
                    text(relation, "subject_id").to_owned(),
                    text(relation, "object_id").to_owned(),
                ),
                refutation_counts(relation, &established),
            )
        })
        .collect();

    let mut stating: HashMap<&str, Vec<&Record>> = HashMap::new();
    for claim in &records.claims {
        stating
            .entry(text(claim, "statement_id"))
            .or_default()
            .push(claim);
    }
    let statement_depths = statement_by_id
        .keys()
        .map(|id| {
            let claims = stating.get(id).map(Vec::as_slice).unwrap_or_default();
            let depth = if claims.iter().any(|claim| {
                !matches!(
                    claim.get("witness").and_then(Value::as_str),
                    Some("bibliographic" | "unavailable")
                )
            }) {
                "stated"
            } else if !claims.is_empty() || support.get(id).is_some_and(|s| !s.is_empty()) {
                "supported"
            } else {
                "bare"
            };
            ((*id).to_owned(), depth)
        })
        .collect();

    // The route-aware upward walk: a routed conclusion is entered only through
    // its designated arguments; every argument met on the way counts.
    let premise_dependent_arguments = dependents
        .keys()
        .map(|premise| {
            let reached = breadth_first(*premise, |current: &&str| {
                dependents
                    .get(current)
                    .into_iter()
                    .flatten()
                    .filter_map(|argument_id| {
                        let conclusion =
                            text(argument_by_id[argument_id], "conclusion_statement_id");
                        let blocked = routes
                            .get(conclusion)
                            .is_some_and(|designated| !designated.contains(argument_id));
                        (!blocked).then_some(conclusion)
                    })
                    .collect::<Vec<_>>()
            });
            let arguments: HashSet<&str> = reached
                .into_iter()
                .flat_map(|statement| dependents.get(statement).into_iter().flatten().copied())
                .collect();
            ((*premise).to_owned(), arguments.len())
        })
        .collect();

    let mut concluding: HashMap<&str, Vec<&str>> = HashMap::new();
    for argument in &arguments {
        concluding
            .entry(text(argument, "conclusion_statement_id"))
            .or_default()
            .push(text(argument, "id"));
    }
    let reaching_root = if statement_by_id.contains_key(root) {
        breadth_first(root, |conclusion: &&str| {
            concluding
                .get(conclusion)
                .into_iter()
                .flatten()
                .filter(|argument_id| {
                    routes
                        .get(conclusion)
                        .is_none_or(|designated| designated.contains(*argument_id))
                })
                .flat_map(|argument_id| list(argument_by_id[argument_id], "premise_statement_ids"))
                .collect::<Vec<_>>()
        })
        .into_iter()
        .map(str::to_owned)
        .collect()
    } else {
        BTreeSet::new()
    };

    FrontierInputs {
        root: root.to_owned(),
        transcription_results,
        reaching_root,
        statement_depths,
        premise_dependent_arguments,
        counted_refutations,
    }
}

/// Floor-marking basis criteria (#500, #999, #1007), as Python `floor_reasons`.
struct Floor<'a, 'r> {
    alternatives: &'r BTreeMap<&'a str, BTreeSet<&'a str>>,
    claim_statement: &'r HashMap<&'a str, &'a str>,
    result_by_id: &'r HashMap<&'a str, &'a Record>,
    argument_by_id: &'r HashMap<&'a str, &'a Record>,
    refuting_arguments: &'r HashMap<&'a str, HashSet<&'a str>>,
    transcription_results: &'r BTreeMap<String, TranscriptionKind>,
}

impl Floor<'_, '_> {
    fn rivals(&self, statement: &str) -> Vec<&str> {
        self.alternatives
            .get(statement)
            .map(|rivals| rivals.iter().copied().collect())
            .unwrap_or_default()
    }

    fn stale(&self, statement: &str, marking: &Record) -> bool {
        let basis = Some(text(marking, "basis"))
            .filter(|basis| !basis.is_empty())
            .unwrap_or("legacy");
        let Some(disagreement) = marking.get("disagreement").filter(|v| !v.is_null()) else {
            return false;
        };
        if basis == "common_ground" && marking.get("owner_approval").is_none_or(Value::is_null) {
            return false;
        }
        let listed: HashSet<&str> = disagreement
            .as_object()
            .map(|object| list(object, "rival_statement_ids").into_iter().collect())
            .unwrap_or_default();
        self.rivals(statement)
            .iter()
            .any(|rival| !listed.contains(rival))
    }

    fn met(
        &self,
        statement: &str,
        marking: &Record,
        established: &HashSet<&str>,
        refuted: &HashSet<&str>,
    ) -> bool {
        if marking.get("owner_approval").is_some_and(|v| !v.is_null()) {
            return !self.stale(statement, marking);
        }
        if self.stale(statement, marking) {
            return false;
        }
        let rivals = self.rivals(statement);
        let justification = list(marking, "justification_ids");
        match Some(text(marking, "basis"))
            .filter(|basis| !basis.is_empty())
            .unwrap_or("legacy")
        {
            "legacy" => true,
            "retorsion" => {
                let Some(denial) = marking.get("denial_statement_id").and_then(Value::as_str)
                else {
                    return false;
                };
                if !rivals.contains(&denial) {
                    return false;
                }
                justification.is_empty()
                    || justification.iter().any(|result_id| {
                        let Some(argument) = self.result_by_id.get(result_id).and_then(|result| {
                            self.argument_by_id.get(text(result, "argument_id"))
                        }) else {
                            return false;
                        };
                        !self.transcription_results.contains_key(*result_id)
                            && self
                                .refuting_arguments
                                .get(denial)
                                .is_some_and(|set| set.contains(text(argument, "id")))
                            && list(argument, "premise_statement_ids")
                                .iter()
                                .all(|premise| established.contains(premise))
                    })
            }
            "common_ground" => {
                if !rivals.is_empty() {
                    return false;
                }
                let question = text(marking, "question_statement_id");
                let question_rivals = self.rivals(question);
                if question_rivals.is_empty() {
                    return false;
                }
                let mut committed: HashMap<&str, usize> = HashMap::new();
                for position in marking
                    .get("positions")
                    .and_then(Value::as_array)
                    .into_iter()
                    .flatten()
                    .filter_map(Value::as_object)
                {
                    let stating = list(position, "claim_ids")
                        .into_iter()
                        .filter(|claim| self.claim_statement.get(claim) == Some(&statement))
                        .count();
                    *committed.entry(text(position, "statement_id")).or_default() += stating;
                }
                std::iter::once(question)
                    .chain(question_rivals)
                    .all(|position| committed.get(position).is_some_and(|count| *count > 0))
            }
            _ => {
                // observation
                let sceptical: HashSet<&str> =
                    list(marking, "sceptical_rival_ids").into_iter().collect();
                justification
                    .iter()
                    .any(|claim| self.claim_statement.get(claim) == Some(&statement))
                    && rivals.iter().all(|rival| sceptical.contains(rival))
                    && rivals.iter().all(|rival| refuted.contains(rival))
            }
        }
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
            }
        }
    }

    fn declared(records: &Records) -> BTreeMap<String, TranscriptionKind> {
        let mut kinds = BTreeMap::new();
        for result in &records.results {
            if let Some(kind) = result.get("transcription").and_then(Value::as_str) {
                kinds.insert(
                    text(result, "id").to_owned(),
                    TranscriptionKind {
                        kind: kind.into(),
                        declared: true,
                    },
                );
            }
        }
        kinds
    }

    #[test]
    fn reaching_root_honors_routes_and_strength_registrations() {
        let fixture = Fixture::new();
        let records = fixture.records();
        let frontier = frontier_inputs("ROOT", &records, declared(&records));
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
        let frontier = frontier_inputs("ROOT", &records, declared(&records));
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

    #[test]
    fn floor_bases_follow_python() {
        let marking = |value: Value| value.as_object().cloned().unwrap_or_default();
        let alternatives = BTreeMap::from([("P", BTreeSet::from(["NOT-P"]))]);
        let claim_statement = HashMap::from([("CLAIM-P", "P")]);
        let (results, arguments, refuting, kinds) = (
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            BTreeMap::new(),
        );
        let floor = Floor {
            alternatives: &alternatives,
            claim_statement: &claim_statement,
            result_by_id: &results,
            argument_by_id: &arguments,
            refuting_arguments: &refuting,
            transcription_results: &kinds,
        };
        let none = HashSet::new();
        assert!(floor.met("P", &marking(json!({})), &none, &none));
        let observation = marking(
            json!({"basis": "observation", "justification_ids": ["CLAIM-P"],
                                         "sceptical_rival_ids": ["NOT-P"]}),
        );
        assert!(!floor.met("P", &observation, &none, &none));
        assert!(floor.met("P", &observation, &none, &HashSet::from(["NOT-P"])));
        // A retorsion with no justification has no failing justification.
        let retorsion = marking(json!({"basis": "retorsion", "denial_statement_id": "NOT-P"}));
        assert!(floor.met("P", &retorsion, &none, &none));
        // A stale disagreement record blocks even an owner-approved marking.
        let stale = marking(json!({"basis": "common_ground", "owner_approval": "x",
                                   "disagreement": {"rival_statement_ids": []}}));
        assert!(!floor.met("P", &stale, &none, &none));
    }
}
