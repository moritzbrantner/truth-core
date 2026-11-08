//! The premise frontier, ported from `scripts/corpus.py` (`frontier_report`,
//! `root_routes`, `statement_view`, `restrict_to_root`, `format_frontier`,
//! `format_routes`, `frontier_delta`, `format_frontier_delta`) and
//! `scripts/next_steps.py` (`next_steps_report`).
//!
//! Closure rules (a)-(d), the strength order (#1017), floor bases (#500,
//! #999, #1007), per-route open-premise costs (#391), source depths (#987)
//! and the next-step what-if probes are computed exactly as the Python
//! frontier computes them. The canonical corpus JSON stays the input; nothing
//! here writes a record, a cache or a status registry, and Lean/Comparator
//! keep proof authority: a "verified" argument is one with a result record.

use crate::thickness::{Record, Records, list, text, truthy};
use crate::transcription::{self, Definitions, Flag};
use serde_json::{Map, Value, json};
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    io::Write,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::{SystemTime, UNIX_EPOCH},
};

/// Stage conclusions of the root skeleton, by uuid (legacy ids in comments).
const STAGE_CONCLUSIONS: &[(u64, &str)] = &[
    (1, "8626f8a5-9531-5da7-9ebd-f901e74b1129"), // STMT-GOD-EXISTS
    (2, "d5ac1620-1de5-5cd8-862e-cfdfd6d8b8a5"), // STMT-GOD-HAS-CLASSICAL-DIVINE-ATTRIBUTES
    (3, "5fc7a6f9-94d7-5938-9e32-b2614c159646"), // STMT-REVELATION-POSSIBLE-AND-RECOGNIZABLE
    (4, "a88d9b81-1246-5844-a119-4be2af4dd3f9"), // STMT-JESUS-CLAIMED-DIVINE-AUTHORITY-AND-ROSE
    (5, "a8dfc0b8-140f-5351-a856-16a719251ac3"), // STMT-CHRIST-FOUNDED-VISIBLE-CHURCH
    (6, "09d4f44b-d7b7-59b1-aa0e-4f44d9c42267"), // STMT-CHRISTS-CHURCH-IS-THE-CATHOLIC-CHURCH
];
const BARE: &str = "bare";
const SUPPORTED: &str = "supported";
const STATED: &str = "stated";
const LEGACY_SOURCED: &str = "sourced";
const DEPTHS: [&str; 3] = [BARE, SUPPORTED, STATED];
const PROVED_UNESTABLISHED: &str = "proved_unestablished";
const CLOSED: &str = "closed";
const ABSENT: &str = "absent";
const SHORT_PROOF_STEPS: usize = 2;

type Upward<'a> = (Vec<&'a str>, Vec<&'a str>, Option<Vec<&'a str>>);

/// Python `transcription_flags`: the Lean-text heuristics for every result
/// whose Solution module and theorem exist, by result ID.
pub fn transcription_flags(checkout: &Path, records: &Records) -> Vec<Flag> {
    let definitions = Definitions::load(checkout);
    let argument_by_id: HashMap<&str, &Record> = records
        .arguments
        .iter()
        .map(|argument| (text(argument, "id"), *argument))
        .collect();
    let declaration_tail: HashMap<&str, &str> = records
        .statements
        .iter()
        .filter(|statement| truthy(statement.get("lean_declaration")))
        .map(|statement| {
            let declaration = text(statement, "lean_declaration");
            (
                text(statement, "id"),
                declaration.rsplit('.').next().unwrap_or(declaration),
            )
        })
        .collect();
    let mut results = records.results.clone();
    results.sort_by_key(|result| text(result, "id"));
    results
        .iter()
        .filter_map(|result| {
            let analysis = transcription::analyze_result(
                checkout,
                text(result, "solution_module"),
                text(result, "theorem"),
            )?;
            let argument_id = text(result, "argument_id");
            let premises = argument_by_id
                .get(argument_id)
                .map(|argument| list(argument, "premise_statement_ids"))
                .unwrap_or_default();
            transcription::flag(
                analysis,
                &definitions,
                &premises,
                &declaration_tail,
                text(result, "id"),
                argument_id,
            )
        })
        .collect()
}

/// `corpus_ids.order_key`: a record's legacy id when it has one, else its id.
fn order_key<'a>(id: &'a str, record: Option<&'a Record>) -> &'a str {
    record
        .and_then(|record| record.get("legacy_id"))
        .and_then(Value::as_str)
        .unwrap_or(id)
}

fn flag_json(flag: &Flag) -> Value {
    json!({
        "result_id": flag.result_id,
        "argument_id": flag.argument_id,
        "proof_steps": flag.proof_steps,
        "single_application_of": flag.single_application_of,
        "assembly_of": flag.assembly_of,
        "opaque_atoms": flag.opaque_atoms,
        "goal_consequent_premises": flag.goal_consequent_premises.iter().map(|premise| json!({
            "hypothesis": premise.hypothesis,
            "statement_ids": premise.statement_ids,
        })).collect::<Vec<_>>(),
    })
}

struct StrengthEntry<'a> {
    relation: &'a Record,
    strong: &'a str,
    weak: &'a str,
    result_id: &'a str,
    argument_id: &'a str,
}

/// Python `strength_order`: registrations whose result's argument has exactly
/// the strong version as premise and the weak version as conclusion.
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
    let mut relations = records.relations.clone();
    relations.sort_by_key(|relation| text(relation, "id"));
    let mut order = Vec::new();
    for relation in relations {
        if text(relation, "predicate") != "strengthens" {
            continue;
        }
        let Some(result) = relation
            .get("verification_result_id")
            .and_then(Value::as_str)
            .and_then(|id| results.get(id))
        else {
            continue;
        };
        let Some(argument) = arguments.get(text(result, "argument_id")) else {
            continue;
        };
        if list(argument, "premise_statement_ids") != [text(relation, "subject_id")]
            || text(argument, "conclusion_statement_id") != text(relation, "object_id")
            || truthy(argument.get("commitment_statement_ids"))
        {
            continue;
        }
        order.push(StrengthEntry {
            relation,
            strong: text(relation, "subject_id"),
            weak: text(relation, "object_id"),
            result_id: text(result, "id"),
            argument_id: text(argument, "id"),
        });
    }
    order
}

/// What the least fixpoint of rules (b)-(d) leaves.
struct Closure<'a> {
    closed: HashSet<&'a str>,
    refuted: HashSet<&'a str>,
    established: HashSet<&'a str>,
    /// conclusion -> (result, argument, sorted distinct premises)
    via_transcription: BTreeMap<&'a str, (&'a str, &'a str, Vec<&'a str>)>,
    /// weak/strong statement -> index of the strength entry that propagated
    established_via_strength: HashMap<&'a str, usize>,
    refuted_via_strength: HashMap<&'a str, usize>,
}

struct Route<'a> {
    argument_id: &'a str,
    cost: usize,
    premise_count: usize,
    verified: bool,
    transcription: bool,
    designated: bool,
    cheapest: bool,
    open: Vec<&'a str>,
    proved_unestablished: Vec<&'a str>,
}

/// The frontier's indexes over one set of records; closure is computed on
/// demand so that the next-step probes rerun exactly the same fixpoint.
pub struct Frontier<'a> {
    root: &'a str,
    records: &'a Records<'a>,
    flags: &'a [Flag],
    order: Vec<StrengthEntry<'a>>,
    arguments: Vec<&'a Record>,
    results: Vec<&'a Record>,
    statement_by_id: BTreeMap<&'a str, &'a Record>,
    argument_by_id: HashMap<&'a str, &'a Record>,
    result_by_id: HashMap<&'a str, &'a Record>,
    verified_arguments: HashSet<&'a str>,
    kinds: BTreeMap<&'a str, (Value, bool)>,
    transcription_results: HashSet<&'a str>,
    verified_conclusions: HashSet<&'a str>,
    transcription_only_conclusions: HashSet<&'a str>,
    dependents: BTreeMap<&'a str, BTreeSet<&'a str>>,
    alternatives: BTreeMap<&'a str, BTreeSet<&'a str>>,
    refutations: Vec<&'a Record>,
    objections: HashMap<&'a str, BTreeSet<String>>,
    support: HashMap<&'a str, BTreeSet<&'a str>>,
    routes: HashMap<&'a str, HashSet<&'a str>>,
    claim_statement: HashMap<&'a str, &'a str>,
    refuting_arguments: HashMap<&'a str, HashSet<&'a str>>,
    floor_markings: BTreeMap<&'a str, &'a Record>,
    stating_claims: HashMap<&'a str, BTreeSet<&'a str>>,
    bibliographic_claims: HashSet<&'a str>,
    unavailable_claims: HashSet<&'a str>,
    transcription_steps: Vec<(&'a str, &'a Record)>,
    verified_steps: Vec<&'a Record>,
    upward_cache: RefCell<HashMap<&'a str, Upward<'a>>>,
}

fn basis(marking: &Record) -> &str {
    Some(text(marking, "basis"))
        .filter(|basis| !basis.is_empty())
        .unwrap_or("legacy")
}

fn present(value: Option<&Value>) -> bool {
    value.is_some_and(|value| !value.is_null())
}

/// Python `str()` of an optional JSON string.
fn py_str(value: Option<&Value>) -> String {
    match value {
        None | Some(Value::Null) => "None".into(),
        Some(Value::String(text)) => text.clone(),
        Some(other) => other.to_string(),
    }
}

impl<'a> Frontier<'a> {
    pub fn new(root: &'a str, records: &'a Records<'a>, flags: &'a [Flag]) -> Self {
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
        let statement_by_id = records
            .statements
            .iter()
            .map(|statement| (text(statement, "id"), *statement))
            .collect();
        let argument_by_id: HashMap<&str, &Record> = arguments
            .iter()
            .map(|argument| (text(argument, "id"), *argument))
            .collect();
        let result_by_id = results
            .iter()
            .map(|result| (text(result, "id"), *result))
            .collect();
        let verified_arguments = results
            .iter()
            .map(|result| text(result, "argument_id"))
            .collect();

        // Python `transcription_kinds`: heuristic kinds, then declared ones.
        let mut kinds: BTreeMap<&str, (Value, bool)> = BTreeMap::new();
        for flag in flags {
            let Some(result) = records
                .results
                .iter()
                .find(|result| text(result, "id") == flag.result_id)
            else {
                continue;
            };
            if flag.single_application_of.is_some() {
                kinds.insert(text(result, "id"), (json!("single_application"), false));
            } else if flag
                .assembly_of
                .as_ref()
                .is_some_and(|found| !found.is_empty())
            {
                kinds.insert(text(result, "id"), (json!("assembly"), false));
            }
        }
        for result in &records.results {
            if let Some(declared) = result.get("transcription").filter(|v| truthy(Some(v))) {
                kinds.insert(text(result, "id"), (declared.clone(), true));
            }
        }
        let transcription_results: HashSet<&str> = kinds.keys().copied().collect();
        let mut verified_conclusions = HashSet::new();
        let mut all_conclusions = HashSet::new();
        for result in &results {
            if let Some(argument) = argument_by_id.get(text(result, "argument_id")) {
                let conclusion = text(argument, "conclusion_statement_id");
                all_conclusions.insert(conclusion);
                if !transcription_results.contains(text(result, "id")) {
                    verified_conclusions.insert(conclusion);
                }
            }
        }
        let transcription_only_conclusions = all_conclusions
            .difference(&verified_conclusions)
            .copied()
            .collect();

        let mut dependents: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
        for argument in &arguments {
            for premise in list(argument, "premise_statement_ids") {
                dependents
                    .entry(premise)
                    .or_default()
                    .insert(text(argument, "id"));
            }
        }
        let mut alternatives: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
        let mut refutations = Vec::new();
        let mut objections: HashMap<&str, BTreeSet<String>> = HashMap::new();
        let mut support: HashMap<&str, BTreeSet<&str>> = HashMap::new();
        let mut routes: HashMap<&str, HashSet<&str>> = HashMap::new();
        for relation in &records.relations {
            let (subject, object) = (text(relation, "subject_id"), text(relation, "object_id"));
            match text(relation, "predicate") {
                "alternative_to" => {
                    alternatives.entry(object).or_default().insert(subject);
                }
                "refutes" => refutations.push(*relation),
                "attacks" => {
                    objections
                        .entry(object)
                        .or_default()
                        .insert(format!("{}:{subject}", text(relation, "subject_kind")));
                }
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
        let claim_statement = records
            .claims
            .iter()
            .map(|claim| (text(claim, "id"), text(claim, "statement_id")))
            .collect();
        let floor_markings = records
            .statements
            .iter()
            .filter_map(|statement| {
                statement
                    .get("self_evident")
                    .and_then(Value::as_object)
                    .map(|marking| (text(statement, "id"), marking))
            })
            .collect();
        let mut stating_claims: HashMap<&str, BTreeSet<&str>> = HashMap::new();
        for claim in &records.claims {
            stating_claims
                .entry(text(claim, "statement_id"))
                .or_default()
                .insert(text(claim, "id"));
        }
        let witness_claims = |witness: &str| {
            records
                .claims
                .iter()
                .filter(|claim| claim.get("witness").and_then(Value::as_str) == Some(witness))
                .map(|claim| text(claim, "id"))
                .collect::<HashSet<_>>()
        };
        let bibliographic_claims = witness_claims("bibliographic");
        let unavailable_claims = witness_claims("unavailable");
        let mut transcription_steps: Vec<(&str, &Record)> = results
            .iter()
            .filter(|result| transcription_results.contains(text(result, "id")))
            .filter_map(|result| {
                argument_by_id
                    .get(text(result, "argument_id"))
                    .map(|argument| (text(result, "id"), *argument))
            })
            .collect();
        transcription_steps.sort_by_key(|(result_id, _)| *result_id);
        let verified_steps = results
            .iter()
            .filter_map(|result| argument_by_id.get(text(result, "argument_id")).copied())
            .collect();
        Self {
            root,
            records,
            flags,
            order,
            arguments,
            results,
            statement_by_id,
            argument_by_id,
            result_by_id,
            verified_arguments,
            kinds,
            transcription_results,
            verified_conclusions,
            transcription_only_conclusions,
            dependents,
            alternatives,
            refutations,
            objections,
            support,
            routes,
            claim_statement,
            refuting_arguments,
            floor_markings,
            stating_claims,
            bibliographic_claims,
            unavailable_claims,
            transcription_steps,
            verified_steps,
            upward_cache: RefCell::new(HashMap::new()),
        }
    }

    fn rivals(&self, statement: &str) -> Vec<&'a str> {
        self.alternatives
            .get(statement)
            .map(|rivals| rivals.iter().copied().collect())
            .unwrap_or_default()
    }

    fn premises(argument: &'a Record) -> Vec<&'a str> {
        list(argument, "premise_statement_ids")
    }

    /// Python `stale_disagreement`.
    fn stale_disagreement(&self, statement: &str) -> Vec<String> {
        let marking = self.floor_markings[statement];
        let Some(disagreement) = marking.get("disagreement").filter(|v| !v.is_null()) else {
            return Vec::new();
        };
        if basis(marking) == "common_ground" && !present(marking.get("owner_approval")) {
            return Vec::new();
        }
        let listed: HashSet<&str> = disagreement
            .as_object()
            .map(|object| list(object, "rival_statement_ids").into_iter().collect())
            .unwrap_or_default();
        let unlisted: Vec<&str> = self
            .rivals(statement)
            .into_iter()
            .filter(|rival| !listed.contains(rival))
            .collect();
        if unlisted.is_empty() {
            Vec::new()
        } else {
            vec![format!(
                "disagreement record omits recorded rivals: {}",
                unlisted.join(", ")
            )]
        }
    }

    /// Python `floor_reasons`: why a marking is not met now; empty when it is.
    fn floor_reasons(
        &self,
        statement: &str,
        established: &HashSet<&str>,
        refuted: &HashSet<&str>,
    ) -> Vec<String> {
        if present(self.floor_markings[statement].get("owner_approval")) {
            return self.stale_disagreement(statement);
        }
        self.criterion_reasons(statement, established, refuted)
    }

    /// Python `criterion_reasons`.
    fn criterion_reasons(
        &self,
        statement: &str,
        established: &HashSet<&str>,
        refuted: &HashSet<&str>,
    ) -> Vec<String> {
        let marking = self.floor_markings[statement];
        let rivals = self.rivals(statement);
        let justification = list(marking, "justification_ids");
        let stale = self.stale_disagreement(statement);
        if !stale.is_empty() {
            return stale;
        }
        match basis(marking) {
            "legacy" => Vec::new(),
            "retorsion" => {
                let denial = marking.get("denial_statement_id");
                let denial_id = denial.and_then(Value::as_str).unwrap_or_default();
                if denial.and_then(Value::as_str).is_none() || !rivals.contains(&denial_id) {
                    return vec![format!(
                        "denial {} is not recorded as alternative_to {statement}",
                        py_str(denial)
                    )];
                }
                let mut reasons = Vec::new();
                for result_id in justification {
                    let argument = self
                        .result_by_id
                        .get(result_id)
                        .and_then(|result| self.argument_by_id.get(text(result, "argument_id")));
                    let Some(argument) = argument else {
                        reasons.push(format!("{result_id} has no argument"));
                        continue;
                    };
                    let argument_id = text(argument, "id");
                    if self.transcription_results.contains(result_id) {
                        reasons.push(format!("{result_id} is a transcription"));
                    } else if !self
                        .refuting_arguments
                        .get(denial_id)
                        .is_some_and(|set| set.contains(argument_id))
                    {
                        reasons.push(format!(
                            "{argument_id} has no refutes relation to {denial_id}"
                        ));
                    } else {
                        let open: BTreeSet<&str> = Self::premises(argument)
                            .into_iter()
                            .filter(|premise| !established.contains(premise))
                            .collect();
                        if open.is_empty() {
                            return Vec::new();
                        }
                        reasons.push(format!(
                            "{result_id} rests on unestablished premises {}",
                            open.into_iter().collect::<Vec<_>>().join(", ")
                        ));
                    }
                }
                reasons
            }
            "common_ground" => {
                if !rivals.is_empty() {
                    return vec![format!("recorded rivals deny it: {}", rivals.join(", "))];
                }
                let question = marking.get("question_statement_id");
                let question_id = question.and_then(Value::as_str).unwrap_or_default();
                let question_rivals = self.rivals(question_id);
                if question_rivals.is_empty() {
                    return vec![format!(
                        "no rival position recorded on {}",
                        py_str(question)
                    )];
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
                let missing: Vec<&str> = std::iter::once(question_id)
                    .chain(question_rivals)
                    .filter(|position| committed.get(position).is_none_or(|count| *count == 0))
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
            _ => {
                let mut reasons = Vec::new();
                if !justification
                    .iter()
                    .any(|claim| self.claim_statement.get(claim) == Some(&statement))
                {
                    reasons.push("no justification claim states it".to_owned());
                }
                let sceptical: HashSet<&str> =
                    list(marking, "sceptical_rival_ids").into_iter().collect();
                let not_sceptical: Vec<&str> = rivals
                    .iter()
                    .copied()
                    .filter(|rival| !sceptical.contains(rival))
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
                    .filter(|rival| sceptical.contains(rival) && !refuted.contains(rival))
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
    }

    fn refutation_counts(&self, relation: &Record, established: &HashSet<&str>) -> bool {
        let subject = text(relation, "subject_id");
        self.argument_by_id.get(subject).is_some_and(|argument| {
            self.verified_arguments.contains(subject)
                && Self::premises(argument)
                    .iter()
                    .all(|premise| established.contains(premise))
        })
    }

    fn defended(&self, statement: &str, refuted: &HashSet<&str>) -> bool {
        self.alternatives.get(statement).is_some_and(|recorded| {
            !recorded.is_empty() && recorded.iter().all(|rival| refuted.contains(rival))
        })
    }

    /// Rules (b)-(d) and the strength order, jointly to a least fixpoint, in
    /// the Python pass order (the order decides only which rule is recorded).
    fn closure(&self, hypothesis: Option<&'a str>) -> Closure<'a> {
        let mut closed = self.verified_conclusions.clone();
        let mut refuted: HashSet<&str> = HashSet::new();
        let mut established: HashSet<&str> = HashSet::new();
        if let Some(hypothesis) = hypothesis {
            closed.insert(hypothesis);
            established.insert(hypothesis);
        }
        let mut via_transcription = BTreeMap::new();
        let mut established_via_strength = HashMap::new();
        let mut refuted_via_strength = HashMap::new();
        let mut changed = true;
        while changed {
            changed = false;
            for &statement in self.floor_markings.keys() {
                if !established.contains(statement)
                    && self
                        .floor_reasons(statement, &established, &refuted)
                        .is_empty()
                {
                    closed.insert(statement);
                    established.insert(statement);
                    changed = true;
                }
            }
            for relation in &self.refutations {
                let object = text(relation, "object_id");
                if !refuted.contains(object) && self.refutation_counts(relation, &established) {
                    refuted.insert(object);
                    changed = true;
                }
            }
            for &statement in self.alternatives.keys() {
                if !established.contains(statement) && self.defended(statement, &refuted) {
                    closed.insert(statement);
                    established.insert(statement);
                    changed = true;
                }
            }
            for argument in &self.verified_steps {
                let conclusion = text(argument, "conclusion_statement_id");
                if !established.contains(conclusion)
                    && Self::premises(argument)
                        .iter()
                        .all(|premise| established.contains(premise))
                {
                    established.insert(conclusion);
                    changed = true;
                }
            }
            for (index, entry) in self.order.iter().enumerate() {
                if established.contains(entry.strong) && !established.contains(entry.weak) {
                    established.insert(entry.weak);
                    closed.insert(entry.weak);
                    established_via_strength.insert(entry.weak, index);
                    changed = true;
                }
                if refuted.contains(entry.weak) && !refuted.contains(entry.strong) {
                    refuted.insert(entry.strong);
                    refuted_via_strength.insert(entry.strong, index);
                    changed = true;
                }
            }
            for (result_id, argument) in &self.transcription_steps {
                let conclusion = text(argument, "conclusion_statement_id");
                if closed.contains(conclusion) {
                    continue;
                }
                let premises = Self::premises(argument);
                if premises.iter().all(|premise| closed.contains(premise)) {
                    closed.insert(conclusion);
                    let distinct: BTreeSet<&str> = premises.into_iter().collect();
                    via_transcription.insert(
                        conclusion,
                        (
                            *result_id,
                            text(argument, "id"),
                            distinct.into_iter().collect(),
                        ),
                    );
                    changed = true;
                }
            }
        }
        Closure {
            closed,
            refuted,
            established,
            via_transcription,
            established_via_strength,
            refuted_via_strength,
        }
    }

    /// `corpus_ids.order_key` of an argument: its legacy id, else its id.
    /// Ties break by it so the uuid migration changed no route choice.
    fn argument_order(&self, argument_id: &'a str) -> &'a str {
        order_key(argument_id, self.argument_by_id.get(argument_id).copied())
    }

    /// `corpus_ids.order_key` of a statement.
    fn statement_order(&self, statement_id: &'a str) -> &'a str {
        order_key(
            statement_id,
            self.statement_by_id.get(statement_id).copied(),
        )
    }

    fn sourced(&self, statement: &str) -> bool {
        self.stating_claims
            .get(statement)
            .is_some_and(|claims| !claims.is_empty())
            || self.support.get(statement).is_some_and(|s| !s.is_empty())
    }

    /// Python `root_routes`: per-route open-premise leaves (#391).
    fn root_routes(&self, closure: &Closure<'a>) -> (Option<&'a str>, Vec<Route<'a>>) {
        let mut results_by_argument: HashMap<&str, Vec<&str>> = HashMap::new();
        for result in &self.results {
            results_by_argument
                .entry(text(result, "argument_id"))
                .or_default()
                .push(text(result, "id"));
        }
        let mut statement_ids: HashSet<&str> = self.statement_by_id.keys().copied().collect();
        for argument in &self.arguments {
            statement_ids.extend(Self::premises(argument));
            statement_ids.insert(text(argument, "conclusion_statement_id"));
        }
        let mut proofs: Vec<(&str, &Record)> = results_by_argument
            .iter()
            .filter(|(_, result_ids)| {
                result_ids
                    .iter()
                    .any(|id| !self.transcription_results.contains(id))
            })
            .filter_map(|(argument_id, _)| {
                self.argument_by_id
                    .get(argument_id)
                    .map(|argument| (*argument_id, *argument))
            })
            .collect();
        proofs.sort_by_key(|(argument_id, _)| self.argument_order(argument_id));
        let proofs: Vec<(&str, Vec<&str>)> = proofs
            .into_iter()
            .map(|(_, argument)| {
                let premises: BTreeSet<&str> = Self::premises(argument).into_iter().collect();
                (
                    text(argument, "conclusion_statement_id"),
                    premises.into_iter().collect(),
                )
            })
            .collect();
        let expandable: HashSet<&str> = proofs.iter().map(|(conclusion, _)| *conclusion).collect();
        let mut leaves: HashMap<&str, Option<BTreeSet<&str>>> = statement_ids
            .iter()
            .map(|&statement| {
                let value = if closure.established.contains(statement) {
                    Some(BTreeSet::new())
                } else if self.sourced(statement) || !expandable.contains(statement) {
                    Some(BTreeSet::from([statement]))
                } else {
                    None
                };
                (statement, value)
            })
            .collect();
        let propagate = |leaves: &mut HashMap<&'a str, Option<BTreeSet<&'a str>>>| {
            let mut changed = true;
            while changed {
                changed = false;
                for (conclusion, premises) in &proofs {
                    let mut candidate = BTreeSet::new();
                    let mut complete = true;
                    for premise in premises {
                        match &leaves[premise] {
                            Some(set) => candidate.extend(set.iter().copied()),
                            None => {
                                complete = false;
                                break;
                            }
                        }
                    }
                    if !complete {
                        continue;
                    }
                    let current = &leaves[conclusion];
                    if current
                        .as_ref()
                        .is_none_or(|current| candidate.len() < current.len())
                    {
                        leaves.insert(conclusion, Some(candidate));
                        changed = true;
                    }
                }
            }
        };
        propagate(&mut leaves);
        loop {
            let unresolved: BTreeSet<&str> = leaves
                .iter()
                .filter(|(_, value)| value.is_none())
                .map(|(statement, _)| *statement)
                .collect();
            if unresolved.is_empty() {
                break;
            }
            let mut dependencies: HashMap<&str, BTreeSet<&str>> =
                unresolved.iter().map(|s| (*s, BTreeSet::new())).collect();
            for (conclusion, premises) in &proofs {
                if let Some(entry) = dependencies.get_mut(conclusion) {
                    entry.extend(premises.iter().filter(|p| unresolved.contains(*p)));
                }
            }
            let reachable = |seed: &'a str| -> BTreeSet<&'a str> {
                let mut reached = BTreeSet::new();
                let mut pending = vec![seed];
                while let Some(node) = pending.pop() {
                    if reached.insert(node) {
                        pending.extend(
                            dependencies[node]
                                .iter()
                                .filter(|next| !reached.contains(*next)),
                        );
                    }
                }
                reached
            };
            let mut seeds: Vec<&str> = unresolved.iter().copied().collect();
            seeds.sort_by_key(|statement| self.statement_order(statement));
            let ordered = |component: &BTreeSet<&'a str>| {
                let mut keys: Vec<&str> = component
                    .iter()
                    .map(|statement| self.statement_order(statement))
                    .collect();
                keys.sort_unstable();
                keys
            };
            let core = seeds
                .into_iter()
                .map(reachable)
                .min_by(|a, b| {
                    a.len()
                        .cmp(&b.len())
                        .then_with(|| ordered(a).cmp(&ordered(b)))
                })
                .unwrap_or_default();
            for statement in core {
                leaves.insert(statement, Some(BTreeSet::from([statement])));
            }
            propagate(&mut leaves);
        }

        let designated = self.routes.get(self.root);
        let mut argument_ids: Vec<&str> = self.argument_by_id.keys().copied().collect();
        argument_ids.sort_by_key(|argument_id| self.argument_order(argument_id));
        let mut entries = Vec::new();
        for argument_id in argument_ids {
            let argument = self.argument_by_id[argument_id];
            if text(argument, "conclusion_statement_id") != self.root {
                continue;
            }
            let premises: BTreeSet<&str> = Self::premises(argument).into_iter().collect();
            let open: BTreeSet<&str> = premises
                .iter()
                .flat_map(|premise| leaves[premise].iter().flatten().copied())
                .collect();
            let result_ids = results_by_argument
                .get(argument_id)
                .map(Vec::as_slice)
                .unwrap_or_default();
            entries.push(Route {
                argument_id,
                cost: open.len(),
                premise_count: premises.len(),
                verified: !result_ids.is_empty(),
                transcription: !result_ids.is_empty()
                    && result_ids
                        .iter()
                        .all(|id| self.transcription_results.contains(id)),
                designated: designated.is_some_and(|set| set.contains(argument_id)),
                cheapest: false,
                proved_unestablished: open
                    .iter()
                    .copied()
                    .filter(|premise| closure.closed.contains(premise))
                    .collect(),
                open: open.into_iter().collect(),
            });
        }
        let cheapest = entries
            .iter_mut()
            .filter(|entry| entry.verified)
            .min_by(|a, b| {
                (a.cost, self.argument_order(a.argument_id))
                    .cmp(&(b.cost, self.argument_order(b.argument_id)))
            });
        let cheapest_id = cheapest.map(|entry| {
            entry.cheapest = true;
            entry.argument_id
        });
        entries.sort_by(|a, b| {
            (!a.verified, a.cost, self.argument_order(a.argument_id)).cmp(&(
                !b.verified,
                b.cost,
                self.argument_order(b.argument_id),
            ))
        });
        (cheapest_id, entries)
    }

    /// The route costs after establishing `hypothesis` alone (next-step probe).
    fn probe(&self, hypothesis: &'a str) -> HashMap<&'a str, usize> {
        let closure = self.closure(Some(hypothesis));
        self.root_routes(&closure)
            .1
            .into_iter()
            .map(|route| (route.argument_id, route.cost))
            .collect()
    }

    /// Python `upward`: the route-aware breadth-first walk from a premise.
    fn upward(&self, statement: &'a str) -> Upward<'a> {
        if let Some(cached) = self.upward_cache.borrow().get(statement) {
            return cached.clone();
        }
        let mut seen_arguments = Vec::new();
        let mut seen_statements = Vec::new();
        let mut visited_arguments = HashSet::new();
        let mut visited_statements = HashSet::from([statement]);
        let mut parent: HashMap<&str, (&str, &str)> = HashMap::new();
        let mut frontier = vec![statement];
        while !frontier.is_empty() {
            let mut layer = Vec::new();
            for current in &frontier {
                for argument_id in self.dependents.get(current).into_iter().flatten() {
                    let conclusion =
                        text(self.argument_by_id[argument_id], "conclusion_statement_id");
                    layer.push((*argument_id, conclusion, *current));
                }
            }
            layer.sort_by_key(|(argument_id, conclusion, current)| {
                (
                    self.argument_order(argument_id),
                    self.statement_order(conclusion),
                    self.statement_order(current),
                )
            });
            let mut next = Vec::new();
            for (argument_id, conclusion, current) in layer {
                if visited_arguments.insert(argument_id) {
                    seen_arguments.push(argument_id);
                }
                if self
                    .routes
                    .get(conclusion)
                    .is_some_and(|designated| !designated.contains(argument_id))
                {
                    continue;
                }
                if visited_statements.insert(conclusion) {
                    parent.insert(conclusion, (argument_id, current));
                    seen_statements.push(conclusion);
                    next.push(conclusion);
                }
            }
            next.sort_by_key(|statement| self.statement_order(statement));
            frontier = next;
        }
        let path = parent.contains_key(self.root).then(|| {
            let mut path = vec![self.root];
            let mut node = self.root;
            while node != statement {
                let (argument_id, previous) = parent[node];
                node = previous;
                path.splice(0..0, [node, argument_id]);
            }
            path
        });
        let walk = (seen_arguments, seen_statements, path);
        self.upward_cache
            .borrow_mut()
            .insert(statement, walk.clone());
        walk
    }

    fn source_depth(&self, statement: &str) -> &'static str {
        let stating = self.stating_claims.get(statement);
        if stating.is_some_and(|claims| {
            claims.iter().any(|claim| {
                !self.bibliographic_claims.contains(claim)
                    && !self.unavailable_claims.contains(claim)
            })
        }) {
            STATED
        } else if stating.is_some_and(|claims| !claims.is_empty())
            || self.support.get(statement).is_some_and(|s| !s.is_empty())
        {
            SUPPORTED
        } else {
            BARE
        }
    }

    /// Python `frontier_report`; `next_steps` adds the next-work projection.
    pub fn report(&self, next_steps: bool) -> Value {
        let closure = self.closure(None);
        let Closure {
            closed,
            refuted,
            established,
            ..
        } = &closure;

        let refutation_report: Vec<Value> = self
            .refutations
            .iter()
            .map(|relation| {
                let subject = text(relation, "subject_id");
                let premises: BTreeSet<&str> = self
                    .argument_by_id
                    .get(subject)
                    .map(|argument| Self::premises(argument).into_iter().collect())
                    .unwrap_or_default();
                json!({
                    "relation_id": text(relation, "id"),
                    "argument_id": subject,
                    "statement_id": text(relation, "object_id"),
                    "verified": self.verified_arguments.contains(subject),
                    "open_premise_statement_ids": premises.iter().filter(|p| !closed.contains(*p)).collect::<Vec<_>>(),
                    "unestablished_premise_statement_ids": premises.iter().filter(|p| !established.contains(*p)).collect::<Vec<_>>(),
                    "counted": self.refutation_counts(relation, established),
                })
            })
            .collect();

        let mut floor_report: Vec<Value> = Vec::new();
        let mut floor_met = HashSet::new();
        for (&statement, marking) in &self.floor_markings {
            let reasons = self.floor_reasons(statement, established, refuted);
            if reasons.is_empty() {
                floor_met.insert(statement);
            }
            let mut justification = list(marking, "justification_ids");
            justification.sort_unstable();
            let reaches = statement == self.root || self.upward(statement).2.is_some();
            floor_report.push(json!({
                "statement_id": statement,
                "basis": basis(marking),
                "met": reasons.is_empty(),
                "reasons": reasons,
                "justification_ids": justification,
                "disagreement": marking.get("disagreement").cloned().unwrap_or(Value::Null),
                "owner_approval": marking.get("owner_approval").cloned().unwrap_or(Value::Null),
                "criterion_reasons": self.criterion_reasons(statement, established, refuted),
                "reaches_root": reaches,
            }));
        }

        let mut closed_statements = Map::new();
        let mut sorted_closed: Vec<&str> = closed.iter().copied().collect();
        sorted_closed.sort_unstable();
        for statement in sorted_closed {
            let reason = if self.verified_conclusions.contains(statement) {
                "proved"
            } else if floor_met.contains(statement) {
                "self_evident"
            } else if self.defended(statement, refuted) {
                "alternatives_refuted"
            } else if closure.established_via_strength.contains_key(statement) {
                "via_strength"
            } else {
                "via_transcription"
            };
            closed_statements.insert(statement.to_owned(), json!(reason));
        }

        let (cheapest, routes) = self.root_routes(&closure);
        let route_entries: Vec<Value> = routes
            .iter()
            .map(|route| {
                let unestablished: HashSet<&str> =
                    route.proved_unestablished.iter().copied().collect();
                let mut depths = Map::new();
                let mut counts: BTreeMap<&str, usize> = DEPTHS
                    .iter()
                    .chain([&PROVED_UNESTABLISHED])
                    .map(|depth| (*depth, 0))
                    .collect();
                for statement in &route.open {
                    let depth = if unestablished.contains(statement) {
                        PROVED_UNESTABLISHED
                    } else {
                        self.source_depth(statement)
                    };
                    depths.insert((*statement).to_owned(), json!(depth));
                    *counts.entry(depth).or_default() += 1;
                }
                json!({
                    "argument_id": route.argument_id,
                    "cost": route.cost,
                    "premise_count": route.premise_count,
                    "verified": route.verified,
                    "transcription": route.transcription,
                    "designated": route.designated,
                    "cheapest": route.cheapest,
                    "open_premise_statement_ids": route.open,
                    "proved_unestablished_statement_ids": route.proved_unestablished,
                    "open_premise_depths": depths,
                    "depth_counts": counts,
                })
            })
            .collect();
        let floor_bases: Vec<Value> = floor_report
            .iter()
            .filter(|entry| entry["met"] == true && entry["reaches_root"] == true)
            .map(|entry| json!({"statement_id": entry["statement_id"], "basis": entry["basis"]}))
            .collect();
        let route_report = json!({
            "root": self.root,
            "cheapest_argument_id": cheapest,
            "routes": route_entries,
            "floor_bases": floor_bases,
        });

        let mut goal_premise_arguments: HashMap<&str, Vec<&str>> = HashMap::new();
        for flag in self.flags {
            for premise in &flag.goal_consequent_premises {
                for statement in &premise.statement_ids {
                    goal_premise_arguments
                        .entry(statement)
                        .or_default()
                        .push(&flag.argument_id);
                }
            }
        }
        let floor_by_id: HashMap<&str, &Value> = floor_report
            .iter()
            .map(|entry| (entry["statement_id"].as_str().unwrap_or_default(), entry))
            .collect();
        let empty = BTreeSet::new();
        let mut items: Vec<(Value, bool, usize, usize, &str)> = Vec::new();
        for (&statement, dependent_arguments) in &self.dependents {
            if closed.contains(statement) {
                continue;
            }
            let (all_arguments, all_conclusions, path) = self.upward(statement);
            let stating = self.stating_claims.get(statement).unwrap_or(&empty);
            let supporting = self.support.get(statement).unwrap_or(&empty);
            let pointing: BTreeSet<&str> = stating.union(supporting).copied().collect();
            let mut item = json!({
                "statement_id": statement,
                "paraphrase": self.statement_by_id.get(statement)
                    .and_then(|record| record.get("paraphrase")).cloned().unwrap_or(json!("")),
                "transcription_only": self.transcription_only_conclusions.contains(statement),
                "dependent_arguments": dependent_arguments,
                "transitive_dependent_arguments": all_arguments,
                "transitive_dependent_statements": all_conclusions,
                "path_to_root": path,
                "alternatives": self.rivals(statement).iter().map(|alternative| json!({
                    "statement_id": alternative, "refuted": refuted.contains(alternative),
                })).collect::<Vec<_>>(),
                "objections": self.objections.get(statement).cloned().unwrap_or_default(),
                "supporting_claims": supporting,
                "stating_claims": stating,
                "bibliographic_claims": pointing.iter().filter(|c| self.bibliographic_claims.contains(*c)).collect::<Vec<_>>(),
                "unavailable_claims": pointing.iter().filter(|c| self.unavailable_claims.contains(*c)).collect::<Vec<_>>(),
                "depth": self.source_depth(statement),
            });
            let mut premise_of = goal_premise_arguments
                .get(statement)
                .cloned()
                .unwrap_or_default();
            premise_of.sort_unstable();
            item["transcription_premise_of"] = json!(premise_of);
            if let Some(entry) = floor_by_id.get(statement) {
                item["floor_unmet"] = json!({"basis": entry["basis"], "reasons": entry["reasons"]});
            }
            items.push((
                item,
                path.is_none(),
                all_arguments.len(),
                dependent_arguments.len(),
                statement,
            ));
        }
        items.sort_by(|a, b| {
            (a.1, std::cmp::Reverse(a.2), std::cmp::Reverse(a.3), a.4).cmp(&(
                b.1,
                std::cmp::Reverse(b.2),
                std::cmp::Reverse(b.3),
                b.4,
            ))
        });
        let items: Vec<Value> = items.into_iter().map(|item| item.0).collect();

        let mut reaching_root: BTreeSet<&str> = BTreeSet::new();
        if self.statement_by_id.contains_key(self.root) {
            let mut concluding: HashMap<&str, Vec<&str>> = HashMap::new();
            for argument in &self.arguments {
                concluding
                    .entry(text(argument, "conclusion_statement_id"))
                    .or_default()
                    .push(text(argument, "id"));
            }
            reaching_root.insert(self.root);
            let mut pending = vec![self.root];
            while let Some(conclusion) = pending.pop() {
                for argument_id in concluding.get(conclusion).into_iter().flatten() {
                    if self
                        .routes
                        .get(conclusion)
                        .is_some_and(|designated| !designated.contains(argument_id))
                    {
                        continue;
                    }
                    for premise in Self::premises(self.argument_by_id[argument_id]) {
                        if reaching_root.insert(premise) {
                            pending.push(premise);
                        }
                    }
                }
            }
        }
        let closures: Vec<Value> = closure
            .via_transcription
            .iter()
            .map(|(statement, (result_id, argument_id, premises))| {
                json!({
                    "statement_id": statement,
                    "result_id": result_id,
                    "argument_id": argument_id,
                    "premise_statement_ids": premises,
                    "path_to_root": self.upward(statement).2,
                })
            })
            .collect();
        let strength: Vec<Value> = self
            .order
            .iter()
            .enumerate()
            .map(|(index, entry)| {
                json!({
                    "relation_id": text(entry.relation, "id"),
                    "strong_statement_id": entry.strong,
                    "weak_statement_id": entry.weak,
                    "result_id": entry.result_id,
                    "argument_id": entry.argument_id,
                    "strictness_result_id": entry.relation.get("strictness_result_id").cloned().unwrap_or(Value::Null),
                    "weak_established_via_strength": closure.established_via_strength.get(entry.weak) == Some(&index),
                    "strong_refuted_via_strength": closure.refuted_via_strength.get(entry.strong) == Some(&index),
                })
            })
            .collect();
        let transcription_results: Map<String, Value> = self
            .kinds
            .iter()
            .map(|(id, (kind, declared))| {
                (
                    (*id).to_owned(),
                    json!({"kind": kind, "declared": declared}),
                )
            })
            .collect();
        let sorted = |set: &HashSet<&'a str>| {
            let mut ids: Vec<&str> = set.iter().copied().collect();
            ids.sort_unstable();
            ids
        };
        let defended: HashSet<&str> = self
            .statement_by_id
            .keys()
            .copied()
            .filter(|statement| self.defended(statement, refuted))
            .collect();
        let open_ids: HashSet<&str> = items
            .iter()
            .filter_map(|item| item["statement_id"].as_str())
            .collect();
        let mut report = json!({
            "root": self.root,
            "root_known": self.statement_by_id.contains_key(self.root),
            "transcription_flags": self.flags.iter().map(flag_json).collect::<Vec<_>>(),
            "transcription_results": transcription_results,
            "closed_via_transcription": closures,
            "refutations": refutation_report,
            "refuted_statements": sorted(refuted),
            "strength_order": strength,
            "routes": route_report,
            "closed_statements": closed_statements,
            "floor": floor_report,
            "established_statements": sorted(established),
            "reaching_root_statements": reaching_root,
            "alternatives_recorded": !self.alternatives.is_empty(),
            "open_premise_count": items.len(),
            "depth_counts": depth_counts(&items),
            "statement_depths": self.statement_by_id.keys()
                .map(|id| ((*id).to_owned(), json!(self.source_depth(id))))
                .collect::<Map<_, _>>(),
            "items": items,
        });
        for (key, value) in self.statement_view(&floor_met, &defended, &open_ids) {
            report[key] = value;
        }
        if next_steps {
            report["next_steps"] = self.next_steps(&report);
        }
        report
    }

    /// Python `statement_view`: per-statement projections for views.
    fn statement_view(
        &self,
        floor_met: &HashSet<&str>,
        defended: &HashSet<&str>,
        open_premises: &HashSet<&str>,
    ) -> Vec<(&'static str, Value)> {
        let mut verifying: HashMap<&str, Vec<&str>> = HashMap::new();
        for result in &self.results {
            if let Some(argument) = self.argument_by_id.get(text(result, "argument_id")) {
                verifying
                    .entry(text(argument, "conclusion_statement_id"))
                    .or_default()
                    .push(text(result, "id"));
            }
        }
        let relations = &self.records.relations;
        let alternative_subjects: HashSet<&str> = relations
            .iter()
            .filter(|relation| text(relation, "predicate") == "alternative_to")
            .map(|relation| text(relation, "subject_id"))
            .collect();
        let objection_subjects: HashSet<&str> = relations
            .iter()
            .filter(|relation| {
                text(relation, "predicate") == "attacks"
                    && relation.get("subject_kind").and_then(Value::as_str) == Some("statement")
            })
            .map(|relation| text(relation, "subject_id"))
            .collect();
        let used_inferences: HashSet<&str> = self
            .arguments
            .iter()
            .flat_map(|argument| list(argument, "inference_ids"))
            .collect();
        let inferences = &self.records.inferences;
        let derived: HashSet<&str> = inferences
            .iter()
            .filter(|inference| used_inferences.contains(text(inference, "id")))
            .map(|inference| text(inference, "output_statement_id"))
            .collect();
        let mut statuses = Map::new();
        for &statement in self.statement_by_id.keys() {
            let proving = verifying
                .get(statement)
                .map(Vec::as_slice)
                .unwrap_or_default();
            let status = if !proving.is_empty() {
                if proving
                    .iter()
                    .all(|id| self.transcription_results.contains(id))
                {
                    "transcription"
                } else {
                    "proved"
                }
            } else if floor_met.contains(statement) {
                "self-evident"
            } else if defended.contains(statement) {
                "defended"
            } else if alternative_subjects.contains(statement) {
                "alternative"
            } else if objection_subjects.contains(statement) {
                "objection"
            } else if open_premises.contains(statement) {
                "open"
            } else if derived.contains(statement) {
                "derived"
            } else {
                "source-only"
            };
            statuses.insert(statement.to_owned(), json!(status));
        }

        let mut producers: HashMap<&str, Vec<Vec<&str>>> = HashMap::new();
        for inference in inferences {
            let mut inputs = list(inference, "input_statement_ids");
            inputs.extend(list(inference, "assumption_statement_ids"));
            producers
                .entry(text(inference, "output_statement_id"))
                .or_default()
                .push(inputs);
        }
        let rests_on = |start: &'a str| -> BTreeSet<&'a str> {
            let mut seen = BTreeSet::from([start]);
            let mut pending = vec![start];
            while let Some(node) = pending.pop() {
                for inputs in producers.get(node).into_iter().flatten() {
                    for statement in inputs {
                        if seen.insert(statement) {
                            pending.push(statement);
                        }
                    }
                }
            }
            seen
        };
        let stages: Vec<(u64, &str)> = STAGE_CONCLUSIONS
            .iter()
            .copied()
            .filter(|(_, statement)| self.statement_by_id.contains_key(statement))
            .collect();
        let mut statement_stages: BTreeMap<&str, Vec<u64>> = BTreeMap::new();
        for (stage, statement) in &stages {
            for reached in rests_on(statement) {
                statement_stages.entry(reached).or_default().push(*stage);
            }
        }
        let default_target = if self.statement_by_id.contains_key(self.root) {
            Some(self.root)
        } else {
            let verified: HashSet<&str> = self
                .results
                .iter()
                .map(|result| text(result, "argument_id"))
                .collect();
            let conclusions: BTreeSet<&str> = self
                .arguments
                .iter()
                .filter(|argument| verified.contains(text(argument, "id")))
                .map(|argument| text(argument, "conclusion_statement_id"))
                .collect();
            let mut best = 0;
            let mut target = None;
            for conclusion in conclusions {
                let size = rests_on(conclusion).len();
                if size > best {
                    best = size;
                    target = Some(conclusion);
                }
            }
            target
        };
        let premise_dependents: Map<String, Value> = self
            .dependents
            .keys()
            .map(|&statement| {
                let (arguments, statements, _) = self.upward(statement);
                (
                    statement.to_owned(),
                    json!({"arguments": arguments, "statements": statements}),
                )
            })
            .collect();
        vec![
            ("statement_statuses", Value::Object(statuses)),
            (
                "stages",
                json!(
                    stages
                        .iter()
                        .map(
                            |(stage, statement)| json!({"stage": stage, "statement_id": statement})
                        )
                        .collect::<Vec<_>>()
                ),
            ),
            ("statement_stages", json!(statement_stages)),
            ("default_target", json!(default_target)),
            ("premise_dependents", Value::Object(premise_dependents)),
        ]
    }

    /// Python `next_steps_report`: navigation and ranking, with every closure
    /// decision taken from the report and the probe of the same fixpoint.
    fn next_steps(&self, report: &Value) -> Value {
        let by_id = |records: &[&'a Record]| {
            let mut sorted = records.to_vec();
            sorted.sort_by_key(|record| text(record, "id"));
            sorted
        };
        let statements = by_id(&self.records.statements);
        let arguments = by_id(&self.records.arguments);
        let results = by_id(&self.records.results);
        let relations = by_id(&self.records.relations);
        let statement_by_id: HashMap<&str, &Record> = statements
            .iter()
            .map(|statement| (text(statement, "id"), *statement))
            .collect();
        let argument_by_id: HashMap<&str, &Record> = arguments
            .iter()
            .map(|argument| (text(argument, "id"), *argument))
            .collect();
        let mut result_ids: HashMap<&str, Vec<&str>> = HashMap::new();
        for result in &results {
            result_ids
                .entry(text(result, "argument_id"))
                .or_default()
                .push(text(result, "id"));
        }
        let strings = |value: &Value| -> HashSet<String> {
            value
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .map(str::to_owned)
                .collect()
        };
        let established = strings(&report["established_statements"]);
        let refuted = strings(&report["refuted_statements"]);
        let routes = report["routes"]["routes"]
            .as_array()
            .cloned()
            .unwrap_or_default();
        let open_of = |route: &Value| -> Vec<String> {
            route["open_premise_statement_ids"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .map(str::to_owned)
                .collect()
        };
        let cheapest = routes.iter().find(|route| route["cheapest"] == true);
        let leaves: BTreeSet<String> = routes.iter().flat_map(open_of).collect();
        let mut alternatives: HashMap<&str, BTreeSet<&str>> = HashMap::new();
        for relation in &relations {
            if text(relation, "predicate") == "alternative_to" {
                alternatives
                    .entry(text(relation, "object_id"))
                    .or_default()
                    .insert(text(relation, "subject_id"));
            }
        }
        let mut refutations: HashMap<String, Vec<Value>> = HashMap::new();
        for refutation in report["refutations"].as_array().into_iter().flatten() {
            refutations
                .entry(
                    refutation["statement_id"]
                        .as_str()
                        .unwrap_or_default()
                        .to_owned(),
                )
                .or_default()
                .push(refutation.clone());
        }
        let transcription_results = &report["transcription_results"];
        let statement = |sid: &str| -> Value {
            let record = statement_by_id.get(sid);
            let field = |name: &str| record.and_then(|record| record.get(name)).cloned();
            json!({
                "statement_id": sid,
                "paraphrase": field("paraphrase").unwrap_or(json!(sid)),
                "established": established.contains(sid),
                "status": report["statement_statuses"].get(sid).cloned().unwrap_or(json!("open")),
                "depth": report["statement_depths"].get(sid).cloned().unwrap_or(Value::Null),
                "lean_declaration": field("lean_declaration").unwrap_or(Value::Null),
                "definition_ids": field("definition_ids").unwrap_or(json!([])),
            })
        };
        let derivation = |argument: &Record| -> Value {
            let id = text(argument, "id");
            let ids = result_ids.get(id).cloned().unwrap_or_default();
            json!({
                "argument_id": id,
                "meaning": argument.get("meaning").cloned().unwrap_or(json!("")),
                "conclusion_statement_id": argument.get("conclusion_statement_id").cloned().unwrap_or(Value::Null),
                "premise_statement_ids": argument.get("premise_statement_ids").cloned().unwrap_or(Value::Null),
                "missing_statement_ids": list(argument, "premise_statement_ids").into_iter()
                    .filter(|sid| !established.contains(*sid)).collect::<Vec<_>>(),
                "result_ids": ids,
                "verified": !ids.is_empty(),
                "transcription": !ids.is_empty() && ids.iter().all(|rid| transcription_results.get(*rid).is_some()),
            })
        };
        let merge = |base: Value, extra: Value| -> Value {
            let mut object = base.as_object().cloned().unwrap_or_default();
            for (key, value) in extra.as_object().into_iter().flatten() {
                object.insert(key.clone(), value.clone());
            }
            Value::Object(object)
        };
        let rival = |sid: &str| -> Value {
            merge(
                statement(sid),
                json!({
                    "refuted": refuted.contains(sid),
                    "refutations": refutations.get(sid).cloned().unwrap_or_default(),
                    "consequences": arguments.iter()
                        .filter(|argument| list(argument, "premise_statement_ids").contains(&sid))
                        .map(|argument| derivation(argument)).collect::<Vec<_>>(),
                }),
            )
        };
        let rivals_of = |sid: &str| -> Vec<Value> {
            alternatives
                .get(sid)
                .into_iter()
                .flatten()
                .map(|rid| rival(rid))
                .collect()
        };

        // Every ID a route leaf can be, with the corpus lifetime the probe needs.
        let mut known: HashSet<&'a str> = self.statement_by_id.keys().copied().collect();
        for argument in &self.arguments {
            known.extend(Self::premises(argument));
            known.insert(text(argument, "conclusion_statement_id"));
        }
        let mut leaf_rows: Vec<Value> = Vec::new();
        for sid in &leaves {
            let hypothetical = known
                .get(sid.as_str())
                .map(|sid| self.probe(sid))
                .unwrap_or_default();
            let impacts: Vec<Value> = routes
                .iter()
                .filter(|route| route["verified"] == true)
                .filter_map(|route| {
                    let argument_id = route["argument_id"].as_str().unwrap_or_default();
                    let before = route["cost"].as_i64().unwrap_or(0);
                    let after = hypothetical.get(argument_id).copied().unwrap_or(0) as i64;
                    (before != after).then(|| {
                        json!({"argument_id": argument_id, "before": before, "after": after, "drop": before - after})
                    })
                })
                .collect();
            let recorded_rivals = rivals_of(sid);
            let derivations: Vec<Value> = arguments
                .iter()
                .filter(|argument| text(argument, "conclusion_statement_id") == sid)
                .map(|argument| derivation(argument))
                .collect();
            let route_depths: Map<String, Value> = routes
                .iter()
                .filter(|route| open_of(route).contains(sid))
                .map(|route| {
                    (
                        route["argument_id"].as_str().unwrap_or_default().to_owned(),
                        route["open_premise_depths"][sid].clone(),
                    )
                })
                .collect();
            let marking = report["floor"]
                .as_array()
                .into_iter()
                .flatten()
                .find(|entry| entry["statement_id"] == sid.as_str())
                .cloned()
                .unwrap_or(Value::Null);
            let improved = impacts
                .iter()
                .filter(|impact| impact["drop"].as_i64().unwrap_or(0) > 0)
                .count();
            let total: i64 = impacts
                .iter()
                .map(|impact| impact["drop"].as_i64().unwrap_or(0))
                .sum();
            let undefeated: Vec<Value> = recorded_rivals
                .iter()
                .filter(|rival| rival["refuted"] != true)
                .map(|rival| rival["statement_id"].clone())
                .collect();
            leaf_rows.push(merge(
                statement(sid),
                json!({
                    "route_depths": route_depths,
                    "on_cheapest_route": cheapest.is_some_and(|route| open_of(route).contains(sid)),
                    "rivals": recorded_rivals,
                    "derivations": derivations,
                    "floor": {"owner_decision_required": true, "marking": marking},
                    "definition_decisions": statement_by_id.get(sid.as_str())
                        .and_then(|record| record.get("settlement_actions")).cloned().unwrap_or(json!([])),
                    "impact": {"routes_improved": improved, "total_cost_drop": total, "routes": impacts},
                    "defense": {
                        "recorded_rival_count": recorded_rivals.len(),
                        "undefeated_statement_ids": undefeated,
                        "coverage": "recorded rivals only; not a certified exhaustive partition",
                    },
                }),
            ));
        }
        leaf_rows.sort_by(|a, b| {
            let key = |row: &Value| {
                (
                    std::cmp::Reverse(row["impact"]["routes_improved"].as_i64().unwrap_or(0)),
                    std::cmp::Reverse(row["impact"]["total_cost_drop"].as_i64().unwrap_or(0)),
                    row["statement_id"].as_str().unwrap_or_default().to_owned(),
                )
            };
            key(a).cmp(&key(b))
        });

        let failures = |route: &Value| -> Vec<(String, Value)> {
            open_of(route)
                .into_iter()
                .map(|sid| {
                    let mode = json!({
                        "statement_id": sid,
                        "failure": format!("not ({sid})"),
                        "recorded_rivals": rivals_of(&sid),
                        "negation_consequence_coverage": "unresolved: no certificate covering this failure mode registered",
                    });
                    (sid, mode)
                })
                .collect()
        };
        let verified_routes: Vec<&Value> = routes
            .iter()
            .filter(|route| route["verified"] == true)
            .collect();
        let mut pairs: Vec<Value> = Vec::new();
        for (index, left) in verified_routes.iter().enumerate() {
            for right in &verified_routes[index + 1..] {
                let left_open = open_of(left);
                let right_open = open_of(right);
                let right_set: HashSet<&String> = right_open.iter().collect();
                let overlap: BTreeSet<&String> = left_open
                    .iter()
                    .filter(|sid| right_set.contains(sid))
                    .collect();
                pairs.push(json!({
                    "left_argument_id": left["argument_id"], "right_argument_id": right["argument_id"],
                    "shared_statement_ids": overlap, "overlap_count": overlap.len(),
                    "left_failure_statement_ids": left["open_premise_statement_ids"],
                    "right_failure_statement_ids": right["open_premise_statement_ids"],
                    "certified": false,
                    "remaining": [
                        "Cover every failure mode of each route by a consequence theorem.",
                        "Establish incompatibility of the two consequences, with all its premises settled.",
                        "Compose both route implications with the joint-failure certificate.",
                    ],
                }));
            }
        }
        pairs.sort_by(|a, b| {
            let key = |pair: &Value| {
                (
                    pair["overlap_count"].as_u64().unwrap_or(0),
                    pair["left_argument_id"]
                        .as_str()
                        .unwrap_or_default()
                        .to_owned(),
                    pair["right_argument_id"]
                        .as_str()
                        .unwrap_or_default()
                        .to_owned(),
                )
            };
            key(a).cmp(&key(b))
        });
        let shared: BTreeSet<String> = if verified_routes.len() > 1 {
            let mut sets = verified_routes
                .iter()
                .map(|route| open_of(route).into_iter().collect::<BTreeSet<_>>());
            let first = sets.next().unwrap_or_default();
            sets.fold(first, |acc, set| acc.intersection(&set).cloned().collect())
        } else {
            BTreeSet::new()
        };
        let joint_summary = json!({
            "verified_route_count": verified_routes.len(),
            "pair_count": pairs.len(),
            "minimum_pair_overlap": pairs.first().map(|pair| pair["overlap_count"].clone()),
            "shared_by_all_reported_routes": shared,
            "scope": "Intersection of the reported verified root bundles only; not an exhaustive set of possible routes or a proof of necessary premises.",
        });

        let mut partitions = Vec::new();
        for result in &results {
            let Some(annotation) = result.get("case_split").filter(|v| truthy(Some(v))) else {
                continue;
            };
            let Some(argument) = argument_by_id.get(text(result, "argument_id")) else {
                continue;
            };
            let cells: Vec<Value> = annotation["cases"]
                .as_array()
                .into_iter()
                .flatten()
                .map(|cell| {
                    let case_sid = cell
                        .get("statement_id")
                        .and_then(Value::as_str)
                        .filter(|sid| !sid.is_empty());
                    merge(
                        cell.clone(),
                        json!({
                            "refuted": case_sid.is_some_and(|sid| refuted.contains(sid)),
                            "refutations": case_sid.map(|sid| refutations.get(sid).cloned().unwrap_or_default()).unwrap_or_default(),
                            "refutation_scope": if case_sid.is_some() {
                                "counted refutations of the registered case statement"
                            } else {
                                "no independent case statement; no counted refutation registered"
                            },
                        }),
                    )
                })
                .collect();
            let target = annotation["target_statement_id"].clone();
            partitions.push(json!({
                "result_id": text(result, "id"),
                "theorem": result.get("theorem").cloned().unwrap_or(Value::Null),
                "target_statement_id": target,
                "target_established": target.as_str().is_some_and(|sid| established.contains(sid)),
                "coverage_statement_id": argument.get("conclusion_statement_id").cloned().unwrap_or(Value::Null),
                "missing_background_statement_ids": list(argument, "premise_statement_ids").into_iter()
                    .filter(|sid| !established.contains(*sid)).collect::<Vec<_>>(),
                "cases": cells,
                "survival_result_id": annotation.get("survival_result_id").cloned().unwrap_or(Value::Null),
                "note": annotation.get("note").cloned().unwrap_or(json!("")),
            }));
        }
        let reaching_root = strings(&report["reaching_root_statements"]);
        let graph_arguments: Vec<&Record> = arguments
            .iter()
            .copied()
            .filter(|argument| reaching_root.contains(text(argument, "conclusion_statement_id")))
            .collect();
        let mut graph_ids: BTreeSet<String> = reaching_root.iter().cloned().collect();
        graph_ids.extend(
            graph_arguments
                .iter()
                .flat_map(|argument| list(argument, "premise_statement_ids"))
                .map(str::to_owned),
        );
        let floor: Vec<Value> = report["floor"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|entry| {
                let sid = entry["statement_id"].as_str().unwrap_or_default();
                let mut row = merge(entry.clone(), statement(sid));
                row["rivals"] = json!(rivals_of(sid));
                row["dependents"] = report["premise_dependents"]
                    .get(sid)
                    .cloned()
                    .unwrap_or(json!({"arguments": [], "statements": []}));
                row
            })
            .collect();
        let owner_decisions: Vec<Value> = leaf_rows
            .iter()
            .filter(|leaf| truthy(Some(&leaf["definition_decisions"])))
            .map(|leaf| {
                json!({
                    "statement_id": leaf["statement_id"], "paraphrase": leaf["paraphrase"],
                    "impact": leaf["impact"], "actions": leaf["definition_decisions"],
                })
            })
            .collect();
        let mut failure_modes = Map::new();
        for route in &routes {
            for (sid, mode) in failures(route) {
                failure_modes.insert(sid, mode);
            }
        }
        let root = report["root"].as_str().filter(|root| !root.is_empty());
        json!({
            "root": root.map(statement),
            "root_known": report["root_known"],
            "settlement_rules": {
                "floor": "Accept an explicit starting point. Each new floor item requires an owner decision; a proposed item settles nothing.",
                "derive": "Use a verified argument and establish every premise it needs. A conditional proof alone does not settle its conclusion.",
                "defend": "Refute every recorded rival using verified arguments whose premises are all established. An unrecorded rival may still matter philosophically.",
            },
            "impact_scope": "Counterfactual: establish this leaf alone, propagate the frontier's existing rules, and recompute all verified route costs. No actual approval, proof, or settlement is added.",
            "routes": routes,
            "cheapest_argument_id": report["routes"]["cheapest_argument_id"],
            "leaves": leaf_rows,
            "joint_settlements": pairs,
            "joint_settlement_summary": joint_summary,
            "partitions": partitions,
            "joint_settlement_schema_result_ids": results.iter()
                .filter(|result| result.get("joint_settlement_schema") == Some(&Value::Bool(true)))
                .map(|result| text(result, "id")).collect::<Vec<_>>(),
            "failure_modes": failure_modes,
            "floor_register": floor,
            "owner_decisions": owner_decisions,
            "dag": {
                "statements": graph_ids.iter().map(|sid| statement(sid)).collect::<Vec<_>>(),
                "arguments": graph_arguments.iter().map(|argument| derivation(argument)).collect::<Vec<_>>(),
            },
        })
    }
}

/// Python `item_depth`: an open premise's depth under the current rule.
fn item_depth(item: &Value) -> String {
    let depth = item["depth"].as_str().unwrap_or_default();
    if depth == LEGACY_SOURCED || depth == STATED {
        let ids = |field: &str| -> HashSet<&str> {
            item[field]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .collect()
        };
        let unverifiable: HashSet<&str> = ids("bibliographic_claims")
            .union(&ids("unavailable_claims"))
            .copied()
            .collect();
        let pinned = ids("stating_claims")
            .iter()
            .any(|claim| !unverifiable.contains(claim));
        return if pinned { STATED } else { SUPPORTED }.to_owned();
    }
    depth.to_owned()
}

/// Python `depth_counts`.
fn depth_counts(items: &[Value]) -> Value {
    let depths: Vec<String> = items.iter().map(item_depth).collect();
    let counts: Map<String, Value> = DEPTHS
        .iter()
        .map(|depth| {
            (
                (*depth).to_owned(),
                json!(depths.iter().filter(|d| d == depth).count()),
            )
        })
        .collect();
    Value::Object(counts)
}

/// Python `restrict_to_root` (`frontier --reaching-root`).
pub fn restrict_to_root(report: &mut Value) {
    let items: Vec<Value> = report["items"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|item| !item["path_to_root"].is_null())
        .cloned()
        .collect();
    let on_path: HashSet<String> = items
        .iter()
        .flat_map(|item| {
            item["transitive_dependent_arguments"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .map(str::to_owned)
        })
        .collect();
    report["open_premise_count"] = json!(items.len());
    report["depth_counts"] = depth_counts(&items);
    report["items"] = json!(items);
    let keep = |field: &str, keep: &dyn Fn(&Value) -> bool| -> Value {
        json!(
            report[field]
                .as_array()
                .into_iter()
                .flatten()
                .filter(|entry| keep(entry))
                .cloned()
                .collect::<Vec<_>>()
        )
    };
    let flags = keep("transcription_flags", &|flag| {
        flag["argument_id"]
            .as_str()
            .is_some_and(|id| on_path.contains(id))
    });
    let closures = keep("closed_via_transcription", &|closure| {
        !closure["path_to_root"].is_null()
    });
    report["transcription_flags"] = flags;
    report["closed_via_transcription"] = closures;
}

fn s(value: &Value) -> &str {
    value.as_str().unwrap_or_default()
}

fn strs(value: &Value) -> Vec<&str> {
    value
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .collect()
}

fn count(value: &Value, key: &str) -> i64 {
    value.get(key).and_then(Value::as_i64).unwrap_or(0)
}

/// Python `format_depth_counts`.
fn format_depth_counts(counts: &Value) -> String {
    let mut text = format!(
        "{} bare, {} supported, {} stated",
        count(counts, BARE),
        count(counts, SUPPORTED),
        count(counts, STATED)
    );
    let proved = count(counts, PROVED_UNESTABLISHED);
    if proved != 0 {
        text += &format!(", {proved} proved-unestablished");
    }
    text
}

fn format_floor_bases(routes: &Value) -> Vec<String> {
    let rendered: Vec<String> = routes["floor_bases"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|entry| format!("{} ({})", s(&entry["statement_id"]), s(&entry["basis"])))
        .collect();
    let rendered = if rendered.is_empty() {
        "none".to_owned()
    } else {
        rendered.join(", ")
    };
    vec![
        String::new(),
        format!("closed relative to floor bases: {rendered}"),
    ]
}

/// Python `format_frontier`.
pub fn format_frontier(report: &Value) -> String {
    let mut lines = Vec::new();
    let root = s(&report["root"]);
    let root_note = if report["root_known"] == true {
        root.to_owned()
    } else {
        format!("{root} (unknown statement)")
    };
    lines.push(format!(
        "frontier: {} open premises: {}; root {root_note}",
        report["open_premise_count"],
        format_depth_counts(&report["depth_counts"])
    ));
    let recorded = report["alternatives_recorded"] == true;
    if !recorded {
        lines.push("alternatives: no alternatives recorded".into());
    }
    for item in report["items"].as_array().into_iter().flatten() {
        lines.push(String::new());
        lines.push(format!(
            "{} [{}]",
            s(&item["statement_id"]),
            s(&item["depth"])
        ));
        if truthy(Some(&item["paraphrase"])) {
            lines.push(format!("  {}", s(&item["paraphrase"])));
        }
        if item["transcription_only"] == true {
            lines.push(
                "  open although proved: every verifying result is a transcription (invariant 16)"
                    .into(),
            );
        }
        let dependent = strs(&item["dependent_arguments"]);
        lines.push(format!(
            "  dependent arguments: {} ({})",
            dependent.len(),
            dependent.join(", ")
        ));
        lines.push(format!(
            "  transitive dependents: {} arguments, {} statements",
            strs(&item["transitive_dependent_arguments"]).len(),
            strs(&item["transitive_dependent_statements"]).len()
        ));
        if item["path_to_root"].is_null() {
            lines.push("  path to root: not reached".into());
        } else {
            lines.push(format!(
                "  path to root: {}",
                strs(&item["path_to_root"]).join(" -> ")
            ));
        }
        let alternatives = item["alternatives"].as_array().cloned().unwrap_or_default();
        if !alternatives.is_empty() {
            let rendered: Vec<String> = alternatives
                .iter()
                .map(|alternative| {
                    format!(
                        "{} ({})",
                        s(&alternative["statement_id"]),
                        if alternative["refuted"] == true {
                            "refuted"
                        } else {
                            "open"
                        }
                    )
                })
                .collect();
            lines.push(format!("  alternatives: {}", rendered.join(", ")));
        } else if recorded {
            lines.push("  alternatives: none recorded".into());
        }
        let objections = strs(&item["objections"]);
        lines.push(format!(
            "  objections: {}",
            if objections.is_empty() {
                "none recorded".to_owned()
            } else {
                objections.join(", ")
            }
        ));
        for (field, label) in [
            ("stating_claims", "  stating source claims: "),
            ("supporting_claims", "  supporting source claims: "),
            (
                "bibliographic_claims",
                "  bibliographic witness, not byte-verified: ",
            ),
            (
                "unavailable_claims",
                "  permanently unavailable witness, not byte-verified: ",
            ),
            ("transcription_premise_of", "  transcription premise of: "),
        ] {
            let ids = strs(&item[field]);
            if !ids.is_empty() {
                lines.push(format!("{label}{}", ids.join(", ")));
            }
        }
        if truthy(item.get("floor_unmet")) {
            let unmet = &item["floor_unmet"];
            lines.push(format!(
                "  self_evident basis {} not met: {}",
                s(&unmet["basis"]),
                strs(&unmet["reasons"]).join("; ")
            ));
        }
    }
    let floor = report["floor"].as_array().cloned().unwrap_or_default();
    lines.push(String::new());
    lines.push(format!(
        "floor: {} of {} self_evident markings meet their basis (closure is relative to these bases)",
        floor.iter().filter(|entry| entry["met"] == true).count(),
        floor.len()
    ));
    for entry in &floor {
        let mut status = if entry["met"] == true {
            "met".to_owned()
        } else {
            format!("not met: {}", strs(&entry["reasons"]).join("; "))
        };
        if truthy(entry.get("owner_approval")) && entry["met"] == true {
            status = format!(
                "met by owner approval {}",
                py_str(entry["owner_approval"].get("decision"))
            );
            let criterion = strs(&entry["criterion_reasons"]);
            if !criterion.is_empty() {
                status += &format!(" (criterion not met: {})", criterion.join("; "));
            }
        }
        lines.push(format!(
            "  {} [{}]: {status}",
            s(&entry["statement_id"]),
            s(&entry["basis"])
        ));
    }
    lines.extend(format_floor_bases(&report["routes"]));
    let uncounted: Vec<&Value> = report["refutations"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|refutation| refutation["counted"] != true)
        .collect();
    if !uncounted.is_empty() {
        lines.push(String::new());
        lines.push(format!(
            "refutations not counted for rule (c): {}",
            uncounted.len()
        ));
        for refutation in uncounted {
            let reason = if refutation["verified"] == true {
                format!(
                    "unestablished premises {}",
                    strs(&refutation["unestablished_premise_statement_ids"]).join(", ")
                )
            } else {
                "no verified result".to_owned()
            };
            lines.push(format!(
                "  {} ({} refutes {}): {reason}",
                s(&refutation["relation_id"]),
                s(&refutation["argument_id"]),
                s(&refutation["statement_id"])
            ));
        }
    }
    let closures = report["closed_via_transcription"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    lines.push(String::new());
    lines.push(format!(
        "closed via transcription from closed premises: {} statements (a transcription result whose premises are all closed)",
        closures.len()
    ));
    for closure in &closures {
        let premises = strs(&closure["premise_statement_ids"]);
        lines.push(format!(
            "  {}: closed via transcription {} from closed premises ({})",
            s(&closure["statement_id"]),
            s(&closure["result_id"]),
            if premises.is_empty() {
                "none".to_owned()
            } else {
                premises.join(", ")
            }
        ));
    }
    let strength = report["strength_order"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    if !strength.is_empty() {
        lines.push(String::new());
        lines.push(format!(
            "strength order: {} strong/weak pairs (established strong establishes weak; refuted weak refutes strong; never the reverse)",
            strength.len()
        ));
        for entry in &strength {
            let mut notes = Vec::new();
            if entry["weak_established_via_strength"] == true {
                notes.push("weak established via strength");
            }
            if entry["strong_refuted_via_strength"] == true {
                notes.push("strong refuted via strength");
            }
            let suffix = if notes.is_empty() {
                String::new()
            } else {
                format!(" [{}]", notes.join("; "))
            };
            lines.push(format!(
                "  {} => {} ({}){suffix}",
                s(&entry["strong_statement_id"]),
                s(&entry["weak_statement_id"]),
                s(&entry["result_id"])
            ));
        }
    }
    let flags = report["transcription_flags"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    lines.push(String::new());
    lines.push(format!(
        "transcription heuristics: {} results flagged (single application, assembly of hypotheses, opaque Prop atoms, goal as premise consequent, or at most {SHORT_PROOF_STEPS} proof steps)",
        flags.len()
    ));
    for flag in &flags {
        let mut notes = vec![format!("{} steps", flag["proof_steps"])];
        let kind = &report["transcription_results"][s(&flag["result_id"])];
        if kind["declared"] == true {
            notes.push(format!(
                "declared transcription: {}",
                py_str(Some(&kind["kind"]))
            ));
        }
        if truthy(Some(&flag["single_application_of"])) {
            notes.push(format!(
                "single application of {}",
                s(&flag["single_application_of"])
            ));
        }
        if truthy(Some(&flag["assembly_of"])) {
            notes.push(format!(
                "assembly of {}",
                strs(&flag["assembly_of"]).join(", ")
            ));
        }
        if flag["opaque_atoms"] == true {
            notes.push("opaque Prop atoms".into());
        }
        for premise in flag["goal_consequent_premises"]
            .as_array()
            .into_iter()
            .flatten()
        {
            let ids = strs(&premise["statement_ids"]);
            let ids = if ids.is_empty() {
                "no statement match".to_owned()
            } else {
                ids.join(", ")
            };
            notes.push(format!(
                "goal is consequent of {} ({ids})",
                s(&premise["hypothesis"])
            ));
        }
        lines.push(format!("  {}: {}", s(&flag["result_id"]), notes.join("; ")));
    }
    lines.join("\n")
}

/// Python `format_routes`.
pub fn format_routes(routes: &Value) -> String {
    let entries = routes["routes"].as_array().cloned().unwrap_or_default();
    let cheapest = routes["cheapest_argument_id"]
        .as_str()
        .filter(|id| !id.is_empty())
        .unwrap_or("none (no verified route)");
    let mut lines = vec![format!(
        "routes to {}: {} arguments; cheapest {cheapest}",
        s(&routes["root"]),
        entries.len()
    )];
    if entries.is_empty() {
        return lines.join("\n");
    }
    lines.push("cost  bare  supported  stated  proved  premises  argument".into());
    for entry in &entries {
        let marks: Vec<&str> = [
            ("cheapest", entry["cheapest"] == true),
            ("designated", entry["designated"] == true),
            ("unverified", entry["verified"] != true),
            ("transcription", entry["transcription"] == true),
        ]
        .into_iter()
        .filter(|(_, present)| *present)
        .map(|(mark, _)| mark)
        .collect();
        let suffix = if marks.is_empty() {
            String::new()
        } else {
            format!("  [{}]", marks.join(", "))
        };
        let depths = &entry["depth_counts"];
        lines.push(format!(
            "{:>4}  {:>4}  {:>9}  {:>6}  {:>6}  {:>8}  {}{suffix}",
            count(entry, "cost"),
            count(depths, BARE),
            count(depths, SUPPORTED),
            count(depths, STATED),
            count(depths, PROVED_UNESTABLISHED),
            count(entry, "premise_count"),
            s(&entry["argument_id"])
        ));
    }
    for entry in &entries {
        if entry["cheapest"] != true {
            continue;
        }
        lines.push(String::new());
        lines.push(format!(
            "open premises of the cheapest route {} ({}):",
            s(&entry["argument_id"]),
            entry["cost"]
        ));
        let unestablished = strs(&entry["proved_unestablished_statement_ids"]);
        for statement in strs(&entry["open_premise_statement_ids"]) {
            let note = if unestablished.contains(&statement) {
                " (proved, rests on open premises)".to_owned()
            } else {
                entry["open_premise_depths"]
                    .get(statement)
                    .map(|depth| format!(" [{}]", s(depth)))
                    .unwrap_or_default()
            };
            lines.push(format!("  {statement}{note}"));
        }
    }
    lines.extend(format_floor_bases(routes));
    lines.join("\n")
}

/// Python `frontier_status`.
fn frontier_status(report: &Value, statement: &str) -> String {
    for item in report["items"].as_array().into_iter().flatten() {
        if item["statement_id"] == statement {
            return item_depth(item);
        }
    }
    let listed = |field: &str| match &report[field] {
        Value::Object(map) => map.contains_key(statement),
        Value::Array(items) => items.iter().any(|item| item == statement),
        _ => false,
    };
    if listed("closed_statements") || listed("established_statements") {
        CLOSED.to_owned()
    } else {
        ABSENT.to_owned()
    }
}

/// Python `frontier_delta` (#948) between two reaching-root reports.
pub fn frontier_delta(base: &Value, head: &Value) -> Value {
    let no_routes = json!({"cheapest_argument_id": null, "routes": []});
    let with_routes = |report: &Value| {
        let mut report = report.clone();
        if !truthy(report.get("routes")) {
            report["routes"] = no_routes.clone();
        }
        report
    };
    let (base, head) = (with_routes(base), with_routes(head));
    let open_ids: BTreeSet<&str> = [&base, &head]
        .iter()
        .flat_map(|report| report["items"].as_array().into_iter().flatten())
        .filter_map(|item| item["statement_id"].as_str())
        .collect();
    let mut added: BTreeMap<String, Vec<&str>> = BTreeMap::new();
    let mut removed: BTreeMap<String, Vec<&str>> = BTreeMap::new();
    let mut moved: BTreeMap<String, Vec<&str>> = BTreeMap::new();
    for &statement in &open_ids {
        let (before, after) = (
            frontier_status(&base, statement),
            frontier_status(&head, statement),
        );
        if before == after {
            continue;
        }
        if before == ABSENT {
            added.entry(after).or_default().push(statement);
        } else if after == ABSENT {
            removed.entry(before).or_default().push(statement);
        } else {
            moved
                .entry(format!("{before} -> {after}"))
                .or_default()
                .push(statement);
        }
    }
    let route_map = |report: &Value| -> BTreeMap<String, Value> {
        report["routes"]["routes"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|entry| (s(&entry["argument_id"]).to_owned(), entry.clone()))
            .collect()
    };
    let (base_routes, head_routes) = (route_map(&base), route_map(&head));
    let route_depth_counts = |report: &Value, route: Option<&Value>| -> Value {
        let Some(route) = route else {
            return Value::Null;
        };
        let mut depths: HashMap<String, String> = report["items"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|item| (s(&item["statement_id"]).to_owned(), item_depth(item)))
            .collect();
        for (statement, depth) in report
            .get("all_item_depths")
            .and_then(Value::as_object)
            .into_iter()
            .flatten()
        {
            depths.insert(statement.clone(), s(depth).to_owned());
        }
        let mut counts: Map<String, Value> = DEPTHS
            .iter()
            .chain([&PROVED_UNESTABLISHED])
            .map(|depth| ((*depth).to_owned(), json!(0)))
            .collect();
        let mut bump = |depth: &str| {
            let entry = counts.entry(depth.to_owned()).or_insert(json!(0));
            *entry = json!(entry.as_i64().unwrap_or(0) + 1);
        };
        if let Some(cached) = route.get("open_premise_depths").and_then(Value::as_object) {
            for (statement, depth) in cached {
                let mut depth = s(depth).to_owned();
                if depth != PROVED_UNESTABLISHED
                    && let Some(normalized) = depths.get(statement)
                {
                    depth = normalized.clone();
                }
                bump(&depth);
            }
            return Value::Object(counts);
        }
        if let Some(cached) = route.get("depth_counts") {
            return cached.clone();
        }
        let unestablished = strs(&route["proved_unestablished_statement_ids"]);
        for statement in strs(&route["open_premise_statement_ids"]) {
            match depths.get(statement) {
                Some(depth) if !unestablished.contains(&statement) => bump(depth),
                _ => bump(PROVED_UNESTABLISHED),
            }
        }
        Value::Object(counts)
    };
    let mut route_changes = Vec::new();
    let all_routes: BTreeSet<&String> = base_routes.keys().chain(head_routes.keys()).collect();
    for argument_id in all_routes {
        let (before, after) = (base_routes.get(argument_id), head_routes.get(argument_id));
        let cost = |route: Option<&Value>| {
            route
                .map(|route| route["cost"].clone())
                .unwrap_or(Value::Null)
        };
        let verified = |route: Option<&Value>| route.is_some_and(|route| route["verified"] == true);
        let open = |route: Option<&Value>| -> BTreeSet<String> {
            route
                .map(|route| {
                    strs(&route["open_premise_statement_ids"])
                        .into_iter()
                        .map(str::to_owned)
                        .collect()
                })
                .unwrap_or_default()
        };
        let (before_open, after_open) = (open(before), open(after));
        let before_depths = route_depth_counts(&base, before);
        let after_depths = route_depth_counts(&head, after);
        if (cost(before), verified(before), &before_open, &before_depths)
            == (cost(after), verified(after), &after_open, &after_depths)
        {
            continue;
        }
        route_changes.push(json!({
            "argument_id": argument_id,
            "base_cost": cost(before),
            "head_cost": cost(after),
            "base_verified": verified(before),
            "head_verified": verified(after),
            "base_depth_counts": before_depths,
            "head_depth_counts": after_depths,
            "opened_premise_statement_ids": after_open.difference(&before_open).collect::<Vec<_>>(),
            "closed_premise_statement_ids": before_open.difference(&after_open).collect::<Vec<_>>(),
        }));
    }
    let cheapest = |report: &Value| {
        let argument_id = report["routes"]["cheapest_argument_id"].clone();
        let entry = report["routes"]["routes"]
            .as_array()
            .into_iter()
            .flatten()
            .find(|entry| entry["argument_id"] == argument_id);
        json!({"argument_id": argument_id, "cost": entry.map(|entry| entry["cost"].clone())})
    };
    let counts = |report: &Value| {
        let items = report["items"].as_array().cloned().unwrap_or_default();
        let mut counts = depth_counts(&items);
        counts["open"] = json!(items.len());
        counts
    };
    let bare_added: Vec<&str> = open_ids
        .iter()
        .copied()
        .filter(|statement| {
            frontier_status(&head, statement) == BARE && frontier_status(&base, statement) != BARE
        })
        .collect();
    let (base_cheapest, head_cheapest) = (cheapest(&base), cheapest(&head));
    let changed = !added.is_empty()
        || !removed.is_empty()
        || !moved.is_empty()
        || !route_changes.is_empty()
        || base_cheapest != head_cheapest;
    json!({
        "root": head["root"],
        "base_counts": counts(&base),
        "head_counts": counts(&head),
        "added": added,
        "removed": removed,
        "moved": moved,
        "bare_added": bare_added,
        "base_cheapest_route": base_cheapest,
        "head_cheapest_route": head_cheapest,
        "route_changes": route_changes,
        "changed": changed,
    })
}

/// Python `format_frontier_delta`.
pub fn format_frontier_delta(delta: &Value) -> String {
    let counts = |c: &Value| format!("{} ({})", c["open"], format_depth_counts(c));
    let route = |r: &Value| {
        if truthy(Some(&r["argument_id"])) {
            format!(
                "{} (cost {})",
                s(&r["argument_id"]),
                py_str(Some(&r["cost"]))
            )
        } else {
            "none".to_owned()
        }
    };
    let mut lines = vec![
        format!(
            "premise delta for {}: {} -> {}",
            s(&delta["root"]),
            s(&delta["base"]),
            s(&delta["head"])
        ),
        format!(
            "open premises reaching the root: {} -> {}",
            counts(&delta["base_counts"]),
            counts(&delta["head_counts"])
        ),
        format!(
            "cheapest route: {} -> {}",
            route(&delta["base_cheapest_route"]),
            route(&delta["head_cheapest_route"])
        ),
    ];
    if delta["changed"] != true {
        lines.push("no change".into());
        return lines.join("\n");
    }
    let bare_added = strs(&delta["bare_added"]);
    if bare_added.is_empty() {
        lines.push("bare premises added: none".into());
    } else {
        lines.push(format!(
            "bare premises added: {} (listed for visibility; not a regression, owner decision 2026-11-07)",
            bare_added.len()
        ));
        lines.extend(bare_added.iter().map(|statement| format!("  {statement}")));
    }
    for label in ["added", "removed", "moved"] {
        for (status, statements) in delta[label].as_object().into_iter().flatten() {
            let statements = strs(statements);
            lines.push(format!("{label} ({status}): {}", statements.len()));
            lines.extend(statements.iter().map(|statement| format!("  {statement}")));
        }
    }
    let changes = delta["route_changes"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    if !changes.is_empty() {
        lines.push("route cost changes:".into());
    }
    let side = |cost: &Value, verified: bool, depths: &Value| {
        if cost.is_null() {
            return "absent".to_owned();
        }
        let split = if truthy(Some(depths)) {
            format!(" ({})", format_depth_counts(depths))
        } else {
            String::new()
        };
        format!(
            "{cost}{split}{}",
            if verified { "" } else { " (unverified)" }
        )
    };
    for change in &changes {
        lines.push(format!(
            "  {}: {} -> {}",
            s(&change["argument_id"]),
            side(
                &change["base_cost"],
                change["base_verified"] == true,
                &change["base_depth_counts"]
            ),
            side(
                &change["head_cost"],
                change["head_verified"] == true,
                &change["head_depth_counts"]
            )
        ));
        if change["base_cost"].is_null() || change["head_cost"].is_null() {
            continue;
        }
        let opened = strs(&change["opened_premise_statement_ids"]);
        if !opened.is_empty() {
            lines.push(format!("    + {}", opened.join(", ")));
        }
        let closed = strs(&change["closed_premise_statement_ids"]);
        if !closed.is_empty() {
            lines.push(format!("    - {}", closed.join(", ")));
        }
    }
    lines.join("\n")
}

/// The full frontier report of one checkout (Python `current_frontier`
/// without the `validate()` it runs first).
pub fn current_frontier(
    checkout: &Path,
    corpus: &crate::Corpus,
    root: &str,
    reaching_root: bool,
    next_steps: bool,
) -> Value {
    let records = Records::from_corpus(corpus);
    let flags = transcription_flags(checkout, &records);
    let frontier = Frontier::new(root, &records, &flags);
    let mut report = frontier.report(next_steps);
    if reaching_root {
        restrict_to_root(&mut report);
    }
    report
}

fn git(checkout: &Path, args: &[&str]) -> Result<Vec<u8>, String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(checkout)
        .args(args)
        .output()
        .map_err(|error| format!("cannot run git: {error}"))?;
    if output.status.success() {
        Ok(output.stdout)
    } else {
        Err(String::from_utf8_lossy(&output.stderr).trim().to_owned())
    }
}

/// A `git archive` extract of one revision, removed on drop.
/// Python `uses_uuid_identity`: whether the corpus at `tree` has uuid ids
/// (judged by its first statement record).
fn uses_uuid_identity(tree: &Path) -> bool {
    let directory = tree.join("corpus").join("statements");
    let mut paths: Vec<PathBuf> = std::fs::read_dir(&directory)
        .into_iter()
        .flatten()
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|ext| ext == "json"))
        .collect();
    paths.sort();
    let Some(first) = paths.first() else {
        return true;
    };
    std::fs::read_to_string(first)
        .ok()
        .and_then(|text| serde_json::from_str::<Value>(&text).ok())
        .and_then(|record| record["id"].as_str().map(crate::identity::is_uuid))
        .unwrap_or(false)
}

/// Python `legacy_report_to_uuid`: every string of a pre-migration report
/// that is a legacy id of the tree's records becomes that record's uuid.
/// Only arguments and results share legacy ids; a key naming results picks
/// the result, any other key the argument.
fn legacy_report_to_uuid(report: Value, tree: &Path) -> Value {
    // legacy id -> [(kind, uuid)] in first-insertion order (`Migration.load`).
    let mut table: HashMap<String, Vec<(&'static str, String)>> = HashMap::new();
    for &(directory, kind) in crate::identity::KIND_DIRS {
        let mut paths: Vec<PathBuf> = std::fs::read_dir(tree.join("corpus").join(directory))
            .into_iter()
            .flatten()
            .filter_map(|entry| entry.ok().map(|entry| entry.path()))
            .filter(|path| path.extension().is_some_and(|ext| ext == "json"))
            .collect();
        paths.sort();
        for path in paths {
            let Ok(Value::Object(data)) = std::fs::read_to_string(&path)
                .map_err(|_| ())
                .and_then(|text| serde_json::from_str::<Value>(&text).map_err(|_| ()))
            else {
                continue;
            };
            let records: Vec<&Map<String, Value>> = if kind == "passage" {
                data.get("passages")
                    .and_then(Value::as_array)
                    .into_iter()
                    .flatten()
                    .filter_map(Value::as_object)
                    .collect()
            } else {
                vec![&data]
            };
            for record in records {
                let Some(id) = record.get("id").and_then(Value::as_str) else {
                    continue;
                };
                let uuid = crate::identity::is_uuid(id);
                let legacy = if uuid {
                    record.get("legacy_id").and_then(Value::as_str)
                } else {
                    Some(id)
                };
                let Some(legacy) = legacy.filter(|legacy| !legacy.is_empty()) else {
                    continue;
                };
                let uid = if uuid {
                    id.to_owned()
                } else {
                    crate::identity::legacy_uuid(kind, legacy)
                };
                let kinds = table.entry(legacy.to_owned()).or_default();
                match kinds.iter_mut().find(|(known, _)| *known == kind) {
                    Some(slot) => slot.1 = uid,
                    None => kinds.push((kind, uid)),
                }
            }
        }
    }
    fn convert(
        table: &HashMap<String, Vec<(&'static str, String)>>,
        value: &str,
        key: &str,
    ) -> String {
        let Some(kinds) = table.get(value).filter(|kinds| !kinds.is_empty()) else {
            return value.to_owned();
        };
        if kinds.len() == 1 {
            return kinds[0].1.clone();
        }
        let prefer = if key.contains("result") {
            ["result", "argument"]
        } else {
            ["argument", "result"]
        };
        prefer
            .iter()
            .find_map(|kind| kinds.iter().find(|(known, _)| known == kind))
            .unwrap_or(&kinds[0])
            .1
            .clone()
    }
    fn walk(table: &HashMap<String, Vec<(&'static str, String)>>, node: Value, key: &str) -> Value {
        match node {
            Value::Object(object) => Value::Object(
                object
                    .into_iter()
                    .map(|(k, v)| {
                        let value = walk(table, v, &k);
                        (convert(table, &k, key), value)
                    })
                    .collect(),
            ),
            Value::Array(items) => Value::Array(
                items
                    .into_iter()
                    .map(|item| walk(table, item, key))
                    .collect(),
            ),
            Value::String(text) => Value::String(convert(table, &text, key)),
            other => other,
        }
    }
    walk(&table, report, "")
}

struct Extract(PathBuf);

impl Drop for Extract {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn extract(checkout: &Path, revision: &str) -> Result<Extract, String> {
    let archive = git(checkout, &["archive", "--format=tar", revision])
        .map_err(|error| format!("cannot archive revision {revision}: {error}"))?;
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |elapsed| elapsed.as_nanos());
    let directory = std::env::temp_dir().join(format!(
        "truth-frontier-diff-{}-{nanos}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).map_err(|error| error.to_string())?;
    let extract = Extract(directory);
    let mut tar = Command::new("tar")
        .arg("-x")
        .arg("-C")
        .arg(&extract.0)
        .stdin(Stdio::piped())
        .spawn()
        .map_err(|error| format!("cannot run tar: {error}"))?;
    tar.stdin
        .take()
        .ok_or("tar has no stdin")?
        .write_all(&archive)
        .map_err(|error| error.to_string())?;
    let status = tar.wait().map_err(|error| error.to_string())?;
    if !status.success() {
        return Err(format!("cannot extract revision {revision}"));
    }
    Ok(extract)
}

/// Python `revision_frontier`: the reaching-root frontier at a Git revision,
/// on a `git archive` extract, with `all_item_depths` of the full report.
///
/// Python runs that revision's own `corpus.py`, so a change of the frontier
/// rules between base and head shows in the delta. The Rust engine computes
/// the current rules, so it is used only when the revision's
/// `scripts/corpus.py` is byte-identical to the checkout's (the rules this
/// port matches); otherwise that revision's Python runs, as in
/// `corpus.py frontier-diff`. The engine used is returned with the report.
pub fn revision_frontier(
    checkout: &Path,
    revision: &str,
    root: &str,
    legacy_root: &str,
) -> Result<(Value, &'static str), String> {
    let tree = extract(checkout, revision)?;
    // A revision from before the uuid migration knows only legacy ids: it is
    // asked for the root's legacy id and its report is mapped to uuids
    // (Python `revision_frontier_json`).
    let legacy = !uses_uuid_identity(&tree.0);
    let root = if legacy { legacy_root } else { root };
    let script = format!("{revision}:scripts/corpus.py");
    let same_rules = match (
        git(checkout, &["rev-parse", &script]),
        git(checkout, &["hash-object", "scripts/corpus.py"]),
    ) {
        (Ok(at_revision), Ok(current)) => at_revision == current,
        _ => false,
    };
    let (mut report, engine) = if same_rules {
        let corpus = crate::Corpus::load(&tree.0).map_err(|error| {
            format!(
                "frontier at {revision} failed: {}: {}",
                error.path, error.message
            )
        })?;
        (
            current_frontier(&tree.0, &corpus, root, false, false),
            "rust",
        )
    } else {
        let output = Command::new("python3")
            .arg(tree.0.join("scripts").join("corpus.py"))
            .args(["frontier", "--json", "--root", root])
            .current_dir(&tree.0)
            .output()
            .map_err(|error| format!("cannot run python3: {error}"))?;
        if !output.status.success() {
            return Err(format!(
                "frontier at {revision} failed: {}",
                String::from_utf8_lossy(&output.stderr).trim()
            ));
        }
        let report = serde_json::from_slice(&output.stdout)
            .map_err(|error| format!("frontier at {revision}: invalid JSON: {error}"))?;
        (report, "python")
    };
    if legacy {
        report = legacy_report_to_uuid(report, &tree.0);
    }
    let all_item_depths: Map<String, Value> = report["items"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|item| (s(&item["statement_id"]).to_owned(), json!(item_depth(item))))
        .collect();
    restrict_to_root(&mut report);
    report["all_item_depths"] = Value::Object(all_item_depths);
    Ok((report, engine))
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
        json!({"id": id, "premise_statement_ids": premises,
               "conclusion_statement_id": conclusion, "inference_ids": ["INF"]})
    }

    fn relation(id: &str, subject: &str, predicate: &str, object: &str) -> Value {
        json!({"id": id, "subject_kind": "statement", "subject_id": subject,
               "predicate": predicate, "object_kind": "statement", "object_id": object})
    }

    struct Fixture {
        statements: Vec<Record>,
        arguments: Vec<Record>,
        results: Vec<Record>,
        relations: Vec<Record>,
        claims: Vec<Record>,
    }

    impl Fixture {
        fn records(&self) -> Records<'_> {
            Records {
                statements: self.statements.iter().collect(),
                arguments: self.arguments.iter().collect(),
                results: self.results.iter().collect(),
                relations: self.relations.iter().collect(),
                claims: self.claims.iter().collect(),
                attempts: Vec::new(),
                definitions: Vec::new(),
                inferences: Vec::new(),
            }
        }
    }

    /// ROOT <- {A, B}; A <-> C proved from each other (a cyclic core); B
    /// proved from a floor premise F and a stated premise S; the declared
    /// transcription T closes nothing but carries closure from F.
    fn fixture() -> Fixture {
        let ids = ["ROOT", "A", "B", "C", "F", "S", "T", "NF"];
        let mut statements: Vec<Value> = ids.iter().map(|id| json!({"id": id})).collect();
        statements[4] = json!({"id": "F", "self_evident": {"basis": "retorsion",
            "denial_statement_id": "NF", "justification_ids": ["RES-NF"]}});
        Fixture {
            statements: records(statements),
            arguments: records(vec![
                argument("ARG-ROOT", &["A", "B"], "ROOT"),
                argument("ARG-A", &["C"], "A"),
                argument("ARG-C", &["A"], "C"),
                argument("ARG-B", &["F", "S"], "B"),
                argument("ARG-T", &["F"], "T"),
                argument("ARG-NF", &[], "NF-REFUTED"),
            ]),
            results: records(vec![
                json!({"id": "RES-ROOT", "argument_id": "ARG-ROOT"}),
                json!({"id": "RES-A", "argument_id": "ARG-A"}),
                json!({"id": "RES-C", "argument_id": "ARG-C"}),
                json!({"id": "RES-B", "argument_id": "ARG-B"}),
                json!({"id": "RES-T", "argument_id": "ARG-T", "transcription": "assembly"}),
                json!({"id": "RES-NF", "argument_id": "ARG-NF"}),
            ]),
            relations: records(vec![
                relation("REL-ALT", "NF", "alternative_to", "F"),
                relation("REL-REFUTES", "ARG-NF", "refutes", "NF"),
            ]),
            claims: records(vec![json!({"id": "CLAIM-S", "statement_id": "S"})]),
        }
    }

    #[test]
    fn closure_routes_and_walks_follow_python() {
        let fixture = fixture();
        let records = fixture.records();
        let frontier = Frontier::new("ROOT", &records, &[]);
        let report = frontier.report(false);
        // The retorsion is met: its refutation of the denial is premise-free.
        assert_eq!(report["floor"][0]["met"], true);
        assert_eq!(report["closed_statements"]["F"], "self_evident");
        assert_eq!(report["closed_statements"]["T"], "via_transcription");
        assert_eq!(report["closed_statements"]["B"], "proved");
        // The cyclic core {A, C} is seeded as single leaves and A keeps its
        // own (C's is no smaller); the stated premise S stays one leaf.
        let route = &report["routes"]["routes"][0];
        assert_eq!(route["open_premise_statement_ids"], json!(["A", "S"]));
        assert_eq!(route["cost"], 2);
        assert_eq!(route["open_premise_depths"]["S"], "stated");
        assert_eq!(report["routes"]["cheapest_argument_id"], "ARG-ROOT");
        // S is open; its walk reaches the root through B.
        let item = &report["items"][0];
        assert_eq!(item["statement_id"], "S");
        assert_eq!(
            item["path_to_root"],
            json!(["S", "ARG-B", "B", "ARG-ROOT", "ROOT"])
        );
        // Establishing S alone drops the route cost by one.
        assert_eq!(frontier.probe("S")["ARG-ROOT"], 1);
    }

    #[test]
    fn floor_reasons_follow_python() {
        let mut fixture = fixture();
        fixture.statements.push(
            json!({"id": "P", "self_evident": {"basis": "observation",
                "justification_ids": ["CLAIM-P"], "sceptical_rival_ids": []}})
            .as_object()
            .cloned()
            .unwrap_or_default(),
        );
        fixture.relations.extend(records(vec![relation(
            "REL-P",
            "NOT-P",
            "alternative_to",
            "P",
        )]));
        let records = fixture.records();
        let frontier = Frontier::new("ROOT", &records, &[]);
        let none = HashSet::new();
        assert_eq!(
            frontier.floor_reasons("P", &none, &none),
            [
                "no justification claim states it",
                "rivals not recorded as global sceptical positions: NOT-P",
            ]
        );
    }

    #[test]
    fn delta_reports_moves_and_route_changes() {
        let fixture = fixture();
        let records = fixture.records();
        let mut head = Frontier::new("ROOT", &records, &[]).report(false);
        restrict_to_root(&mut head);
        let delta = frontier_delta(&head, &head);
        assert_eq!(delta["changed"], false);
        let mut base = head.clone();
        base["items"] = json!([]);
        base["routes"]["routes"][0]["cost"] = json!(1);
        let delta = frontier_delta(&base, &head);
        assert_eq!(delta["added"]["stated"], json!(["S"]));
        assert_eq!(delta["route_changes"][0]["head_cost"], 2);
        let mut delta = delta;
        delta["base"] = json!("BASE");
        delta["head"] = json!("working tree");
        let text = format_frontier_delta(&delta);
        assert!(text.contains("added (stated): 1\n  S"));
    }
}
