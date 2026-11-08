//! Premise dossiers, ported from `scripts/premise_dossiers.py`
//! (`dossier_index`, `format_dossier`) and `scripts/corpus.py dossier`.
//!
//! A dossier is a projection of corpus records plus the frontier report.
//! The frontier report stays the authority for closure, floor bases, route
//! costs and transcription kinds: [`FrontierView`] reads exactly the report
//! fields the dossier and context views consume, from a `corpus.py frontier
//! --json` report (or any report with the same shape). Nothing here closes a
//! statement or changes a route cost.

use crate::senses::{SenseLabels, format_labels};
use crate::{Corpus, pyfmt};
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

pub const DEFAULT_LIMIT: i64 = 8;

type Record = Map<String, Value>;

#[derive(Debug, Clone, Deserialize)]
pub struct TranscriptionKind {
    pub kind: String,
    #[serde(default)]
    pub declared: bool,
}

#[derive(Debug, Clone, Default, Deserialize)]
struct RouteReport {
    #[serde(default)]
    routes: Vec<Value>,
}

/// The frontier report fields that `dossier` and `context` read. Items,
/// floor entries and routes are frontier-owned shapes passed through as JSON.
#[derive(Debug, Clone, Deserialize)]
pub struct FrontierView {
    pub root: Option<String>,
    #[serde(default)]
    pub root_known: bool,
    #[serde(default)]
    pub closed_statements: BTreeMap<String, String>,
    #[serde(default)]
    pub established_statements: BTreeSet<String>,
    #[serde(default)]
    pub reaching_root_statements: BTreeSet<String>,
    #[serde(default)]
    pub transcription_results: BTreeMap<String, TranscriptionKind>,
    #[serde(default)]
    pub floor: Vec<Value>,
    #[serde(default)]
    pub items: Vec<Value>,
    #[serde(default)]
    routes: RouteReport,
    #[serde(skip)]
    item_index: HashMap<String, usize>,
    #[serde(skip)]
    floor_index: HashMap<String, usize>,
    #[serde(skip)]
    route_leaves: Vec<HashSet<String>>,
}

impl FrontierView {
    pub fn from_report(report: &Value) -> Result<Self, String> {
        let mut view =
            Self::deserialize(report).map_err(|error| format!("not a frontier report: {error}"))?;
        let by_statement = |entries: &[Value]| {
            let mut index = HashMap::new();
            for (position, entry) in entries.iter().enumerate() {
                if let Some(id) = entry["statement_id"].as_str() {
                    index.entry(id.to_owned()).or_insert(position);
                }
            }
            index
        };
        view.item_index = by_statement(&view.items);
        view.floor_index = by_statement(&view.floor);
        view.route_leaves = view
            .routes
            .routes
            .iter()
            .map(|route| {
                route["open_premise_statement_ids"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .filter_map(Value::as_str)
                    .map(str::to_owned)
                    .collect()
            })
            .collect();
        Ok(view)
    }

    /// The root routes, in report order.
    pub fn routes(&self) -> &[Value] {
        &self.routes.routes
    }

    pub fn item(&self, statement_id: &str) -> Option<&Value> {
        self.item_index
            .get(statement_id)
            .map(|position| &self.items[*position])
    }

    pub fn floor_entry(&self, statement_id: &str) -> Option<&Value> {
        self.floor_index
            .get(statement_id)
            .map(|position| &self.floor[*position])
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct ConfigurationCase {
    pub id: String,
    pub semantics_id: Value,
    pub href: String,
    pub verification: &'static str,
}

#[derive(Debug, Clone, Serialize)]
pub struct ModelEvaluation {
    pub model_id: String,
    pub vocabulary: Value,
    pub lean_declaration: Value,
    pub value: Value,
    pub theorem: Value,
    pub arguments: Vec<Value>,
}

#[derive(Debug, Clone, Serialize)]
pub struct RouteContribution {
    pub argument_id: Value,
    pub cost: Value,
    pub open_leaf: bool,
    pub direct_premise: bool,
}

/// One statement's dossier; field order follows Python `dossier_index`.
#[derive(Debug, Clone, Serialize)]
pub struct Dossier {
    pub statement: Record,
    pub root: Option<String>,
    pub closure: Option<String>,
    pub floor: Option<Value>,
    pub established: bool,
    pub frontier: Option<Value>,
    pub claim_ids: Vec<String>,
    pub supporting_claim_ids: Vec<String>,
    pub bibliographic_claim_ids: Vec<String>,
    pub unavailable_claim_ids: Vec<String>,
    pub definition_ids: Vec<String>,
    pub disambiguation_ids: Vec<String>,
    pub argument_ids: Vec<String>,
    pub result_ids: Vec<String>,
    pub transcription_result_ids: Vec<String>,
    pub instantiation_result_ids: Vec<String>,
    pub alternative_relation_ids: Vec<String>,
    pub objection_relation_ids: Vec<String>,
    pub attempts: Vec<Record>,
    pub countermodel_attempt_ids: Vec<String>,
    pub configuration_cases: Vec<ConfigurationCase>,
    pub model_evaluations: Vec<ModelEvaluation>,
    pub route_contributions: Vec<RouteContribution>,
}

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

fn ids(records: &[&Record]) -> Vec<String> {
    let mut ids: Vec<String> = records.iter().map(|r| text(r, "id").to_owned()).collect();
    ids.sort();
    ids
}

/// Statements a configuration case touches: its seed and its applications.
pub fn configuration_statements(case: &Record) -> Vec<&str> {
    let mut statements = vec![text(case, "seed_statement_id")];
    match case
        .get("semantics")
        .and_then(|semantics| semantics.get("applications"))
    {
        Some(Value::Object(map)) => statements.extend(map.keys().map(String::as_str)),
        Some(Value::Array(items)) => statements.extend(items.iter().filter_map(Value::as_str)),
        _ => {}
    }
    statements
}

/// The corpus records a dossier reads, in file order, with lookups shared by
/// every statement's projection.
pub struct DossierIndex<'a> {
    statements: HashMap<&'a str, &'a Record>,
    claims: HashMap<&'a str, Vec<&'a Record>>,
    claim_position: HashMap<&'a str, (usize, &'a Record)>,
    relations: HashMap<&'a str, Vec<&'a Record>>,
    arguments: HashMap<&'a str, BTreeSet<&'a str>>,
    argument_records: HashMap<&'a str, &'a Record>,
    premises: HashMap<&'a str, HashSet<&'a str>>,
    results: HashMap<&'a str, Vec<&'a str>>,
    attempts: HashMap<&'a str, Vec<&'a Record>>,
    models: Vec<&'a Record>,
    configurations: Vec<&'a Record>,
    definitions: HashSet<&'a str>,
    disambiguations: Vec<&'a Record>,
    pub index: HashMap<&'static str, HashMap<&'a str, &'a Record>>,
    senses: SenseLabels<'a>,
}

impl<'a> DossierIndex<'a> {
    pub fn new(corpus: &'a Corpus) -> Self {
        let mut models = corpus.records("models");
        models.sort_by_key(|record| text(record, "id"));
        let mut configurations = corpus.records("configurations");
        configurations.sort_by_key(|record| text(record, "id"));
        let index = [
            "claims",
            "definitions",
            "disambiguations",
            "relations",
            "arguments",
            "results",
        ]
        .into_iter()
        .map(|kind| {
            (
                kind,
                corpus
                    .records(kind)
                    .into_iter()
                    .map(|record| (text(record, "id"), record))
                    .collect(),
            )
        })
        .collect();
        let claim_records = corpus.records("claims");
        let mut claims: HashMap<&str, Vec<&Record>> = HashMap::new();
        for claim in &claim_records {
            claims
                .entry(text(claim, "statement_id"))
                .or_default()
                .push(claim);
        }
        let mut relations: HashMap<&str, Vec<&Record>> = HashMap::new();
        for relation in corpus.records("relations") {
            let (subject, object) = (text(relation, "subject_id"), text(relation, "object_id"));
            relations.entry(subject).or_default().push(relation);
            if object != subject {
                relations.entry(object).or_default().push(relation);
            }
        }
        // An intermediate inference output may occur without being an
        // argument's outer premise or conclusion.
        let mut inferences: HashMap<&str, HashSet<&str>> = HashMap::new();
        for inference in corpus.records("inferences") {
            for sid in list(inference, "input_statement_ids")
                .into_iter()
                .chain(list(inference, "assumption_statement_ids"))
                .chain(list(inference, "discharged_statement_ids"))
                .chain([text(inference, "output_statement_id")])
            {
                inferences
                    .entry(sid)
                    .or_default()
                    .insert(text(inference, "id"));
            }
        }
        let argument_records = corpus.records("arguments");
        let mut by_inference: HashMap<&str, Vec<&str>> = HashMap::new();
        let mut arguments: HashMap<&str, BTreeSet<&str>> = HashMap::new();
        for argument in &argument_records {
            let id = text(argument, "id");
            for inference in list(argument, "inference_ids") {
                by_inference.entry(inference).or_default().push(id);
            }
            for sid in list(argument, "premise_statement_ids")
                .into_iter()
                .chain(list(argument, "commitment_statement_ids"))
                .chain([text(argument, "conclusion_statement_id")])
            {
                arguments.entry(sid).or_default().insert(id);
            }
        }
        for (sid, inference_ids) in &inferences {
            let touching = arguments.entry(sid).or_default();
            for inference in inference_ids {
                touching.extend(by_inference.get(inference).into_iter().flatten());
            }
        }
        let mut results: HashMap<&str, Vec<&str>> = HashMap::new();
        for result in corpus.records("results") {
            results
                .entry(text(result, "argument_id"))
                .or_default()
                .push(text(result, "id"));
        }
        let mut attempts: HashMap<&str, Vec<&Record>> = HashMap::new();
        for attempt in corpus.records("attempts") {
            let mut seen = HashSet::new();
            for sid in list(attempt, "statement_ids") {
                if seen.insert(sid) {
                    attempts.entry(sid).or_default().push(attempt);
                }
            }
        }
        Self {
            senses: SenseLabels::new(corpus),
            statements: corpus
                .records("statements")
                .into_iter()
                .map(|record| (text(record, "id"), record))
                .collect(),
            claim_position: claim_records
                .iter()
                .enumerate()
                .map(|(position, claim)| (text(claim, "id"), (position, *claim)))
                .collect(),
            claims,
            relations,
            arguments,
            premises: argument_records
                .iter()
                .map(|argument| {
                    (
                        text(argument, "id"),
                        list(argument, "premise_statement_ids")
                            .into_iter()
                            .collect(),
                    )
                })
                .collect(),
            argument_records: argument_records
                .iter()
                .map(|argument| (text(argument, "id"), *argument))
                .collect(),
            results,
            attempts,
            models,
            configurations,
            definitions: corpus
                .records("definitions")
                .into_iter()
                .map(|record| text(record, "id"))
                .collect(),
            disambiguations: corpus.records("disambiguations"),
            index,
        }
    }

    pub fn statement_ids(&self) -> Vec<&'a str> {
        let mut ids: Vec<&str> = self.statements.keys().copied().collect();
        ids.sort_unstable();
        ids
    }

    /// Python `dossier_index(...)[sid]`; `None` for an unknown statement.
    pub fn dossier(&self, sid: &str, report: &FrontierView) -> Option<Dossier> {
        let statement = *self.statements.get(sid)?;
        let claims: Vec<&Record> = self.claims.get(sid).cloned().unwrap_or_default();
        let relations: Vec<&Record> = self.relations.get(sid).cloned().unwrap_or_default();
        let mut supporting_claims: Vec<(usize, &Record)> = relations
            .iter()
            .filter(|r| text(r, "predicate") == "supports" && text(r, "object_id") == sid)
            .filter_map(|r| self.claim_position.get(text(r, "subject_id")).copied())
            .collect();
        supporting_claims.sort_by_key(|(position, _)| *position);
        supporting_claims.dedup_by_key(|(position, _)| *position);
        let supporting_claims: Vec<&Record> = supporting_claims
            .into_iter()
            .map(|(_, claim)| claim)
            .collect();
        let touching_ids: BTreeSet<&str> = self.arguments.get(sid).cloned().unwrap_or_default();
        let mut result_ids: Vec<String> = touching_ids
            .iter()
            .flat_map(|id| self.results.get(id).into_iter().flatten())
            .map(|id| (*id).to_owned())
            .collect();
        result_ids.sort();
        let term_records = std::iter::once(statement)
            .chain(claims.iter().copied())
            .chain(supporting_claims.iter().copied())
            .chain(touching_ids.iter().map(|id| self.argument_records[id]));
        let mut definition_ids: BTreeSet<&str> = BTreeSet::new();
        let mut disambiguation_ids: BTreeSet<&str> = BTreeSet::new();
        for record in term_records {
            definition_ids.extend(list(record, "definition_ids"));
            disambiguation_ids.extend(list(record, "disambiguation_ids"));
        }
        for entry in &self.disambiguations {
            if list(entry, "sense_definition_ids")
                .iter()
                .any(|id| definition_ids.contains(id))
            {
                disambiguation_ids.insert(text(entry, "id"));
            }
        }
        for entry in &self.disambiguations {
            if disambiguation_ids.contains(text(entry, "id")) {
                definition_ids.extend(list(entry, "sense_definition_ids"));
            }
        }
        let mut attempts: Vec<&Record> = self.attempts.get(sid).cloned().unwrap_or_default();
        attempts.sort_by_key(|attempt| (text(attempt, "date"), text(attempt, "id")));
        let transcriptions: Vec<String> = result_ids
            .iter()
            .filter(|id| report.transcription_results.contains_key(*id))
            .cloned()
            .collect();
        let witnessed = |witness: &str| {
            // Python keeps a claim twice when it both states and supports.
            ids(&claims
                .iter()
                .chain(&supporting_claims)
                .copied()
                .filter(|claim| claim.get("witness").and_then(Value::as_str) == Some(witness))
                .collect::<Vec<_>>())
        };
        let predicate_ids = |predicate: &str| {
            ids(&relations
                .iter()
                .copied()
                .filter(|r| text(r, "predicate") == predicate)
                .collect::<Vec<_>>())
        };
        Some(Dossier {
            statement: statement.clone(),
            root: report.root.clone(),
            closure: report.closed_statements.get(sid).cloned(),
            floor: report.floor_entry(sid).cloned(),
            established: report.established_statements.contains(sid),
            frontier: report.item(sid).cloned(),
            claim_ids: ids(&claims),
            supporting_claim_ids: ids(&supporting_claims),
            bibliographic_claim_ids: witnessed("bibliographic"),
            unavailable_claim_ids: witnessed("unavailable"),
            definition_ids: definition_ids
                .iter()
                .filter(|id| self.definitions.contains(*id))
                .map(|id| (*id).to_owned())
                .collect(),
            disambiguation_ids: disambiguation_ids
                .iter()
                .map(|id| (*id).to_owned())
                .collect(),
            argument_ids: touching_ids.iter().map(|id| (*id).to_owned()).collect(),
            instantiation_result_ids: transcriptions
                .iter()
                .filter(|id| report.transcription_results[*id].kind == "instantiation")
                .cloned()
                .collect(),
            transcription_result_ids: transcriptions,
            result_ids,
            alternative_relation_ids: predicate_ids("alternative_to"),
            objection_relation_ids: predicate_ids("attacks"),
            countermodel_attempt_ids: attempts
                .iter()
                .filter(|attempt| text(attempt, "kind") == "countermodel")
                .map(|attempt| text(attempt, "id").to_owned())
                .collect(),
            attempts: attempts.into_iter().cloned().collect(),
            configuration_cases: self
                .configurations
                .iter()
                .filter(|case| configuration_statements(case).contains(&sid))
                .map(|case| ConfigurationCase {
                    id: text(case, "id").to_owned(),
                    semantics_id: case
                        .get("semantics")
                        .and_then(|s| s.get("id"))
                        .cloned()
                        .unwrap_or(Value::Null),
                    href: format!("/configurations/{}", text(case, "id")),
                    verification: "required (registration only)",
                })
                .collect(),
            model_evaluations: self
                .models
                .iter()
                .flat_map(|model| {
                    model
                        .get("evaluations")
                        .and_then(Value::as_array)
                        .into_iter()
                        .flatten()
                        .filter_map(Value::as_object)
                        .filter(|evaluation| text(evaluation, "statement_id") == sid)
                        .map(|evaluation| ModelEvaluation {
                            model_id: text(model, "id").to_owned(),
                            vocabulary: model.get("vocabulary").cloned().unwrap_or(Value::Null),
                            lean_declaration: model
                                .get("lean_declaration")
                                .cloned()
                                .unwrap_or(Value::Null),
                            value: evaluation.get("value").cloned().unwrap_or(Value::Null),
                            theorem: evaluation.get("theorem").cloned().unwrap_or(Value::Null),
                            arguments: list(evaluation, "arguments")
                                .into_iter()
                                .map(|key| model["bindings"][key].clone())
                                .collect(),
                        })
                })
                .collect(),
            route_contributions: report
                .routes()
                .iter()
                .zip(&report.route_leaves)
                .map(|(route, leaves)| {
                    let argument = route["argument_id"].as_str().unwrap_or_default();
                    RouteContribution {
                        argument_id: route["argument_id"].clone(),
                        cost: route["cost"].clone(),
                        open_leaf: leaves.contains(sid),
                        direct_premise: self
                            .premises
                            .get(argument)
                            .is_some_and(|premises| premises.contains(sid)),
                    }
                })
                .collect(),
        })
    }
}

/// Python `format_dossier`: `limit` caps each section (`None` shows all).
pub fn format_dossier(dossier: &Dossier, index: &DossierIndex, limit: Option<usize>) -> String {
    let shown = |len: usize| limit.map_or(len, |limit| limit.min(len));
    let clip = |text: String| -> String {
        let Some(_) = limit else { return text };
        let text = pyfmt::collapse(&text);
        if text.chars().count() <= 220 {
            text
        } else {
            format!("{}…", pyfmt::rstrip(pyfmt::head(&text, 219)))
        }
    };
    let more = |len: usize, lines: &mut Vec<String>| {
        if let Some(limit) = limit
            && len > limit
        {
            lines.push(format!("  … {} more (see --json)", len - limit));
        }
    };
    let statement = &dossier.statement;
    let status = match (&dossier.closure, &dossier.frontier) {
        (Some(closure), _) if !closure.is_empty() => closure.clone(),
        (_, Some(frontier)) => format!("open ({})", pyfmt::text(&frontier["depth"])),
        _ => "not on the frontier".into(),
    };
    let mut lines = vec![
        text(statement, "id").to_owned(),
        pyfmt::text(statement.get("paraphrase").unwrap_or(&Value::Null)),
        format!(
            "Lean: {}",
            statement
                .get("lean_declaration")
                .map_or_else(|| "none".into(), pyfmt::text)
        ),
        format!(
            "Status: {status}; established: {}",
            if dossier.established { "true" } else { "false" }
        ),
    ];
    let senses = index.senses.labels(statement);
    if !senses.is_empty() {
        lines.insert(2, format!("Senses: {}", format_labels(&senses)));
    }
    if let Some(floor) = &dossier.floor {
        let reasons: Vec<String> = floor["reasons"]
            .as_array()
            .into_iter()
            .flatten()
            .map(pyfmt::text)
            .collect();
        let met = if pyfmt::truthy(Some(&floor["met"])) {
            "met".to_owned()
        } else {
            format!("not met, closes nothing: {}", reasons.join("; "))
        };
        let justification: Vec<String> = floor["justification_ids"]
            .as_array()
            .into_iter()
            .flatten()
            .map(pyfmt::text)
            .collect();
        lines.push(format!(
            "Floor basis: {} ({met}); justification: {}",
            pyfmt::text(&floor["basis"]),
            justification.join(", ")
        ));
        let mut disagreement = floor.get("disagreement").cloned().unwrap_or(Value::Null);
        if let Value::Object(map) = &disagreement {
            let names: Vec<String> = ["rival_statement_ids", "claim_ids"]
                .iter()
                .flat_map(|key| {
                    map.get(*key)
                        .and_then(Value::as_array)
                        .into_iter()
                        .flatten()
                })
                .map(pyfmt::text)
                .collect();
            disagreement = Value::String(names.join(", "));
        }
        let disagreement = if pyfmt::truthy(Some(&disagreement)) {
            pyfmt::text(&disagreement)
        } else if floor["basis"].as_str() == Some("common_ground") {
            "recorded rivals agree (common_ground)".into()
        } else {
            "not recorded".into()
        };
        lines.push(format!("Floor disagreement (#378): {disagreement}"));
    }
    let sections: [(&str, &Vec<String>, &str); 8] = [
        ("claims", &dossier.claim_ids, "Source readings"),
        (
            "claims",
            &dossier.supporting_claim_ids,
            "Supporting source readings",
        ),
        ("definitions", &dossier.definition_ids, "Definitions"),
        (
            "disambiguations",
            &dossier.disambiguation_ids,
            "Disambiguations",
        ),
        (
            "relations",
            &dossier.alternative_relation_ids,
            "Alternatives",
        ),
        ("relations", &dossier.objection_relation_ids, "Objections"),
        (
            "arguments",
            &dossier.argument_ids,
            "Arguments (premise, conclusion, commitment or inference)",
        ),
        ("results", &dossier.result_ids, "Results"),
    ];
    let value_text =
        |record: &Record, field: &str| record.get(field).map_or_else(String::new, pyfmt::text);
    for (directory, entries, label) in sections {
        lines.push(format!("\n{label}:"));
        let records = &index.index[directory];
        for record_id in &entries[..shown(entries.len())] {
            let Some(record) = records.get(record_id.as_str()) else {
                continue;
            };
            let mut description = [
                "interpretation",
                "definition",
                "resolution",
                "meaning",
                "description",
                "basis",
            ]
            .iter()
            .find(|field| pyfmt::truthy(record.get(**field)))
            .map_or_else(String::new, |field| value_text(record, field));
            if directory == "claims" {
                description = format!(
                    "{} {}: {description}",
                    value_text(record, "source_id"),
                    value_text(record, "locator")
                );
                match record.get("witness").and_then(Value::as_str) {
                    Some("bibliographic") => {
                        description =
                            format!("[bibliographic witness, not byte-verified] {description}")
                    }
                    Some("unavailable") => {
                        description = format!(
                            "[permanently unavailable witness, not byte-verified] {description}"
                        )
                    }
                    _ => {}
                }
            }
            if directory == "relations" {
                let note = match record.get("note") {
                    Some(note) => pyfmt::text(note),
                    None => record.get("basis").map_or_else(String::new, pyfmt::text),
                };
                description = format!(
                    "{} {} {}: {note}",
                    value_text(record, "subject_id"),
                    value_text(record, "predicate"),
                    value_text(record, "object_id")
                );
            }
            if directory == "results" {
                let theorem = record
                    .get("theorem")
                    .map_or_else(|| "no theorem".into(), pyfmt::text);
                description = format!("{theorem}; {description}");
            }
            if matches!(directory, "definitions" | "arguments") {
                let senses = index.senses.labels(record);
                if !senses.is_empty() {
                    description = format!("[{}] {description}", format_labels(&senses));
                }
            }
            lines.push(format!("  {record_id}: {}", clip(description)));
        }
        more(entries.len(), &mut lines);
        if entries.is_empty() {
            lines.push("  none recorded".into());
        }
    }
    for (entries, label) in [
        (&dossier.transcription_result_ids, "Transcriptions"),
        (
            &dossier.instantiation_result_ids,
            "Declared/recognized instantiations (not a mode-5 schema registry)",
        ),
    ] {
        let joined = if entries.is_empty() {
            "none recorded".into()
        } else {
            entries.join(", ")
        };
        lines.push(format!("\n{label}: {joined}"));
    }
    lines.push(
        "\nConfiguration cases (registration only; run configurations for live verification):"
            .into(),
    );
    for case in &dossier.configuration_cases {
        lines.push(format!(
            "  {}: semantics {}; {}",
            case.id,
            pyfmt::text(&case.semantics_id),
            case.href
        ));
    }
    lines.push("\nAttempts (outcomes do not establish truth or close premises):".into());
    let attempts = &dossier.attempts;
    let start = limit.map_or(0, |limit| attempts.len().saturating_sub(limit));
    if start > 0 {
        lines.push(format!("  … {start} earlier (see --json)"));
    }
    for attempt in &attempts[start..] {
        lines.push(format!(
            "  {} [{}; {}; {}]: {}",
            value_text(attempt, "id"),
            value_text(attempt, "date"),
            value_text(attempt, "kind"),
            value_text(attempt, "outcome"),
            clip(value_text(attempt, "summary"))
        ));
        let evidence: Vec<String> = attempt
            .get("evidence")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .map(pyfmt::text)
            .collect();
        lines.push(format!(
            "    evidence: {}",
            if evidence.is_empty() {
                "none recorded".into()
            } else {
                evidence.join(", ")
            }
        ));
        if pyfmt::truthy(attempt.get("blocker")) {
            lines.push(format!(
                "    blocker: {}",
                clip(value_text(attempt, "blocker"))
            ));
        }
    }
    if attempts.is_empty() {
        lines.push("  none recorded".into());
    }
    lines.push(format!(
        "\nCountermodel attempts: {}",
        if dossier.countermodel_attempt_ids.is_empty() {
            "none recorded".into()
        } else {
            dossier.countermodel_attempt_ids.join(", ")
        }
    ));
    lines.push(
        "Registered finite evaluations (formal interpretations only; no premise closure):".into(),
    );
    let evaluations = &dossier.model_evaluations;
    for evaluation in &evaluations[..shown(evaluations.len())] {
        lines.push(format!(
            "  {} {}; vocabulary {}; {}; arguments {}",
            evaluation.model_id,
            pyfmt::text(&evaluation.value),
            pyfmt::text(&evaluation.vocabulary),
            pyfmt::text(&evaluation.theorem),
            pyfmt::repr(&Value::Array(evaluation.arguments.clone()))
        ));
    }
    more(evaluations.len(), &mut lines);
    if evaluations.is_empty() {
        lines.push("  none registered; no conclusion about consistency or derivability".into());
    }
    lines.push("Explicit instance_of_schema registrations are recorded in corpus/relations/ (see docs/schemas.md); this dossier does not project them. No links are inferred from prose.".into());
    lines.push(format!(
        "\nRoutes to {} (one counted leaf when open_leaf=true, not a counterfactual cost reduction):",
        dossier.root.as_deref().unwrap_or("None")
    ));
    let routes = &dossier.route_contributions;
    for route in &routes[..shown(routes.len())] {
        lines.push(format!(
            "  {}: cost={}, open_leaf={}, direct_premise={}",
            pyfmt::text(&route.argument_id),
            pyfmt::text(&route.cost),
            route.open_leaf,
            route.direct_premise
        ));
    }
    more(routes.len(), &mut lines);
    lines.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn object(value: Value) -> Record {
        value.as_object().cloned().unwrap()
    }

    #[test]
    fn frontier_view_reads_report_fields() {
        let view = FrontierView::from_report(&json!({
            "root": "R", "root_known": true,
            "closed_statements": {"A": "proved"},
            "established_statements": ["A"],
            "transcription_results": {"RES": {"kind": "instantiation", "declared": true}},
            "items": [{"statement_id": "B", "depth": "bare"}],
            "routes": {"routes": [{"argument_id": "ARG", "cost": 1, "open_premise_statement_ids": ["B"]}]},
            "unrelated": 1,
        }))
        .unwrap();
        assert_eq!(view.item("B").unwrap()["depth"], "bare");
        assert_eq!(view.routes().len(), 1);
        assert!(FrontierView::from_report(&json!({"root": 3})).is_err());
    }

    #[test]
    fn configuration_statements_accept_maps_and_lists() {
        let case =
            object(json!({"seed_statement_id": "S", "semantics": {"applications": {"A": 1}}}));
        assert_eq!(configuration_statements(&case), vec!["S", "A"]);
        let case = object(json!({"seed_statement_id": "S", "semantics": {"applications": ["B"]}}));
        assert_eq!(configuration_statements(&case), vec!["S", "B"]);
    }
}
