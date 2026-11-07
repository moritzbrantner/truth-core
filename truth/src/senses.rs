//! Sense labels for display and naming: Python `scripts/sense_labels.py`.
//!
//! Each disambiguation gives its term a `term_label` (PRIOR) and its senses
//! an opaque uuid plus a stable display label TERM_n (PRIOR_1). For any record
//! this answers which sense label each disambiguated term takes in it.

use crate::Corpus;
use serde_json::{Map, Value};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

type Record = Map<String, Value>;

struct Sense<'a> {
    label: &'a str,
    term: &'a str,
}

/// Python `sense_labels_from_data`: senses by definition, with the
/// statements and arguments records refer to.
pub struct SenseLabels<'a> {
    statements: HashMap<&'a str, &'a Record>,
    arguments: HashMap<&'a str, &'a Record>,
    by_definition: HashMap<&'a str, Vec<Sense<'a>>>,
    by_id: HashMap<&'a str, &'a str>,
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

impl<'a> SenseLabels<'a> {
    pub fn new(corpus: &'a Corpus) -> Self {
        let by_id_of = |kind| {
            corpus
                .records(kind)
                .into_iter()
                .map(|record| (text(record, "id"), record))
                .collect::<HashMap<_, _>>()
        };
        let mut by_definition: HashMap<&str, Vec<Sense>> = HashMap::new();
        let mut by_id = HashMap::new();
        let mut seen = HashSet::new();
        for disambiguation in corpus.records("disambiguations") {
            let term = text(disambiguation, "term_label");
            let senses = disambiguation.get("senses").and_then(Value::as_array);
            for sense in senses.into_iter().flatten().filter_map(Value::as_object) {
                let id = text(sense, "id");
                if !seen.insert(id) {
                    continue;
                }
                let label = text(sense, "label");
                by_id.insert(id, label);
                by_definition
                    .entry(text(sense, "definition_id"))
                    .or_default()
                    .push(Sense { label, term });
            }
        }
        SenseLabels {
            statements: by_id_of("statements"),
            arguments: by_id_of("arguments"),
            by_definition,
            by_id,
        }
    }

    /// Python `record_definitions`.
    fn definitions(&self, record: &'a Record, with_argument: bool) -> Vec<&'a str> {
        let mut definitions = Vec::new();
        if record.contains_key("definition") && record.contains_key("term") {
            definitions.push(text(record, "id"));
        }
        definitions.extend(list(record, "definition_ids"));
        if let Some(statement) = self.statements.get(text(record, "statement_id")) {
            definitions.extend(list(statement, "definition_ids"));
        }
        if with_argument && let Some(argument) = self.arguments.get(text(record, "argument_id")) {
            definitions.extend(self.definitions(argument, false));
        }
        if record.contains_key("conclusion_statement_id") {
            let ids = std::iter::once(text(record, "conclusion_statement_id"))
                .chain(list(record, "premise_statement_ids"))
                .chain(list(record, "commitment_statement_ids"));
            for sid in ids {
                if let Some(statement) = self.statements.get(sid) {
                    definitions.extend(list(statement, "definition_ids"));
                }
            }
        }
        definitions
    }

    /// Python `record_sense_labels`: term -> sorted sense labels.
    pub fn labels(&self, record: &'a Record) -> BTreeMap<String, Vec<String>> {
        let mut labels: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for definition in self.definitions(record, true) {
            for sense in self.by_definition.get(definition).into_iter().flatten() {
                labels
                    .entry(sense.term.to_owned())
                    .or_default()
                    .insert(sense.label.to_owned());
            }
        }
        let mut declared: Vec<(&String, &Value)> = Vec::new();
        if let Some(Value::Object(map)) = record.get("term_senses") {
            declared.extend(map);
        }
        if let Some(argument) = self.arguments.get(text(record, "argument_id"))
            && let Some(Value::Object(map)) = argument.get("term_senses")
        {
            declared.extend(map);
        }
        for (term, sense) in declared {
            if let Some(label) = sense.as_str().and_then(|id| self.by_id.get(id)) {
                labels
                    .entry(term.clone())
                    .or_default()
                    .insert((*label).to_owned());
            }
        }
        labels
            .into_iter()
            .map(|(term, values)| (term, values.into_iter().collect()))
            .collect()
    }
}

/// Python `format_sense_labels`: `PRIOR_1, CAUSE_2`.
pub fn format_labels(labels: &BTreeMap<String, Vec<String>>) -> String {
    labels
        .values()
        .flatten()
        .cloned()
        .collect::<Vec<_>>()
        .join(", ")
}
