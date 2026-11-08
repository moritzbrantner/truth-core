//! `related`: discovery ranking of propositions connected to one statement,
//! ported from `scripts/research_index.py` (`related`) and the text view of
//! `scripts/corpus.py related`.
//!
//! Python ranks over its disposable SQLite projection
//! (`.cache/research-index.sqlite`). The projection holds the same corpus
//! records, so Rust ranks over the loaded corpus in memory and writes no
//! cache. Discovery only: nothing here is an equivalence, entailment or
//! certification judgment.

use crate::{Corpus, Record, pyfmt};
use serde::Serialize;
use serde_json::{Map, Value};
use std::collections::{BTreeMap, BTreeSet, HashMap};

pub const DEFAULT_LIMIT: i64 = 10;
/// `legacy_uuid("statement", "STMT-CONFIGURATION-FALSE")`.
const CONFIGURATION_FALSE: &str = "37f33696-dc47-5bd3-9cd8-edfd5bf00aa5";
const STOP_WORDS: &str = "a an the is are of to and or in for that this its it with by from as not every all some only has have be being";

/// Why a lookup failed; `Unknown` is an unknown exact ID.
#[derive(Debug, PartialEq, Eq)]
pub enum LookupError {
    Unknown(String),
    Invalid(String),
}

impl LookupError {
    pub fn message(&self) -> &str {
        match self {
            Self::Unknown(message) | Self::Invalid(message) => message,
        }
    }
}

#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct ResultRef {
    pub id: Value,
    pub theorem: Value,
    pub status: Value,
}

/// One piece of evidence connecting two statements. Field order follows Python.
#[derive(Debug, Clone, Serialize, PartialEq)]
#[serde(untagged)]
pub enum Reason {
    Argument {
        kind: &'static str,
        argument_id: String,
        path: String,
        premise_statement_ids: Vec<String>,
        conclusion_statement_id: Option<String>,
        results: Vec<ResultRef>,
        qualification: &'static str,
    },
    Relation {
        kind: &'static str,
        relation_id: String,
        predicate: Value,
        subject_id: Value,
        object_id: Value,
        path: String,
        qualification: &'static str,
    },
    Shared {
        kind: &'static str,
        ids: Vec<String>,
    },
    Declaration {
        kind: &'static str,
        declaration: String,
        qualification: &'static str,
    },
    Namespace {
        kind: &'static str,
        namespace: String,
        qualification: &'static str,
    },
    Text {
        kind: &'static str,
        words: Vec<String>,
        qualification: &'static str,
    },
}

impl Reason {
    pub fn kind(&self) -> &'static str {
        match self {
            Self::Argument { kind, .. }
            | Self::Relation { kind, .. }
            | Self::Shared { kind, .. }
            | Self::Declaration { kind, .. }
            | Self::Namespace { kind, .. }
            | Self::Text { kind, .. } => kind,
        }
    }

    fn premise_count(&self) -> Option<usize> {
        match self {
            Self::Argument {
                premise_statement_ids,
                ..
            } => Some(premise_statement_ids.len()),
            _ => None,
        }
    }

    /// The text view's evidence column (Python's `or` chain).
    fn evidence(&self) -> String {
        match self {
            Self::Argument { argument_id, .. } => argument_id.clone(),
            Self::Relation { relation_id, .. } => relation_id.clone(),
            Self::Shared { ids, .. } => ids.join(", "),
            Self::Declaration { declaration, .. } => declaration.clone(),
            Self::Namespace { namespace, .. } => namespace.clone(),
            Self::Text { words, .. } => words.join(", "),
        }
    }
}

#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct Match {
    pub statement_id: String,
    pub paraphrase: Value,
    pub path: String,
    pub tier: u8,
    pub reason_count: usize,
    pub reasons: Vec<Reason>,
}

#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct PriorAttempt {
    pub id: String,
    pub path: String,
    pub outcome: Value,
    pub summary: Value,
    pub blocker: Value,
}

#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct RelatedReport {
    pub statement_id: String,
    pub mode: &'static str,
    pub ranking: [&'static str; 4],
    pub candidate_count: usize,
    pub matches: Vec<Match>,
    pub prior_attempts: Vec<PriorAttempt>,
    pub scope: &'static str,
}

fn text<'a>(record: &'a Map<String, Value>, field: &str) -> &'a str {
    record
        .get(field)
        .and_then(Value::as_str)
        .unwrap_or_default()
}

fn strings(record: &Map<String, Value>, field: &str) -> Vec<String> {
    record
        .get(field)
        .and_then(Value::as_array)
        .map(|items| {
            items
                .iter()
                .filter_map(Value::as_str)
                .map(str::to_owned)
                .collect()
        })
        .unwrap_or_default()
}

fn field(record: &Map<String, Value>, name: &str) -> Value {
    record.get(name).cloned().unwrap_or(Value::Null)
}

/// Every string in a record outside `id` fields (Python `references`).
fn references<'a>(value: &'a Value, out: &mut Vec<&'a str>) {
    match value {
        Value::String(text) => out.push(text),
        Value::Array(items) => items.iter().for_each(|item| references(item, out)),
        Value::Object(map) => map
            .iter()
            .filter(|(key, _)| key.as_str() != "id")
            .for_each(|(_, item)| references(item, out)),
        _ => {}
    }
}

/// Resolve an exact ID or `kind:ID` to exactly one record (Python `record`).
pub fn resolve<'a>(
    corpus: &'a Corpus,
    identifier: &'a str,
) -> Result<(&'static str, &'a Record), LookupError> {
    let mut found: Vec<(&'static str, &Record)> = corpus.inspect(identifier).collect();
    if let Some((kind, id)) = identifier.split_once(':') {
        found.extend(
            corpus
                .inspect(id)
                .filter(|(found_kind, _)| *found_kind == kind),
        );
    }
    match found.as_slice() {
        [] => Err(LookupError::Unknown(format!(
            "unknown record: {identifier}"
        ))),
        [one] => Ok(*one),
        _ => Err(LookupError::Invalid(format!(
            "ambiguous ID; use kind:ID, for example results:{identifier}"
        ))),
    }
}

fn words(value: &str, stop: &BTreeSet<&str>) -> BTreeSet<String> {
    let lower = value.to_lowercase();
    let mut found = BTreeSet::new();
    let mut current = String::new();
    let mut flush = |current: &mut String| {
        if current.len() >= 2 && !stop.contains(current.as_str()) {
            found.insert(current.clone());
        }
        current.clear();
    };
    for c in lower.chars() {
        if c.is_ascii_lowercase() || (!current.is_empty() && c.is_ascii_digit()) {
            current.push(c);
        } else {
            flush(&mut current);
        }
    }
    flush(&mut current);
    found
}

struct Evidence {
    tier: u8,
    reasons: Vec<Reason>,
}

/// Python `research_index.related`: rank by recorded argument connections,
/// recorded relations, shared terms or Lean declaration, then paraphrase overlap.
pub fn related(
    corpus: &Corpus,
    identifier: &str,
    limit: i64,
) -> Result<RelatedReport, LookupError> {
    let (kind, target) = resolve(corpus, identifier)?;
    let sid = text(&target.fields, "id").to_owned();
    let statements = corpus.entries("statements");
    let by_id: HashMap<&str, &Record> = statements
        .iter()
        .map(|record| (text(&record.fields, "id"), *record))
        .collect();
    if kind != "statements"
        || !by_id.contains_key(sid.as_str())
        || (identifier.contains(':') && !identifier.starts_with("statements:"))
    {
        return Err(LookupError::Invalid(
            "related requires a statement ID".into(),
        ));
    }
    let target = &target.fields;
    let mut evidence: BTreeMap<String, Evidence> = BTreeMap::new();
    let mut add = |other: &str, tier: u8, reason: Reason| {
        if by_id.contains_key(other) && other != sid {
            let entry = evidence.entry(other.to_owned()).or_insert(Evidence {
                tier,
                reasons: Vec::new(),
            });
            entry.tier = entry.tier.min(tier);
            entry.reasons.push(reason);
        }
    };
    let mut results: HashMap<&str, Vec<ResultRef>> = HashMap::new();
    for result in corpus.entries("results") {
        results
            .entry(text(&result.fields, "argument_id"))
            .or_default()
            .push(ResultRef {
                id: field(&result.fields, "id"),
                theorem: field(&result.fields, "theorem"),
                status: field(&result.fields, "status"),
            });
    }
    for record in corpus.entries("arguments") {
        let argument = &record.fields;
        let premises = strings(argument, "premise_statement_ids");
        let conclusion = argument
            .get("conclusion_statement_id")
            .and_then(Value::as_str)
            .map(str::to_owned);
        let concludes = conclusion.as_deref() == Some(sid.as_str());
        if !premises.contains(&sid) && !concludes {
            continue;
        }
        let others: BTreeSet<&str> = premises
            .iter()
            .map(String::as_str)
            .chain(conclusion.as_deref().filter(|c| !c.is_empty()))
            .filter(|other| *other != sid)
            .collect();
        for other in others {
            let other_is_premise = premises.iter().any(|premise| premise == other);
            let role = if conclusion.as_deref() == Some(CONFIGURATION_FALSE) && other_is_premise {
                "incompatible_bundle_member"
            } else if premises.contains(&sid) && other_is_premise {
                "joint_premise"
            } else if premises.contains(&sid) {
                "consequence_with_full_bundle"
            } else {
                "supporting_premise"
            };
            add(
                other,
                0,
                Reason::Argument {
                    kind: role,
                    argument_id: text(argument, "id").to_owned(),
                    path: record.path.clone(),
                    premise_statement_ids: premises.clone(),
                    conclusion_statement_id: conclusion.clone(),
                    results: results
                        .get(text(argument, "id"))
                        .cloned()
                        .unwrap_or_default(),
                    qualification: "Recorded argument; all premises are retained. Not newly verified.",
                },
            );
        }
    }
    for record in corpus.entries("relations") {
        let relation = &record.fields;
        let (subject, object) = (
            relation.get("subject_id").and_then(Value::as_str),
            relation.get("object_id").and_then(Value::as_str),
        );
        if subject != Some(sid.as_str()) && object != Some(sid.as_str()) {
            continue;
        }
        let other = if subject == Some(sid.as_str()) {
            object
        } else {
            subject
        };
        add(
            other.unwrap_or_default(),
            1,
            Reason::Relation {
                kind: "recorded_relation",
                relation_id: text(relation, "id").to_owned(),
                predicate: field(relation, "predicate"),
                subject_id: field(relation, "subject_id"),
                object_id: field(relation, "object_id"),
                path: record.path.clone(),
                qualification: "Recorded semantic relation, not a proof of entailment.",
            },
        );
    }
    let declaration = text(target, "lean_declaration");
    let namespace = declaration
        .rsplit_once('.')
        .map_or(declaration, |(ns, _)| ns);
    for record in &statements {
        let statement = &record.fields;
        let other = text(statement, "id");
        for (name, kind) in [
            ("definition_ids", "shared_definition_ids"),
            ("disambiguation_ids", "shared_disambiguation_ids"),
        ] {
            let mine: BTreeSet<String> = strings(target, name).into_iter().collect();
            let shared: Vec<String> = strings(statement, name)
                .into_iter()
                .collect::<BTreeSet<_>>()
                .intersection(&mine)
                .cloned()
                .collect();
            if !shared.is_empty() {
                add(other, 2, Reason::Shared { kind, ids: shared });
            }
        }
        let candidate = text(statement, "lean_declaration");
        if !declaration.is_empty() && declaration == candidate {
            add(
                other,
                2,
                Reason::Declaration {
                    kind: "same_lean_declaration",
                    declaration: declaration.to_owned(),
                    qualification: "Check parameterization and readings before claiming equivalence.",
                },
            );
        } else if declaration.matches('.').count() >= 3
            && namespace == candidate.rsplit_once('.').map_or(candidate, |(ns, _)| ns)
        {
            add(
                other,
                2,
                Reason::Namespace {
                    kind: "shared_lean_namespace",
                    namespace: namespace.to_owned(),
                    qualification: "Module proximity only; no type or predicate equivalence inferred.",
                },
            );
        }
    }
    let stop: BTreeSet<&str> = STOP_WORDS.split(' ').collect();
    let tokens: Vec<(&str, BTreeSet<String>)> = statements
        .iter()
        .map(|record| {
            (
                text(&record.fields, "id"),
                words(text(&record.fields, "paraphrase"), &stop),
            )
        })
        .collect();
    let mut counts: HashMap<&str, usize> = HashMap::new();
    for word in tokens.iter().flat_map(|(_, group)| group) {
        *counts.entry(word).or_default() += 1;
    }
    let own = tokens
        .iter()
        .find(|(id, _)| *id == sid)
        .map(|(_, group)| group.clone())
        .unwrap_or_default();
    let mut text_scores: HashMap<&str, f64> = HashMap::new();
    for (other, group) in &tokens {
        let overlap: Vec<String> = own.intersection(group).cloned().collect();
        if overlap.len() >= 2 {
            let score = overlap
                .iter()
                .map(|word| (1.0 + tokens.len() as f64 / counts[word.as_str()] as f64).ln())
                .sum::<f64>();
            text_scores.insert(other, score);
            add(
                other,
                3,
                Reason::Text {
                    kind: "text_overlap",
                    words: overlap,
                    qualification: "Discovery heuristic only; no logical relationship established.",
                },
            );
        }
    }
    let bundle_size = |entry: &Evidence| {
        entry
            .reasons
            .iter()
            .filter_map(Reason::premise_count)
            .min()
            .unwrap_or(1_000_000)
    };
    let shared_ids = |entry: &Evidence| {
        entry
            .reasons
            .iter()
            .map(|reason| match reason {
                Reason::Shared { ids, .. } => ids.len(),
                _ => 0,
            })
            .sum::<usize>()
    };
    let mut ranked: Vec<(&String, &Evidence)> = evidence.iter().collect();
    ranked.sort_by(|(a_id, a), (b_id, b)| {
        let score = |id: &String| text_scores.get(id.as_str()).copied().unwrap_or(0.0);
        a.tier
            .cmp(&b.tier)
            .then(bundle_size(a).cmp(&bundle_size(b)))
            .then(shared_ids(b).cmp(&shared_ids(a)))
            .then(score(b_id).total_cmp(&score(a_id)))
            .then(a_id.cmp(b_id))
    });
    let keep = limit.clamp(1, 200) as usize;
    let matches = ranked
        .into_iter()
        .take(keep)
        .map(|(other, entry)| {
            let mut reasons = entry.reasons.clone();
            reasons.sort_by_key(|reason| {
                (
                    usize::from(!matches!(reason, Reason::Argument { .. })),
                    reason.premise_count().unwrap_or(0),
                )
            });
            let record = by_id[other.as_str()];
            Match {
                statement_id: other.clone(),
                paraphrase: field(&record.fields, "paraphrase"),
                path: record.path.clone(),
                tier: entry.tier,
                reason_count: reasons.len(),
                reasons,
            }
        })
        .collect();
    let mut prior_attempts: Vec<PriorAttempt> = corpus
        .entries("attempts")
        .into_iter()
        .filter(|record| {
            let mut found = Vec::new();
            record
                .fields
                .iter()
                .filter(|(key, _)| key.as_str() != "id")
                .for_each(|(_, value)| references(value, &mut found));
            found.contains(&sid.as_str())
        })
        .map(|record| PriorAttempt {
            id: text(&record.fields, "id").to_owned(),
            path: record.path.clone(),
            outcome: field(&record.fields, "outcome"),
            summary: field(&record.fields, "summary"),
            blocker: field(&record.fields, "blocker"),
        })
        .collect();
    prior_attempts.sort_by(|a, b| a.id.cmp(&b.id));
    Ok(RelatedReport {
        statement_id: sid,
        mode: "discovery, not certification",
        ranking: [
            "recorded argument connections (smaller premise bundles first)",
            "recorded semantic relations",
            "shared definitions/disambiguations/declaration or namespace",
            "weighted paraphrase overlap",
        ],
        candidate_count: evidence.len(),
        matches,
        prior_attempts,
        scope: "No automatic equivalence, strengthening, contradiction or cross-profile composition is inferred.",
    })
}

/// The text view of `corpus.py related`.
pub fn format_related(report: &RelatedReport) -> String {
    let mut lines = vec![format!(
        "Related to {} (discovery, not certification)",
        report.statement_id
    )];
    for item in &report.matches {
        lines.push(format!(
            "\n{}: {}",
            item.statement_id,
            pyfmt::text(&item.paraphrase)
        ));
        lines.push(format!("  {}", item.path));
        for reason in item.reasons.iter().take(3) {
            lines.push(format!("  {}: {}", reason.kind(), reason.evidence()));
            if let Reason::Argument {
                premise_statement_ids,
                conclusion_statement_id,
                ..
            } = reason
            {
                lines.push(format!(
                    "    requires: {}",
                    premise_statement_ids.join(", ")
                ));
                lines.push(format!(
                    "    concludes: {}",
                    conclusion_statement_id.as_deref().unwrap_or("None")
                ));
            }
        }
        if item.reason_count > 3 {
            lines.push(format!(
                "  {} reasons total; showing 3 (all in --json)",
                item.reason_count
            ));
        }
    }
    lines.push("\nPrior attempts:".into());
    for attempt in &report.prior_attempts {
        lines.push(format!(
            "  {} [{}]: {}",
            attempt.id,
            pyfmt::text(&attempt.outcome),
            attempt.path
        ));
    }
    if report.prior_attempts.is_empty() {
        lines.push("  none directly linked".into());
    }
    lines.push("\nUse dossier for premise status and configurations for certification.".into());
    lines.join("\n")
}
