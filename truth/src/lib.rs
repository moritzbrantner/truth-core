//! Read-only structural view of the canonical corpus.
pub mod bridges;
pub mod context;
pub mod dossier;
mod kernels;
pub mod pyfmt;
pub mod related;
pub mod thickness;
mod transcription;

use serde_json::{Map, Value};
use std::{collections::BTreeMap, fs, path::Path};

const KINDS: &[&str] = &[
    "sources",
    "passages",
    "statements",
    "claims",
    "inferences",
    "arguments",
    "relations",
    "results",
    "candidates",
    "definitions",
    "disambiguations",
    "attempts",
    "models",
    "configurations",
];

#[derive(Debug)]
pub struct CorpusError {
    pub code: &'static str,
    pub path: String,
    pub message: String,
}

pub struct Record {
    pub path: String,
    pub fields: Map<String, Value>,
}

pub struct Corpus {
    records: BTreeMap<&'static str, BTreeMap<String, Record>>,
    fingerprint: u64,
}

impl Corpus {
    pub fn load(root: &Path) -> Result<Self, CorpusError> {
        let mut corpus = Self {
            records: BTreeMap::new(),
            fingerprint: 0xcbf29ce484222325,
        };
        if fs::symlink_metadata(root.join("corpus"))
            .is_ok_and(|metadata| metadata.file_type().is_symlink())
        {
            return Err(failure(
                "invalid_path",
                "corpus",
                "a symlinked corpus directory is not supported".into(),
            ));
        }
        for &kind in KINDS {
            let directory = root.join("corpus").join(kind);
            if fs::symlink_metadata(&directory)
                .is_ok_and(|metadata| metadata.file_type().is_symlink())
            {
                return Err(failure(
                    "invalid_path",
                    kind,
                    "symlinked corpus directories are not supported".into(),
                ));
            }
            let entries = match fs::read_dir(&directory) {
                Ok(entries) => entries,
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                    if !root.join("corpus").is_dir() {
                        return Err(failure("read_error", "corpus", error.to_string()));
                    }
                    corpus.records.insert(kind, BTreeMap::new());
                    continue;
                }
                Err(error) => return Err(failure("read_error", kind, error.to_string())),
            };
            let mut paths = entries
                .map(|entry| entry.map(|entry| entry.path()))
                .collect::<Result<Vec<_>, _>>()
                .map_err(|error| failure("read_error", kind, error.to_string()))?;
            paths.sort();
            let mut records: BTreeMap<String, Record> = BTreeMap::new();
            for path in paths {
                if path.extension().and_then(|ext| ext.to_str()) != Some("json") {
                    continue;
                }
                let relative = path
                    .strip_prefix(root)
                    .map_err(|error| failure("read_error", kind, error.to_string()))?
                    .to_str()
                    .ok_or_else(|| failure("read_error", kind, "non-UTF-8 record path".into()))?
                    .to_owned();
                if fs::symlink_metadata(&path)
                    .map_err(|error| failure("read_error", &relative, error.to_string()))?
                    .file_type()
                    .is_symlink()
                {
                    return Err(failure(
                        "invalid_path",
                        &relative,
                        "symlinked corpus records are not supported".into(),
                    ));
                }
                let bytes = fs::read(path)
                    .map_err(|error| failure("read_error", &relative, error.to_string()))?;
                let fields: Map<String, Value> =
                    serde_json::from_slice(&bytes).map_err(|error| {
                        failure("invalid_json_object", &relative, error.to_string())
                    })?;
                let entries = if kind == "passages" {
                    expand_passages(&fields, &relative)?
                } else {
                    vec![fields]
                };
                for fields in entries {
                    let id = required_string(&fields, "id", &relative)?.to_owned();
                    if let Some(first) = records.get(&id) {
                        return Err(failure(
                            "duplicate_id",
                            &relative,
                            format!("duplicate {kind} id {id}; first seen in {}", first.path),
                        ));
                    }
                    validate_fields(kind, &fields, &relative)?;
                    records.insert(
                        id,
                        Record {
                            path: relative.clone(),
                            fields,
                        },
                    );
                }
                corpus.hash(relative.as_bytes());
                corpus.hash(&bytes);
            }
            corpus.records.insert(kind, records);
        }
        Ok(corpus)
    }

    fn hash(&mut self, bytes: &[u8]) {
        for byte in (bytes.len() as u64)
            .to_le_bytes()
            .into_iter()
            .chain(bytes.iter().copied())
        {
            self.fingerprint ^= u64::from(byte);
            self.fingerprint = self.fingerprint.wrapping_mul(0x100000001b3);
        }
    }

    /// Non-cryptographic identity of the paths and bytes consumed by this loader.
    pub fn input_identity(&self) -> String {
        format!("fnv1a64:{:016x}", self.fingerprint)
    }

    pub fn counts(&self) -> impl Iterator<Item = (&'static str, usize)> + '_ {
        self.records
            .iter()
            .map(|(&kind, records)| (kind, records.len()))
    }

    /// The records of one kind in file order (Python `load_dir` order).
    pub fn records(&self, kind: &str) -> Vec<&Map<String, Value>> {
        let mut records: Vec<&Record> = self
            .records
            .get(kind)
            .map(|records| records.values().collect())
            .unwrap_or_default();
        records.sort_by(|a, b| a.path.cmp(&b.path));
        records.into_iter().map(|record| &record.fields).collect()
    }

    /// The records of one kind with their paths, in file order.
    pub fn entries(&self, kind: &str) -> Vec<&Record> {
        let mut records: Vec<&Record> = self
            .records
            .get(kind)
            .map(|records| records.values().collect())
            .unwrap_or_default();
        records.sort_by(|a, b| a.path.cmp(&b.path));
        records
    }

    /// One record of one kind by ID.
    pub fn get(&self, kind: &str, id: &str) -> Option<&Record> {
        self.records.get(kind).and_then(|records| records.get(id))
    }

    /// Records of one kind in ID order (empty for an unknown kind).
    pub fn records_by_id<'a>(&'a self, kind: &str) -> impl Iterator<Item = (&'a str, &'a Record)> {
        self.records
            .get(kind)
            .into_iter()
            .flat_map(|records| records.iter().map(|(id, record)| (id.as_str(), record)))
    }

    /// IDs are unique within a kind. A lookup returns all exact matches.
    pub fn inspect<'a>(&'a self, id: &'a str) -> impl Iterator<Item = (&'static str, &'a Record)> {
        self.records
            .iter()
            .filter_map(move |(&kind, records)| records.get(id).map(|record| (kind, record)))
    }
}

fn failure(code: &'static str, path: &str, message: String) -> CorpusError {
    CorpusError {
        code,
        path: path.into(),
        message,
    }
}

fn required_string<'a>(
    fields: &'a Map<String, Value>,
    field: &str,
    path: &str,
) -> Result<&'a str, CorpusError> {
    fields
        .get(field)
        .and_then(Value::as_str)
        .filter(|value| !value.is_empty())
        .ok_or_else(|| {
            failure(
                "invalid_field",
                path,
                format!("{field} must be a non-empty string"),
            )
        })
}

fn validate_fields(kind: &str, fields: &Map<String, Value>, path: &str) -> Result<(), CorpusError> {
    let strings: &[&str] = match kind {
        "sources" => &[
            "kind",
            "author",
            "work",
            "citation_system",
            "work_urn",
            "catalog_url",
        ],
        "statements" => &["paraphrase"],
        "claims" => &[
            "statement_id",
            "source_id",
            "locator",
            "interpretation",
            "status",
        ],
        "inferences" => &["output_statement_id", "rule", "meaning"],
        "arguments" => &["conclusion_statement_id", "meaning"],
        "relations" => &[
            "subject_kind",
            "subject_id",
            "predicate",
            "object_kind",
            "object_id",
        ],
        "candidates" => &["source_id", "locator", "goal", "reason", "status"],
        "results" => &[
            "argument_id",
            "challenge_module",
            "solution_module",
            "theorem",
            "comparator_config",
            "status",
        ],
        "definitions" => &["term", "definition", "basis"],
        "disambiguations" => &["term", "resolution"],
        _ => &[],
    };
    for field in strings {
        required_string(fields, field, path)?;
    }
    let lists: &[&str] = match kind {
        "arguments" if fields.contains_key("commitment_statement_ids") => &[
            "premise_statement_ids",
            "inference_ids",
            "commitment_statement_ids",
        ],
        "arguments" => &["premise_statement_ids", "inference_ids"],
        "inferences" => &[
            "input_statement_ids",
            "assumption_statement_ids",
            "discharged_statement_ids",
        ],
        _ => &[],
    };
    for &field in lists {
        let valid = fields
            .get(field)
            .and_then(Value::as_array)
            .is_some_and(|items| {
                (field != "inference_ids" || !items.is_empty())
                    && items
                        .iter()
                        .all(|item| item.as_str().is_some_and(|value| !value.is_empty()))
            });
        if !valid {
            return Err(failure(
                "invalid_field",
                path,
                format!("invalid string list {field}"),
            ));
        }
    }
    if kind == "candidates"
        && !fields
            .get("priority")
            .is_some_and(|value| value.is_i64() || value.is_u64())
    {
        return Err(failure(
            "invalid_field",
            path,
            "priority must be an integer".into(),
        ));
    }
    Ok(())
}

fn expand_passages(
    fields: &Map<String, Value>,
    path: &str,
) -> Result<Vec<Map<String, Value>>, CorpusError> {
    let invalid = || {
        failure(
            "invalid_field",
            path,
            "expected snapshot object and non-empty passages list of objects".into(),
        )
    };
    let snapshot = fields
        .get("snapshot")
        .and_then(Value::as_object)
        .ok_or_else(invalid)?;
    let passages = fields
        .get("passages")
        .and_then(Value::as_array)
        .filter(|items| !items.is_empty())
        .ok_or_else(invalid)?;
    passages
        .iter()
        .map(|passage| {
            let passage = passage.as_object().ok_or_else(invalid)?;
            Ok(snapshot
                .iter()
                .chain(passage)
                .map(|(key, value)| (key.clone(), value.clone()))
                .collect())
        })
        .collect()
}
