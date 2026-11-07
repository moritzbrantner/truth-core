//! Advisory bridge candidates (#415): statements whose Lean vocabulary
//! overlaps a target's, ranked by exact Jaccard similarity over the
//! TruthCore constants their declarations mention.
//!
//! The ranking is a search heuristic. Shared constants are not evidence that
//! a candidate set entails the target, that two statements mean the same, or
//! that they share an interpretation (AGENTS.md invariants 6 and 16). Nothing
//! here writes corpus records.
use crate::{
    Corpus,
    kernels::{
        jaccard_similarity_sorted_unique, reachable, sorted_unique_intersection_count,
        sorted_unique_union,
    },
};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

/// Ranking limits. `top` candidates are kept per arity; pairs and triples are
/// formed from the best `pool` single candidates.
#[derive(Clone, Copy, Debug)]
pub struct Options {
    pub top: usize,
    pub pool: usize,
}

impl Default for Options {
    fn default() -> Self {
        Self { top: 5, pool: 12 }
    }
}

/// Reads the `scripts/StatementConstants.lean` export: an array of
/// `{declaration, constants: [..]}` objects.
pub fn parse_constants(value: &Value) -> Result<BTreeMap<String, Vec<String>>, String> {
    let rows = value
        .as_array()
        .ok_or("constants export must be a JSON array")?;
    let mut out = BTreeMap::new();
    for row in rows {
        let declaration = row["declaration"]
            .as_str()
            .ok_or("constants row without a declaration")?;
        if row.get("error").is_some() {
            continue;
        }
        let constants = row["constants"]
            .as_array()
            .ok_or_else(|| format!("{declaration}: constants must be an array"))?
            .iter()
            .map(|name| {
                name.as_str()
                    .map(str::to_owned)
                    .ok_or_else(|| format!("{declaration}: constant names must be strings"))
            })
            .collect::<Result<BTreeSet<_>, _>>()?;
        out.insert(declaration.to_owned(), constants.into_iter().collect());
    }
    Ok(out)
}

/// Statement IDs in queue order from `corpus.py thickness --queue --json`.
pub fn parse_queue(value: &Value) -> Result<Vec<String>, String> {
    value["queue"]
        .as_array()
        .ok_or("queue export must have a `queue` array")?
        .iter()
        .map(|entry| {
            entry["statement_id"]
                .as_str()
                .map(str::to_owned)
                .ok_or_else(|| "queue entry without statement_id".to_owned())
        })
        .collect()
}

struct Statement<'a> {
    declaration: &'a str,
    constants: Vec<u32>,
}

struct Index<'a> {
    names: Vec<&'a str>,
    statements: BTreeMap<&'a str, Statement<'a>>,
    /// premise -> conclusions and conclusion -> premises, over every argument.
    forward: BTreeMap<&'a str, BTreeSet<&'a str>>,
    backward: BTreeMap<&'a str, BTreeSet<&'a str>>,
    /// Symmetric `alternative_to`/`attacks` statement relations.
    rivals: BTreeMap<&'a str, BTreeSet<&'a str>>,
}

impl<'a> Index<'a> {
    fn new(corpus: &'a Corpus, constants: &'a BTreeMap<String, Vec<String>>) -> Self {
        let mut ids: BTreeMap<&str, u32> = BTreeMap::new();
        let mut names = Vec::new();
        let mut statements = BTreeMap::new();
        for (id, record) in corpus.records("statements") {
            let Some(declaration) = record
                .fields
                .get("lean_declaration")
                .and_then(Value::as_str)
            else {
                continue;
            };
            let Some(mentioned) = constants.get(declaration) else {
                continue;
            };
            let mut interned: Vec<u32> = mentioned
                .iter()
                .map(|name| {
                    *ids.entry(name.as_str()).or_insert_with(|| {
                        names.push(name.as_str());
                        names.len() as u32 - 1
                    })
                })
                .collect();
            interned.sort_unstable();
            interned.dedup();
            statements.insert(
                id,
                Statement {
                    declaration,
                    constants: interned,
                },
            );
        }
        let mut forward: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
        let mut backward: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
        for (_, argument) in corpus.records("arguments") {
            let Some(conclusion) = argument
                .fields
                .get("conclusion_statement_id")
                .and_then(Value::as_str)
            else {
                continue;
            };
            let premises = ["premise_statement_ids", "commitment_statement_ids"]
                .iter()
                .filter_map(|field| argument.fields.get(*field).and_then(Value::as_array))
                .flatten()
                .filter_map(Value::as_str);
            for premise in premises {
                forward.entry(premise).or_default().insert(conclusion);
                backward.entry(conclusion).or_default().insert(premise);
            }
        }
        let mut rivals: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
        for (_, relation) in corpus.records("relations") {
            let field = |name| relation.fields.get(name).and_then(Value::as_str);
            if matches!(field("predicate"), Some("alternative_to" | "attacks"))
                && field("subject_kind") == Some("statement")
                && field("object_kind") == Some("statement")
                && let (Some(subject), Some(object)) = (field("subject_id"), field("object_id"))
            {
                rivals.entry(subject).or_default().insert(object);
                rivals.entry(object).or_default().insert(subject);
            }
        }
        Self {
            names,
            statements,
            forward,
            backward,
            rivals,
        }
    }

    fn ancestors(&self, id: &'a str) -> BTreeSet<&'a str> {
        reachable(id, |node| {
            self.backward.get(node).into_iter().flatten().copied()
        })
    }

    fn descendants(&self, id: &'a str) -> BTreeSet<&'a str> {
        reachable(id, |node| {
            self.forward.get(node).into_iter().flatten().copied()
        })
    }

    fn names(&self, constants: &[u32]) -> Vec<&'a str> {
        constants.iter().map(|&c| self.names[c as usize]).collect()
    }
}

struct Scored<'a> {
    members: Vec<&'a str>,
    union: Vec<u32>,
    /// Target constants the members mention between them.
    covered: usize,
    score: f64,
}

impl<'a> Scored<'a> {
    fn new(members: Vec<&'a str>, union: Vec<u32>, goal: &[u32]) -> Self {
        Self {
            covered: sorted_unique_intersection_count(&union, goal),
            score: jaccard_similarity_sorted_unique(&union, goal),
            members,
            union,
        }
    }
}

/// Singles rank by Jaccard similarity.
fn by_similarity(left: &Scored, right: &Scored) -> std::cmp::Ordering {
    right
        .score
        .total_cmp(&left.score)
        .then_with(|| left.members.cmp(&right.members))
}

/// Combinations rank by target coverage first: extra vocabulary in a second
/// premise lowers Jaccard even when it supplies a missing target constant.
fn by_coverage(left: &Scored, right: &Scored) -> std::cmp::Ordering {
    right
        .covered
        .cmp(&left.covered)
        .then_with(|| by_similarity(left, right))
}

fn combine<'a>(parts: &[&Scored<'a>], goal: &[u32]) -> Scored<'a> {
    let members = parts.iter().map(|part| part.members[0]).collect();
    let union = parts.iter().fold(Vec::new(), |acc, part| {
        sorted_unique_union(&acc, &part.union)
    });
    Scored::new(members, union, goal)
}

/// Ranks single, pair and triple candidate premise sets for each target.
pub fn report(
    corpus: &Corpus,
    constants: &BTreeMap<String, Vec<String>>,
    targets: &[String],
    options: Options,
) -> Result<Value, String> {
    let index = Index::new(corpus, constants);
    let known: BTreeSet<&str> = corpus.records("statements").map(|(id, _)| id).collect();
    let mut rows = Vec::new();
    for target in targets {
        let target = known
            .get(target.as_str())
            .copied()
            .ok_or_else(|| format!("unknown statement {target}"))?;
        rows.push(target_report(&index, target, options));
    }
    Ok(json!({
        "mode": "advisory vocabulary ranking; NOT a proof, equivalence or fidelity judgment",
        "similarity": "exact Jaccard over sorted-unique TruthCore constants mentioned by each lean_declaration (type and stored body, not unfolded); pairs and triples rank by covered target constants, then Jaccard, and need every member to cover a target constant the others lack",
        "exclusions": "the target itself, statements sharing its declaration, statements already reaching it or reached from it through recorded arguments, its alternative_to/attacks rivals, and combinations whose members are already connected",
        "options": {"top": options.top, "pool": options.pool},
        "targets": rows,
    }))
}

fn target_report<'a>(index: &Index<'a>, target: &'a str, options: Options) -> Value {
    let Some(goal) = index.statements.get(target) else {
        return json!({"statement_id": target,
            "skipped": "no lean_declaration with exported constants"});
    };
    let ancestors = index.ancestors(target);
    let descendants = index.descendants(target);
    let rivals = index.rivals.get(target);
    let mut excluded: BTreeMap<&str, usize> = BTreeMap::new();
    let mut singles = Vec::new();
    for (&id, statement) in &index.statements {
        let reason = if id == target {
            continue;
        } else if statement.declaration == goal.declaration {
            Some("same_declaration")
        } else if ancestors.contains(id) {
            Some("already_derives_target")
        } else if descendants.contains(id) {
            Some("derived_from_target")
        } else if rivals.is_some_and(|rivals| rivals.contains(id)) {
            Some("rival_of_target")
        } else {
            None
        };
        if let Some(reason) = reason {
            *excluded.entry(reason).or_default() += 1;
            continue;
        }
        let single = Scored::new(vec![id], statement.constants.clone(), &goal.constants);
        if single.covered > 0 {
            singles.push(single);
        }
    }
    singles.sort_by(by_similarity);
    let pool: Vec<&Scored> = singles.iter().take(options.pool).collect();
    let connected: BTreeMap<&str, BTreeSet<&str>> = pool
        .iter()
        .map(|single| (single.members[0], index.ancestors(single.members[0])))
        .collect();
    let linked = |a: &str, b: &str| connected[a].contains(b) || connected[b].contains(a);
    let (mut pairs, mut triples) = (Vec::new(), Vec::new());
    for (i, a) in pool.iter().enumerate() {
        for (j, b) in pool.iter().enumerate().skip(i + 1) {
            if linked(a.members[0], b.members[0]) {
                *excluded.entry("pair_already_connected").or_default() += 1;
                continue;
            }
            let pair = combine(&[a, b], &goal.constants);
            // Each member must cover a target constant the other lacks.
            if pair.covered > a.covered.max(b.covered) {
                pairs.push(pair);
            }
            for c in pool.iter().skip(j + 1) {
                if linked(a.members[0], c.members[0]) || linked(b.members[0], c.members[0]) {
                    continue;
                }
                let triple = combine(&[a, b, c], &goal.constants);
                let best_pair = [[*a, *b], [*a, *c], [*b, *c]]
                    .iter()
                    .map(|parts| combine(parts, &goal.constants).covered)
                    .max()
                    .unwrap_or(0);
                if triple.covered > best_pair {
                    triples.push(triple);
                }
            }
        }
    }
    pairs.sort_by(by_coverage);
    triples.sort_by(by_coverage);
    let render = |scored: &[Scored]| -> Vec<Value> {
        scored
            .iter()
            .take(options.top)
            .map(|candidate| {
                let shared: Vec<u32> = candidate
                    .union
                    .iter()
                    .copied()
                    .filter(|c| goal.constants.binary_search(c).is_ok())
                    .collect();
                let missing: Vec<u32> = goal
                    .constants
                    .iter()
                    .copied()
                    .filter(|c| candidate.union.binary_search(c).is_err())
                    .collect();
                json!({
                    "statement_ids": candidate.members,
                    "lean_declarations": candidate.members.iter()
                        .map(|id| index.statements[id].declaration).collect::<Vec<_>>(),
                    "score": (candidate.score * 10_000.0).round() / 10_000.0,
                    "covered_target_constants": candidate.covered,
                    "shared_constants": index.names(&shared),
                    "missing_target_constants": index.names(&missing),
                })
            })
            .collect()
    };
    json!({
        "statement_id": target,
        "lean_declaration": goal.declaration,
        "constants": index.names(&goal.constants),
        "singles": render(&singles),
        "pairs": render(&pairs),
        "triples": render(&triples),
        "excluded": excluded,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn fixture() -> (tempfile_dir::Dir, Corpus) {
        let dir = tempfile_dir::Dir::new();
        let statements = dir.path.join("corpus/statements");
        let arguments = dir.path.join("corpus/arguments");
        fs::create_dir_all(&statements).unwrap();
        fs::create_dir_all(&arguments).unwrap();
        for (id, decl) in [
            ("STMT-T", "N.T"),
            ("STMT-A", "N.A"),
            ("STMT-B", "N.B"),
            ("STMT-LINKED", "N.L"),
            ("STMT-ALIAS", "N.T"),
            ("STMT-NONE", "N.Z"),
            ("STMT-RIVAL", "N.R"),
        ] {
            fs::write(
                statements.join(format!("{id}.json")),
                json!({"id": id, "paraphrase": id, "lean_declaration": decl}).to_string(),
            )
            .unwrap();
        }
        fs::write(
            arguments.join("ARG.json"),
            json!({"id": "ARG", "premise_statement_ids": ["STMT-LINKED"],
                   "conclusion_statement_id": "STMT-T", "meaning": "fixture",
                   "inference_ids": ["INF"]})
            .to_string(),
        )
        .unwrap();
        let relations = dir.path.join("corpus/relations");
        fs::create_dir_all(&relations).unwrap();
        fs::write(
            relations.join("REL.json"),
            json!({"id": "REL", "subject_kind": "statement", "subject_id": "STMT-RIVAL",
                   "predicate": "alternative_to", "object_kind": "statement",
                   "object_id": "STMT-T"})
            .to_string(),
        )
        .unwrap();
        let corpus = Corpus::load(&dir.path).unwrap();
        (dir, corpus)
    }

    fn constants() -> BTreeMap<String, Vec<String>> {
        parse_constants(&json!([
            {"declaration": "N.T", "constants": ["N.P", "N.Q", "N.T"]},
            {"declaration": "N.A", "constants": ["N.A", "N.P"]},
            {"declaration": "N.B", "constants": ["N.B", "N.Q"]},
            {"declaration": "N.L", "constants": ["N.L", "N.P", "N.Q"]},
            {"declaration": "N.Z", "constants": ["N.Z"]},
            {"declaration": "N.R", "constants": ["N.R", "N.T"]},
        ]))
        .unwrap()
    }

    #[test]
    fn ranks_pairs_and_excludes_connected_and_aliases() {
        let (_dir, corpus) = fixture();
        let report = report(
            &corpus,
            &constants(),
            &["STMT-T".into()],
            Options::default(),
        )
        .unwrap();
        let target = &report["targets"][0];
        let singles: Vec<_> = target["singles"]
            .as_array()
            .unwrap()
            .iter()
            .map(|c| c["statement_ids"][0].as_str().unwrap())
            .collect();
        // STMT-LINKED already derives the target, STMT-ALIAS shares its
        // declaration, STMT-RIVAL is a recorded alternative and STMT-NONE
        // shares nothing.
        assert_eq!(singles, ["STMT-A", "STMT-B"]);
        assert_eq!(target["excluded"]["already_derives_target"], 1);
        assert_eq!(target["excluded"]["same_declaration"], 1);
        assert_eq!(target["excluded"]["rival_of_target"], 1);
        assert_eq!(
            target["pairs"][0]["statement_ids"],
            json!(["STMT-A", "STMT-B"])
        );
        assert_eq!(target["pairs"][0]["score"], 0.4);
        assert_eq!(
            target["pairs"][0]["missing_target_constants"],
            json!(["N.T"])
        );
        assert!(target["triples"].as_array().unwrap().is_empty());
    }

    #[test]
    fn unknown_targets_and_missing_vocabulary() {
        let (_dir, corpus) = fixture();
        assert!(
            report(
                &corpus,
                &constants(),
                &["STMT-X".into()],
                Options::default()
            )
            .is_err()
        );
        let skipped = report(
            &corpus,
            &BTreeMap::new(),
            &["STMT-T".into()],
            Options::default(),
        )
        .unwrap();
        assert!(skipped["targets"][0]["skipped"].is_string());
        assert_eq!(
            parse_queue(&json!({"queue": [{"statement_id": "STMT-T"}]})).unwrap(),
            ["STMT-T"]
        );
    }

    /// Minimal self-cleaning temporary directory (no extra dev-dependency).
    mod tempfile_dir {
        pub struct Dir {
            pub path: std::path::PathBuf,
        }
        impl Dir {
            pub fn new() -> Self {
                use std::sync::atomic::{AtomicU32, Ordering};
                static NEXT: AtomicU32 = AtomicU32::new(0);
                let path = std::env::temp_dir().join(format!(
                    "truth-bridges-{}-{}",
                    std::process::id(),
                    NEXT.fetch_add(1, Ordering::Relaxed)
                ));
                std::fs::create_dir_all(&path).unwrap();
                Self { path }
            }
        }
        impl Drop for Dir {
            fn drop(&mut self) {
                let _ = std::fs::remove_dir_all(&self.path);
            }
        }
    }
}
