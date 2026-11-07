//! Disconnected verified work: verified results whose argument conclusion
//! does not reach the frontier root.
//!
//! `thickness --queue` ranks only statements that already reach the root, so
//! a whole verified family can stay invisible to round selection. This report
//! lists such results grouped by Lean module area (or by argument family) and,
//! for each group, names root-path statements it shares Lean imports,
//! vocabulary modules, definitions or paraphrase words with.
//!
//! Contacts are discovery leads, not equivalences or entailments (AGENTS.md
//! invariants 6 and 16). Nothing here closes a statement, changes a route
//! cost or writes a record; `scripts/corpus.py frontier` stays the closure
//! authority. Reaching the root uses the same route-aware walk as
//! `thickness` (`thickness::frontier_inputs`).
use crate::{
    Corpus,
    thickness::{self, FrontierInputs, Records},
};
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fs,
    path::Path,
};

type Record = Map<String, Value>;

/// Contacts reported per group.
const CONTACT_LIMIT: usize = 5;
/// A statement shared by more disconnected arguments than this is a hub and
/// does not join argument families.
const FAMILY_HUB_LIMIT: usize = 8;
/// Conclusions listed per group in text output (`--json` lists all).
const TEXT_CONCLUSION_LIMIT: usize = 8;
/// A vocabulary module imported by more than this share of results is too
/// common to count as a shared-vocabulary contact.
const COMMON_MODULE_SHARE: f64 = 0.05;
const STOP_WORDS: &str = "a an the is are of to and or in for that this its it with by from as not every all some only has have be being";

/// How results are grouped.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GroupBy {
    /// Lean module area: `TruthCore.Results.Modal.K.Solution` -> `TruthCore.Modal`.
    Module,
    /// Weakly connected components of the disconnected arguments' statements.
    Family,
}

impl GroupBy {
    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "module" => Some(Self::Module),
            "family" => Some(Self::Family),
            _ => None,
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Module => "module",
            Self::Family => "family",
        }
    }
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

/// The area of a Lean module: the first namespace component below
/// `TruthCore` (after `Results`, when present).
pub fn module_area(module: &str) -> String {
    let parts: Vec<&str> = module.split('.').collect();
    match parts.as_slice() {
        ["TruthCore", "Results", area, ..] | ["TruthCore", area, ..] => {
            format!("TruthCore.{area}")
        }
        [] | [""] => "(no module)".into(),
        [first, ..] => (*first).to_owned(),
    }
}

/// Lean module reads, cached per module.
struct Lean<'p> {
    checkout: &'p Path,
    imports: HashMap<String, Vec<String>>,
    declaration_modules: HashMap<String, Option<String>>,
}

impl<'p> Lean<'p> {
    fn new(checkout: &'p Path) -> Self {
        Self {
            checkout,
            imports: HashMap::new(),
            declaration_modules: HashMap::new(),
        }
    }

    fn file(&self, module: &str) -> std::path::PathBuf {
        self.checkout
            .join(format!("{}.lean", module.replace('.', "/")))
    }

    /// Direct imports of a module, without toolchain and aggregator modules.
    fn imports(&mut self, module: &str) -> &[String] {
        if !self.imports.contains_key(module) {
            let source = fs::read_to_string(self.file(module)).unwrap_or_default();
            let mut found = Vec::new();
            for line in source.lines() {
                let line = line.trim();
                let rest = [
                    "public meta import ",
                    "public import ",
                    "meta import ",
                    "import ",
                ]
                .iter()
                .find_map(|prefix| line.strip_prefix(prefix));
                let Some(rest) = rest else { continue };
                for name in rest.split_whitespace() {
                    if name.starts_with("TruthCore.") && !name.starts_with("TruthCore.Imports.") {
                        found.push(name.to_owned());
                    }
                }
            }
            found.sort();
            found.dedup();
            self.imports.insert(module.to_owned(), found);
        }
        &self.imports[module]
    }

    /// The longest proper prefix of a declaration name that is a module file.
    fn declaration_module(&mut self, declaration: &str) -> Option<String> {
        if let Some(found) = self.declaration_modules.get(declaration) {
            return found.clone();
        }
        let parts: Vec<&str> = declaration.split('.').collect();
        let found = (2..parts.len())
            .rev()
            .map(|length| parts[..length].join("."))
            .find(|module| self.file(module).is_file());
        self.declaration_modules
            .insert(declaration.to_owned(), found.clone());
        found
    }
}

struct Orphan<'a> {
    result: &'a Record,
    argument: &'a Record,
    transcription: Option<String>,
    /// A premise, commitment or argument relation touches the root path.
    touches: Vec<String>,
}

fn words(value: &str) -> BTreeSet<String> {
    let stop: BTreeSet<&str> = STOP_WORDS.split(' ').collect();
    let lower = value.to_lowercase();
    let mut found = BTreeSet::new();
    let mut current = String::new();
    for c in lower.chars().chain(std::iter::once(' ')) {
        if c.is_ascii_lowercase() || (c.is_ascii_digit() && !current.is_empty()) {
            current.push(c);
        } else {
            if current.len() >= 2 && !stop.contains(current.as_str()) {
                found.insert(current.clone());
            }
            current.clear();
        }
    }
    found
}

struct Contact {
    statement: String,
    tier: u8,
    score: f64,
    reasons: Vec<Value>,
}

/// The report. `checkout` is read for Solution imports, declaration modules
/// and the transcription heuristics.
pub fn report(checkout: &Path, corpus: &Corpus, root: &str, by: GroupBy) -> Value {
    let records = Records::from_corpus(corpus);
    let flags = crate::frontier::transcription_flags(checkout, &records);
    let frontier = thickness::frontier_inputs(root, &records, &flags);
    build(checkout, &records, &frontier, by)
}

fn build(checkout: &Path, records: &Records, frontier: &FrontierInputs, by: GroupBy) -> Value {
    let reaching = &frontier.reaching_root;
    let statements: BTreeMap<&str, &Record> = records
        .statements
        .iter()
        .map(|statement| (text(statement, "id"), *statement))
        .collect();
    let arguments: HashMap<&str, &Record> = records
        .arguments
        .iter()
        .map(|argument| (text(argument, "id"), *argument))
        .collect();
    let mut rivals: HashMap<&str, BTreeSet<&str>> = HashMap::new();
    let mut argument_relations: HashMap<&str, Vec<&Record>> = HashMap::new();
    for relation in &records.relations {
        let (subject, object) = (text(relation, "subject_id"), text(relation, "object_id"));
        if matches!(text(relation, "predicate"), "alternative_to" | "attacks")
            && text(relation, "subject_kind") == "statement"
            && text(relation, "object_kind") == "statement"
        {
            rivals.entry(subject).or_default().insert(object);
            rivals.entry(object).or_default().insert(subject);
        }
        if text(relation, "subject_kind") == "argument" {
            argument_relations
                .entry(subject)
                .or_default()
                .push(relation);
        }
    }
    let on_path = |statement: &str| reaching.contains(statement);
    let rival_of_path = |statement: &str| {
        rivals
            .get(statement)
            .is_some_and(|set| set.iter().any(|rival| on_path(rival)))
    };

    let verified: Vec<(&Record, &Record)> = records
        .results
        .iter()
        .filter(|result| matches!(text(result, "status"), "solution-present" | "verified"))
        .filter_map(|result| {
            arguments
                .get(text(result, "argument_id"))
                .map(|argument| (*result, *argument))
        })
        .collect();
    let mut connected = 0usize;
    let mut orphans: Vec<Orphan> = Vec::new();
    for (result, argument) in &verified {
        if on_path(text(argument, "conclusion_statement_id")) {
            connected += 1;
            continue;
        }
        let mut touches: Vec<String> = list(argument, "premise_statement_ids")
            .into_iter()
            .chain(list(argument, "commitment_statement_ids"))
            .filter(|premise| on_path(premise))
            .map(|premise| format!("premise {premise}"))
            .collect();
        for relation in argument_relations
            .get(text(argument, "id"))
            .into_iter()
            .flatten()
        {
            let object = text(relation, "object_id");
            if on_path(object) || rival_of_path(object) {
                touches.push(format!("{} {object}", text(relation, "predicate")));
            }
        }
        touches.sort();
        touches.dedup();
        orphans.push(Orphan {
            result,
            argument,
            transcription: frontier
                .transcription_results
                .get(text(result, "id"))
                .map(|kind| kind.kind.clone()),
            touches,
        });
    }

    let mut lean = Lean::new(checkout);
    let groups = group(&orphans, by);

    // Root-path vocabulary: declaration modules of root-path statements and
    // the Solution modules (and imports) of results concluding them.
    let mut path_modules: BTreeMap<&str, BTreeSet<String>> = BTreeMap::new();
    let mut solution_concludes: HashMap<String, Vec<(&str, &str)>> = HashMap::new();
    let mut import_users: HashMap<String, Vec<(&str, &str)>> = HashMap::new();
    let mut module_frequency: HashMap<String, usize> = HashMap::new();
    for statement in reaching {
        let Some(record) = statements.get(statement.as_str()) else {
            continue;
        };
        let declaration = text(record, "lean_declaration");
        if !declaration.is_empty()
            && let Some(module) = lean.declaration_module(declaration)
        {
            path_modules
                .entry(text(record, "id"))
                .or_default()
                .insert(module);
        }
    }
    for (result, argument) in &verified {
        let module = text(result, "solution_module").to_owned();
        let imports = lean.imports(&module).to_vec();
        for import in &imports {
            *module_frequency.entry(import.clone()).or_default() += 1;
        }
        let conclusion = text(argument, "conclusion_statement_id");
        let Some((statement, _)) = statements.get_key_value(conclusion) else {
            continue;
        };
        if !on_path(conclusion) {
            continue;
        }
        let id = text(result, "id");
        solution_concludes
            .entry(module.clone())
            .or_default()
            .push((statement, id));
        for import in imports {
            import_users
                .entry(import)
                .or_default()
                .push((statement, id));
        }
    }
    let common = (verified.len() as f64 * COMMON_MODULE_SHARE).max(3.0);
    let rare = |module: &str| (module_frequency.get(module).copied().unwrap_or(0) as f64) <= common;

    let tokens: BTreeMap<&str, BTreeSet<String>> = statements
        .iter()
        .map(|(id, record)| (*id, words(text(record, "paraphrase"))))
        .collect();
    let mut document_frequency: HashMap<&str, usize> = HashMap::new();
    for group in tokens.values() {
        for word in group {
            *document_frequency.entry(word.as_str()).or_default() += 1;
        }
    }
    let idf = |word: &str| {
        (1.0 + tokens.len() as f64 / document_frequency.get(word).copied().unwrap_or(1) as f64).ln()
    };

    let mut output_groups = Vec::new();
    for (key, members) in groups {
        let mut conclusions: BTreeSet<&str> = BTreeSet::new();
        let mut solutions: BTreeSet<String> = BTreeSet::new();
        let mut vocabulary: BTreeSet<String> = BTreeSet::new();
        let mut definitions: BTreeSet<&str> = BTreeSet::new();
        let mut group_words: BTreeSet<String> = BTreeSet::new();
        let mut transcriptions = 0usize;
        let mut touching = 0usize;
        let mut results = Vec::new();
        for orphan in &members {
            let conclusion = text(orphan.argument, "conclusion_statement_id");
            conclusions.insert(conclusion);
            let solution = text(orphan.result, "solution_module").to_owned();
            vocabulary.extend(lean.imports(&solution).iter().cloned());
            solutions.insert(solution);
            if let Some(statement) = statements.get(conclusion) {
                definitions.extend(list(statement, "definition_ids"));
                definitions.extend(list(statement, "disambiguation_ids"));
                let declaration = text(statement, "lean_declaration");
                if !declaration.is_empty()
                    && let Some(module) = lean.declaration_module(declaration)
                {
                    vocabulary.insert(module);
                }
                if let Some(found) = tokens.get(conclusion) {
                    group_words.extend(found.iter().cloned());
                }
            }
            transcriptions += usize::from(orphan.transcription.is_some());
            touching += usize::from(!orphan.touches.is_empty());
            results.push(json!({
                "result_id": text(orphan.result, "id"),
                "argument_id": text(orphan.argument, "id"),
                "conclusion_statement_id": conclusion,
                "solution_module": text(orphan.result, "solution_module"),
                "transcription": orphan.transcription,
                "touches_root_path": orphan.touches,
            }));
        }

        let mut contacts: BTreeMap<String, Contact> = BTreeMap::new();
        let mut add = |statement: &str, tier: u8, score: f64, reason: Value| {
            let entry = contacts.entry(statement.to_owned()).or_insert(Contact {
                statement: statement.to_owned(),
                tier,
                score: 0.0,
                reasons: Vec::new(),
            });
            entry.tier = entry.tier.min(tier);
            if !entry.reasons.contains(&reason) {
                entry.score += score;
                entry.reasons.push(reason);
            }
        };
        // Tier 0: Lean import reuse across the corpus boundary.
        for solution in &solutions {
            for (statement, result) in import_users.get(solution).into_iter().flatten() {
                add(
                    statement,
                    0,
                    1.0,
                    json!({"kind": "root_path_result_imports_group_solution",
                           "result_id": result, "module": solution}),
                );
            }
            for import in lean.imports(solution).to_vec() {
                for (statement, result) in solution_concludes.get(&import).into_iter().flatten() {
                    add(
                        statement,
                        0,
                        1.0,
                        json!({"kind": "group_solution_imports_root_path_result",
                               "result_id": result, "module": import}),
                    );
                }
            }
        }
        for (statement, modules) in &path_modules {
            // Tier 1: shared vocabulary module.
            let shared: Vec<&String> = modules
                .iter()
                .filter(|module| vocabulary.contains(*module) && rare(module))
                .collect();
            if !shared.is_empty() {
                add(
                    statement,
                    1,
                    shared.len() as f64,
                    json!({"kind": "shared_vocabulary_module", "modules": shared}),
                );
            }
        }
        for statement in reaching {
            let Some(record) = statements.get(statement.as_str()) else {
                continue;
            };
            // Tier 2: shared definitions or disambiguations.
            let shared: Vec<&str> = list(record, "definition_ids")
                .into_iter()
                .chain(list(record, "disambiguation_ids"))
                .filter(|id| definitions.contains(id))
                .collect();
            if !shared.is_empty() {
                add(
                    statement,
                    2,
                    shared.len() as f64,
                    json!({"kind": "shared_definitions", "ids": shared}),
                );
            }
            // Tier 3: weighted paraphrase overlap.
            let overlap: Vec<&String> = tokens
                .get(statement.as_str())
                .into_iter()
                .flatten()
                .filter(|word| group_words.contains(*word))
                .collect();
            if overlap.len() >= 2 {
                let score = overlap.iter().map(|word| idf(word)).sum::<f64>();
                add(
                    statement,
                    3,
                    score / 100.0,
                    json!({"kind": "text_overlap", "words": overlap}),
                );
            }
        }
        let mut ranked: Vec<Contact> = contacts.into_values().collect();
        ranked.sort_by(|left, right| {
            left.tier
                .cmp(&right.tier)
                .then(right.score.total_cmp(&left.score))
                .then(left.statement.cmp(&right.statement))
        });
        let contacts: Vec<Value> = ranked
            .into_iter()
            .take(CONTACT_LIMIT)
            .map(|contact| {
                json!({
                    "statement_id": contact.statement,
                    "tier": contact.tier,
                    "paraphrase": statements.get(contact.statement.as_str())
                        .map(|record| text(record, "paraphrase")).unwrap_or_default(),
                    "reasons": contact.reasons,
                })
            })
            .collect();
        output_groups.push(json!({
            "group": key,
            "result_count": members.len(),
            "non_transcription_count": members.len() - transcriptions,
            "transcription_count": transcriptions,
            "touching_root_path_count": touching,
            "conclusion_statement_ids": conclusions,
            "results": results,
            "contacts": contacts,
        }));
    }
    output_groups.sort_by(|left, right| {
        right["result_count"]
            .as_u64()
            .cmp(&left["result_count"].as_u64())
            .then(left["group"].as_str().cmp(&right["group"].as_str()))
    });
    let transcriptions = orphans
        .iter()
        .filter(|orphan| orphan.transcription.is_some())
        .count();
    json!({
        "root": frontier.root,
        "by": by.name(),
        "mode": "discovery, not certification",
        "verified_result_count": verified.len(),
        "connected_result_count": connected,
        "disconnected_result_count": orphans.len(),
        "disconnected_non_transcription_count": orphans.len() - transcriptions,
        "disconnected_transcription_count": transcriptions,
        "reaching_root_statement_count": reaching.len(),
        "groups": output_groups,
        "scope": "Contacts are advisory leads (Lean import reuse, shared vocabulary modules, shared definitions, paraphrase overlap); no equivalence, entailment or closure is inferred.",
    })
}

/// Groups disconnected results by module area or by argument family.
fn group<'o, 'a>(orphans: &'o [Orphan<'a>], by: GroupBy) -> BTreeMap<String, Vec<&'o Orphan<'a>>> {
    let mut groups: BTreeMap<String, Vec<&Orphan>> = BTreeMap::new();
    match by {
        GroupBy::Module => {
            for orphan in orphans {
                groups
                    .entry(module_area(text(orphan.result, "solution_module")))
                    .or_default()
                    .push(orphan);
            }
        }
        GroupBy::Family => {
            // Union-find over statements joined by a disconnected argument.
            // Hub statements (shared by more than FAMILY_HUB_LIMIT arguments,
            // such as STMT-CONFIGURATION-FALSE) do not join families.
            let nodes_of = |orphan: &Orphan<'a>| -> Vec<&'a str> {
                list(orphan.argument, "premise_statement_ids")
                    .into_iter()
                    .chain(list(orphan.argument, "commitment_statement_ids"))
                    .chain([text(orphan.argument, "conclusion_statement_id")])
                    .collect()
            };
            let mut degree: HashMap<&str, usize> = HashMap::new();
            for orphan in orphans {
                let mut nodes = nodes_of(orphan);
                nodes.sort_unstable();
                nodes.dedup();
                for node in nodes {
                    *degree.entry(node).or_default() += 1;
                }
            }
            let mut parent: HashMap<&str, &str> = HashMap::new();
            fn find<'s>(parent: &mut HashMap<&'s str, &'s str>, node: &'s str) -> &'s str {
                let mut current = node;
                while let Some(&next) = parent.get(current) {
                    if next == current {
                        break;
                    }
                    current = next;
                }
                parent.insert(node, current);
                current
            }
            let joining = |orphan: &Orphan<'a>| -> Vec<&'a str> {
                nodes_of(orphan)
                    .into_iter()
                    .filter(|node| degree[node] <= FAMILY_HUB_LIMIT)
                    .collect()
            };
            for orphan in orphans {
                let nodes = joining(orphan);
                for node in &nodes {
                    parent.entry(node).or_insert(node);
                }
                for pair in nodes.windows(2) {
                    let (left, right) = (find(&mut parent, pair[0]), find(&mut parent, pair[1]));
                    if left != right {
                        let (low, high) = if left < right {
                            (left, right)
                        } else {
                            (right, left)
                        };
                        parent.insert(high, low);
                    }
                }
            }
            let mut members: BTreeMap<&str, Vec<&Orphan>> = BTreeMap::new();
            for orphan in orphans {
                let representative = match joining(orphan).first() {
                    Some(node) => find(&mut parent, node),
                    None => text(orphan.argument, "conclusion_statement_id"),
                };
                members.entry(representative).or_default().push(orphan);
            }
            for (representative, family) in members {
                let mut areas: BTreeMap<String, usize> = BTreeMap::new();
                for orphan in &family {
                    *areas
                        .entry(module_area(text(orphan.result, "solution_module")))
                        .or_default() += 1;
                }
                let area = areas
                    .iter()
                    .max_by(|left, right| left.1.cmp(right.1).then(right.0.cmp(left.0)))
                    .map(|(area, _)| area.clone())
                    .unwrap_or_default();
                groups.insert(format!("{area} family of {representative}"), family);
            }
        }
    }
    groups
}

/// Statement ID suffixes recognized as a coverage or exclusivity statement
/// when a disambiguation does not name one in its fork fields.
const COVERAGE_SUFFIXES: &[&str] = &["-SENSES-EXHAUSTIVE"];
const EXCLUSIVITY_SUFFIXES: &[&str] = &["-SENSE-UNIQUE", "-SENSES-EXCLUSIVE"];

/// Root-path disambiguations without a certified sense fork.
///
/// A fork needs three parts (docs/corpus-model.md, "Sense forks"): a
/// coverage statement (the listed senses are all the relevant ones), an
/// exclusivity statement (exactly one sense applies to the use) and a
/// verified joint theorem by cases over the sense enum that takes the
/// coverage statement as a premise. Each part is read from the optional
/// disambiguation fields `coverage_statement_id`, `exclusivity_statement_id`
/// and `fork_result_ids` (validated by `corpus.py check`); when a field is
/// absent, a statement linking the disambiguation whose ID ends in
/// `-SENSES-EXHAUSTIVE` (coverage) or `-SENSE-UNIQUE`/`-SENSES-EXCLUSIVE`
/// (exclusivity), and a verified result whose argument links the
/// disambiguation and takes that coverage statement as a premise, are
/// accepted as a heuristic fallback. A disambiguation is on a root path when
/// a statement reaching the root, or an argument concluding one, links it
/// or one of its sense definitions.
pub fn sense_report(checkout: &Path, corpus: &Corpus, root: &str) -> Value {
    let records = Records::from_corpus(corpus);
    let flags = crate::frontier::transcription_flags(checkout, &records);
    let frontier = thickness::frontier_inputs(root, &records, &flags);
    let reaching = &frontier.reaching_root;
    let statements: HashMap<&str, &Record> = records
        .statements
        .iter()
        .map(|statement| (text(statement, "id"), *statement))
        .collect();
    let arguments: HashMap<&str, &Record> = records
        .arguments
        .iter()
        .map(|argument| (text(argument, "id"), *argument))
        .collect();
    let verified: BTreeMap<&str, &Record> = records
        .results
        .iter()
        .filter(|result| matches!(text(result, "status"), "solution-present" | "verified"))
        .map(|result| (text(result, "id"), *result))
        .collect();
    let mut linkers: Vec<(&str, &str, &Record)> = reaching
        .iter()
        .filter_map(|id| {
            statements
                .get(id.as_str())
                .map(|record| ("statement", text(record, "id"), *record))
        })
        .collect();
    linkers.extend(
        records
            .arguments
            .iter()
            .filter(|argument| reaching.contains(text(argument, "conclusion_statement_id")))
            .map(|argument| ("argument", text(argument, "id"), *argument)),
    );
    let mut linking_statements: HashMap<&str, Vec<&str>> = HashMap::new();
    for statement in &records.statements {
        for disambiguation in list(statement, "disambiguation_ids") {
            linking_statements
                .entry(disambiguation)
                .or_default()
                .push(text(statement, "id"));
        }
    }
    let links_result = |result: &Record, id: &str| {
        list(result, "disambiguation_ids").contains(&id)
            || arguments
                .get(text(result, "argument_id"))
                .is_some_and(|argument| list(argument, "disambiguation_ids").contains(&id))
    };

    let mut disambiguations: Vec<&Record> = corpus.records("disambiguations");
    disambiguations.sort_by_key(|record| text(record, "id"));
    let mut entries = Vec::new();
    let mut forked = Vec::new();
    for disambiguation in disambiguations {
        let id = text(disambiguation, "id");
        let senses = list(disambiguation, "sense_definition_ids");
        if senses.len() < 2 {
            continue;
        }
        let linked: Vec<String> = linkers
            .iter()
            .filter(|(_, _, record)| {
                list(record, "disambiguation_ids").contains(&id)
                    || list(record, "definition_ids")
                        .iter()
                        .any(|definition| senses.contains(definition))
            })
            .map(|(kind, linker, _)| format!("{kind} {linker}"))
            .collect();
        if linked.is_empty() {
            continue;
        }
        let by_suffix = |suffixes: &[&str]| {
            linking_statements
                .get(id)
                .into_iter()
                .flatten()
                .find(|statement| suffixes.iter().any(|suffix| statement.ends_with(suffix)))
                .map(|statement| (*statement).to_owned())
        };
        let field = |name: &str| {
            disambiguation
                .get(name)
                .and_then(Value::as_str)
                .filter(|value| statements.contains_key(value))
                .map(str::to_owned)
        };
        let coverage = field("coverage_statement_id").or_else(|| by_suffix(COVERAGE_SUFFIXES));
        let exclusivity =
            field("exclusivity_statement_id").or_else(|| by_suffix(EXCLUSIVITY_SUFFIXES));
        let declared = list(disambiguation, "fork_result_ids");
        let joint: Vec<&str> = match &coverage {
            None => Vec::new(),
            Some(coverage) => verified
                .iter()
                .filter(|(result_id, result)| {
                    (declared.is_empty() || declared.contains(result_id))
                        && links_result(result, id)
                        && arguments
                            .get(text(result, "argument_id"))
                            .is_some_and(|argument| {
                                list(argument, "premise_statement_ids").contains(&coverage.as_str())
                            })
                })
                .map(|(result_id, _)| *result_id)
                .collect(),
        };
        let mut missing = Vec::new();
        if coverage.is_none() {
            missing.push("coverage");
        }
        if exclusivity.is_none() {
            missing.push("exclusivity");
        }
        if joint.is_empty() {
            missing.push("joint_theorem");
        }
        if missing.is_empty() {
            forked.push(id);
            continue;
        }
        entries.push(json!({
            "disambiguation_id": id,
            "term": text(disambiguation, "term"),
            "sense_count": senses.len(),
            "senses": senses,
            "missing": missing,
            "coverage_statement_id": coverage,
            "exclusivity_statement_id": exclusivity,
            "fork_result_ids": joint,
            "root_path_link_count": linked.len(),
            "root_path_links": linked,
        }));
    }
    entries.sort_by(|left, right| {
        right["root_path_link_count"]
            .as_u64()
            .cmp(&left["root_path_link_count"].as_u64())
            .then(
                right["sense_count"]
                    .as_u64()
                    .cmp(&left["sense_count"].as_u64()),
            )
            .then(
                left["disambiguation_id"]
                    .as_str()
                    .cmp(&right["disambiguation_id"].as_str()),
            )
    });
    json!({
        "root": root,
        "mode": "structural check, not certification",
        "root_path_disambiguation_count": entries.len() + forked.len(),
        "forked_disambiguation_ids": forked,
        "unforked_count": entries.len(),
        "disambiguations": entries,
        "rule": "A sense fork needs a coverage statement, an exclusivity statement and a verified joint theorem by cases taking the coverage statement as a premise: the disambiguation's coverage_statement_id, exclusivity_statement_id and fork_result_ids, or statements linking it whose IDs end in -SENSES-EXHAUSTIVE / -SENSE-UNIQUE (or -SENSES-EXCLUSIVE) and a verified result whose argument links it and takes that coverage premise.",
        "remedy": "First state coverage and exclusivity; then prove each sense's branch (yields the step) or refute it (countermodel or refutes relation); then the joint theorem by cases (docs/configuration-elimination-loop.md, certified forks). Only then pursue rival definitions and worldviews.",
    })
}

pub fn format_senses(report: &Value) -> String {
    let mut lines = vec![
        format!(
            "Unforked senses on root paths (root {}; structural check, not certification)",
            report["root"].as_str().unwrap_or_default()
        ),
        format!(
            "root-path disambiguations: {}; with a certified sense fork: {}; without: {}",
            report["root_path_disambiguation_count"],
            report["forked_disambiguation_ids"]
                .as_array()
                .map_or(0, Vec::len),
            report["unforked_count"]
        ),
        "A fork needs coverage, exclusivity and a joint theorem by cases (docs/corpus-model.md, \"Sense forks\").".into(),
    ];
    for entry in report["disambiguations"].as_array().into_iter().flatten() {
        let strings = |field: &str| -> Vec<&str> {
            entry[field]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .collect()
        };
        let links = strings("root_path_links");
        lines.push(String::new());
        lines.push(format!(
            "{} ({}): {} senses; missing {}; {} root-path links",
            entry["disambiguation_id"].as_str().unwrap_or_default(),
            entry["term"].as_str().unwrap_or_default(),
            entry["sense_count"],
            strings("missing").join(", "),
            links.len(),
        ));
        lines.push(format!("  senses: {}", strings("senses").join(", ")));
        let more = links.len().saturating_sub(3);
        lines.push(format!(
            "  root-path links: {}{}",
            links[..links.len().min(3)].join(", "),
            if more > 0 {
                format!(" (+{more} more)")
            } else {
                String::new()
            }
        ));
    }
    lines.join("\n")
}

pub fn format(report: &Value) -> String {
    let count = |field: &str| report[field].as_u64().unwrap_or(0);
    let mut lines = vec![
        format!(
            "Disconnected verified work (root {}; grouped by {}; discovery, not certification)",
            report["root"].as_str().unwrap_or_default(),
            report["by"].as_str().unwrap_or_default()
        ),
        format!(
            "verified results: {}; conclusion reaches the root: {}; disconnected: {} ({} non-transcription, {} transcription)",
            count("verified_result_count"),
            count("connected_result_count"),
            count("disconnected_result_count"),
            count("disconnected_non_transcription_count"),
            count("disconnected_transcription_count"),
        ),
        "Contacts are advisory leads, not equivalences or entailments.".into(),
    ];
    for group in report["groups"].as_array().into_iter().flatten() {
        let conclusions: Vec<&str> = group["conclusion_statement_ids"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .collect();
        lines.push(String::new());
        lines.push(format!(
            "{}  {} results ({} non-transcription, {} transcription; {} touch the root path), {} conclusions",
            group["group"].as_str().unwrap_or_default(),
            group["result_count"],
            group["non_transcription_count"],
            group["transcription_count"],
            group["touching_root_path_count"],
            conclusions.len(),
        ));
        let shown: Vec<&str> = conclusions
            .iter()
            .take(TEXT_CONCLUSION_LIMIT)
            .copied()
            .collect();
        let more = conclusions.len().saturating_sub(TEXT_CONCLUSION_LIMIT);
        lines.push(format!(
            "  conclusions: {}{}",
            shown.join(", "),
            if more > 0 {
                format!(" (+{more} more; --json lists all)")
            } else {
                String::new()
            }
        ));
        let contacts = group["contacts"].as_array().cloned().unwrap_or_default();
        if contacts.is_empty() {
            lines.push("  nearest root-path contacts: none found".into());
            continue;
        }
        lines.push("  nearest root-path contacts:".into());
        for contact in contacts {
            let reasons: Vec<String> = contact["reasons"]
                .as_array()
                .into_iter()
                .flatten()
                .take(2)
                .map(describe)
                .collect();
            lines.push(format!(
                "    {}  {}",
                contact["statement_id"].as_str().unwrap_or_default(),
                reasons.join("; ")
            ));
        }
    }
    lines.join("\n")
}

fn describe(reason: &Value) -> String {
    let strings = |field: &str| -> String {
        let items: Vec<&str> = reason[field]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .collect();
        let more = items.len().saturating_sub(4);
        let shown = items[..items.len().min(4)].join(", ");
        if more > 0 {
            format!("{shown} (+{more})")
        } else {
            shown
        }
    };
    let field = |name: &str| reason[name].as_str().unwrap_or_default().to_owned();
    match reason["kind"].as_str().unwrap_or_default() {
        "root_path_result_imports_group_solution" => {
            format!("{} imports {}", field("result_id"), field("module"))
        }
        "group_solution_imports_root_path_result" => {
            format!("group imports {} ({})", field("module"), field("result_id"))
        }
        "shared_vocabulary_module" => format!("shares vocabulary {}", strings("modules")),
        "shared_definitions" => format!("shares {}", strings("ids")),
        "text_overlap" => format!("words {}", strings("words")),
        other => other.to_owned(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Corpus;
    use std::path::PathBuf;

    struct Dir(PathBuf);
    impl Drop for Dir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn write(root: &Path, relative: &str, value: &str) {
        let path = root.join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, value).unwrap();
    }

    fn fixture() -> Dir {
        use std::sync::atomic::{AtomicU32, Ordering};
        static NEXT: AtomicU32 = AtomicU32::new(0);
        let root = std::env::temp_dir().join(format!(
            "truth-orphans-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        let statement = |id: &str, paraphrase: &str, lean: &str| {
            write(
                &root,
                &format!("corpus/statements/{id}.json"),
                &json!({"id": id, "paraphrase": paraphrase, "lean_declaration": lean}).to_string(),
            )
        };
        statement("ROOT", "The root holds.", "TruthCore.Case.root");
        statement(
            "P",
            "Necessary being exists in every world.",
            "TruthCore.Case.p",
        );
        statement(
            "Q",
            "Kripke frames are reflexive.",
            "TruthCore.Modal.Kripke.q",
        );
        statement(
            "M",
            "Necessary being exists in every accessible world.",
            "TruthCore.Modal.Kripke.m",
        );
        statement("N", "Kripke frame lemma.", "TruthCore.Modal.Kripke.n");
        statement("C", "A causal chain is finite.", "TruthCore.Causality.c");
        let argument =
            |id: &str, premises: &[&str], conclusion: &str, area: &str, transcription: bool| {
                write(
                    &root,
                    &format!("corpus/arguments/{id}.json"),
                    &json!({"id": id, "premise_statement_ids": premises, "inference_ids": ["I"],
                        "conclusion_statement_id": conclusion, "meaning": "m"})
                    .to_string(),
                );
                let module = format!("TruthCore.Results.{area}.{id}");
                let mut result = json!({"id": id, "argument_id": id,
                "challenge_module": format!("{module}.Challenge"),
                "solution_module": format!("{module}.Solution"),
                "theorem": format!("{module}.t"), "comparator_config": "c",
                "status": "solution-present"});
                if transcription {
                    result["transcription"] = json!("single_application");
                }
                write(
                    &root,
                    &format!("corpus/results/{id}.json"),
                    &result.to_string(),
                );
            };
        argument("ROOT-ARG", &["P"], "ROOT", "Case", false);
        argument("MODAL-A", &["Q"], "M", "Modal", false);
        argument("MODAL-B", &["N"], "Q", "Modal", true);
        argument("CAUSE-A", &["P"], "C", "Causality", false);
        write(&root, "TruthCore/Case.lean", "module\n");
        write(&root, "TruthCore/Modal/Kripke.lean", "module\n");
        write(
            &root,
            "TruthCore/Results/Modal/MODAL-A/Solution.lean",
            "module\n\npublic import TruthCore.Modal.Kripke\npublic import TruthCore.Imports.Modal\n",
        );
        write(
            &root,
            "TruthCore/Results/Case/ROOT-ARG/Solution.lean",
            "module\n\npublic import TruthCore.Results.Modal.MODAL-A.Solution\n",
        );
        Dir(root)
    }

    #[test]
    fn module_areas() {
        assert_eq!(
            module_area("TruthCore.Results.Modal.K.Solution"),
            "TruthCore.Modal"
        );
        assert_eq!(module_area("TruthCore.Modal.Kripke"), "TruthCore.Modal");
        assert_eq!(module_area(""), "(no module)");
    }

    #[test]
    fn groups_disconnected_results_with_contacts() {
        let dir = fixture();
        let corpus = Corpus::load(&dir.0).unwrap();
        let report = report(&dir.0, &corpus, "ROOT", GroupBy::Module);
        assert_eq!(report["verified_result_count"], 4);
        assert_eq!(report["connected_result_count"], 1);
        assert_eq!(report["disconnected_result_count"], 3);
        assert_eq!(report["disconnected_transcription_count"], 1);
        let groups = report["groups"].as_array().unwrap();
        assert_eq!(groups[0]["group"], "TruthCore.Modal");
        assert_eq!(groups[0]["result_count"], 2);
        assert_eq!(groups[0]["transcription_count"], 1);
        assert_eq!(groups[0]["conclusion_statement_ids"], json!(["M", "Q"]));
        // The root-path result imports MODAL-A's Solution: a tier-0 lead.
        let contact = &groups[0]["contacts"][0];
        assert_eq!(contact["statement_id"], "ROOT");
        assert_eq!(contact["tier"], 0);
        // CAUSE-A consumes a root-path premise without reaching the root.
        assert_eq!(groups[1]["group"], "TruthCore.Causality");
        assert_eq!(groups[1]["touching_root_path_count"], 1);
        assert_eq!(
            groups[1]["results"][0]["touches_root_path"],
            json!(["premise P"])
        );
        let text = format(&report);
        assert!(text.contains("TruthCore.Modal  2 results (1 non-transcription, 1 transcription"));
        assert!(text.contains("ROOT-ARG imports TruthCore.Results.Modal.MODAL-A.Solution"));
    }

    #[test]
    fn families_join_arguments_through_shared_statements() {
        let dir = fixture();
        let corpus = Corpus::load(&dir.0).unwrap();
        let report = report(&dir.0, &corpus, "ROOT", GroupBy::Family);
        let groups = report["groups"].as_array().unwrap();
        assert_eq!(groups.len(), 2);
        assert_eq!(groups[0]["group"], "TruthCore.Modal family of M");
        assert_eq!(groups[0]["result_count"], 2);
    }

    #[test]
    fn sense_forks_need_coverage_exclusivity_and_a_joint_theorem() {
        let dir = fixture();
        let root = &dir.0;
        for sense in ["DEF-S1", "DEF-S2"] {
            write(
                root,
                &format!("corpus/definitions/{sense}.json"),
                &json!({"id": sense, "term": "t", "definition": "d", "basis": "stipulative"})
                    .to_string(),
            );
        }
        let disambiguation = |fields: Value| {
            let mut record = json!({"id": "DISAMB-T", "term": "t", "resolution": "r",
                "sense_definition_ids": ["DEF-S1", "DEF-S2"]});
            for (key, value) in fields.as_object().unwrap() {
                record[key] = value.clone();
            }
            write(
                root,
                "corpus/disambiguations/DISAMB-T.json",
                &record.to_string(),
            );
        };
        // P reaches the root and uses one sense: the term is on a root path.
        write(
            root,
            "corpus/statements/P.json",
            &json!({"id": "P", "paraphrase": "p", "definition_ids": ["DEF-S1"]}).to_string(),
        );
        for id in ["T-SENSES-EXHAUSTIVE", "T-SENSE-UNIQUE"] {
            write(
                root,
                &format!("corpus/statements/{id}.json"),
                &json!({"id": id, "paraphrase": "x", "disambiguation_ids": ["DISAMB-T"]})
                    .to_string(),
            );
        }
        disambiguation(json!({}));
        let unforked = sense_report(root, &Corpus::load(root).unwrap(), "ROOT");
        assert_eq!(unforked["unforked_count"], 1);
        assert_eq!(
            unforked["disambiguations"][0]["missing"],
            json!(["joint_theorem"])
        );
        assert_eq!(
            unforked["disambiguations"][0]["coverage_statement_id"],
            "T-SENSES-EXHAUSTIVE"
        );
        // A verified joint theorem taking the coverage premise completes it.
        write(
            root,
            "corpus/arguments/FORK.json",
            &json!({"id": "FORK", "premise_statement_ids": ["T-SENSES-EXHAUSTIVE"],
                    "inference_ids": ["I"], "conclusion_statement_id": "C", "meaning": "m",
                    "disambiguation_ids": ["DISAMB-T"]})
            .to_string(),
        );
        write(
            root,
            "corpus/results/FORK.json",
            &json!({"id": "FORK", "argument_id": "FORK", "challenge_module": "c",
                    "solution_module": "s", "theorem": "t", "comparator_config": "c",
                    "status": "solution-present"})
            .to_string(),
        );
        let forked = sense_report(root, &Corpus::load(root).unwrap(), "ROOT");
        assert_eq!(forked["unforked_count"], 0);
        assert_eq!(forked["forked_disambiguation_ids"], json!(["DISAMB-T"]));
        // Declared fields win: a named result that is not the fork leaves it open.
        disambiguation(json!({"fork_result_ids": ["MODAL-A"]}));
        let declared = sense_report(root, &Corpus::load(root).unwrap(), "ROOT");
        assert_eq!(declared["unforked_count"], 1);
        assert!(format_senses(&declared).contains("DISAMB-T (t): 2 senses; missing joint_theorem"));
    }

    #[test]
    fn real_corpus_shows_modal_as_a_large_disconnected_group() {
        let checkout = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
        let Ok(corpus) = Corpus::load(&checkout) else {
            return;
        };
        let report = report(&checkout, &corpus, thickness::DEFAULT_ROOT, GroupBy::Module);
        let modal = report["groups"]
            .as_array()
            .unwrap()
            .iter()
            .find(|group| group["group"] == "TruthCore.Modal")
            .expect("TruthCore.Modal is a disconnected group");
        assert!(
            modal["result_count"].as_u64().unwrap() >= 40,
            "{}",
            modal["result_count"]
        );
    }
}
