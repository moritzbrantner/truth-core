use anyhow::{Context, Result, bail};
use serde::Deserialize;
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    env,
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};
use tempfile::tempdir;

const PRIMITIVE_TARGETS: &[&str] = &[
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.pow",
    "Nat.gcd",
    "Nat.div",
    "Nat.mod",
    "Nat.beq",
    "Nat.ble",
    "Nat.land",
    "Nat.lor",
    "Nat.xor",
    "Nat.shiftLeft",
    "Nat.shiftRight",
    "String.ofList",
    "Char.ofNat",
    "List",
    "eagerReduce",
];

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Config {
    challenge_module: String,
    solution_module: String,
    theorem_names: Vec<String>,
    #[serde(default)]
    definition_names: Vec<String>,
    permitted_axioms: Vec<String>,
    #[serde(default)]
    enable_nanoda: bool,
    #[serde(default)]
    external_kernels: BTreeMap<String, Vec<String>>,
}

struct Tools {
    landrun: String,
    lean4export: String,
    lean_prefix: PathBuf,
    git: PathBuf,
}

#[derive(Clone)]
struct Declaration {
    kind: String,
    data: Value,
}

struct Export {
    names: HashMap<u64, Value>,
    levels: HashMap<u64, Value>,
    expressions: HashMap<u64, Value>,
    declarations: HashMap<String, Declaration>,
}

impl Export {
    fn parse(input: &str) -> Result<Self> {
        let mut names = HashMap::from([(0, Value::String("_".into()))]);
        let mut levels = HashMap::from([(0, json!({ "zero": true }))]);
        let mut expressions = HashMap::new();
        let mut declarations = HashMap::new();

        for (line_number, line) in input.lines().enumerate() {
            let item: Value = serde_json::from_str(line)
                .with_context(|| format!("invalid export JSON on line {}", line_number + 1))?;
            let object = item.as_object().context("export item is not an object")?;
            if object.contains_key("meta") {
                continue;
            }
            if let Some(index) = object.get("in").and_then(Value::as_u64) {
                let name = object
                    .get("str")
                    .or_else(|| object.get("num"))
                    .context("name export lacks str or num")?;
                let tag = if object.contains_key("str") {
                    "str"
                } else {
                    "num"
                };
                names.insert(index, json!({ tag: name }));
                continue;
            }
            if let Some(index) = object.get("il").and_then(Value::as_u64) {
                let tag = ["succ", "max", "imax", "param"]
                    .into_iter()
                    .find(|tag| object.contains_key(*tag))
                    .context("invalid level export")?;
                levels.insert(index, json!({ tag: object.get(tag).unwrap() }));
                continue;
            }
            if let Some(index) = object.get("ie").and_then(Value::as_u64) {
                let tag = [
                    "bvar", "sort", "const", "app", "lam", "forallE", "letE", "proj", "natVal",
                    "strVal", "mdata",
                ]
                .into_iter()
                .find(|tag| object.contains_key(*tag))
                .context("invalid expression export")?;
                expressions.insert(index, json!({ tag: object.get(tag).unwrap() }));
                continue;
            }
            for kind in ["axiom", "def", "thm", "opaque", "quot"] {
                if let Some(data) = object.get(kind) {
                    insert_declaration(&mut declarations, &names, kind, data)?;
                    break;
                }
            }
            if let Some(inductive) = object.get("inductive") {
                for (field, kind) in [("types", "inductive"), ("ctors", "ctor"), ("recs", "rec")] {
                    for data in inductive
                        .get(field)
                        .and_then(Value::as_array)
                        .with_context(|| format!("inductive export lacks {field}"))?
                    {
                        insert_declaration(&mut declarations, &names, kind, data)?;
                    }
                }
            }
        }
        Ok(Self {
            names,
            levels,
            expressions,
            declarations,
        })
    }

    fn declaration(&self, name: &str) -> Result<&Declaration> {
        self.declarations
            .get(name)
            .with_context(|| format!("constant not found in export: {name}"))
    }

    fn used_constants(&self, declaration: &Declaration) -> Result<BTreeSet<String>> {
        let mut result = BTreeSet::new();
        let data = declaration
            .data
            .as_object()
            .context("declaration is not an object")?;
        for field in ["type", "value"] {
            if let Some(index) = data.get(field).and_then(Value::as_u64) {
                self.collect_expression_constants(index, &mut result)?;
            }
        }
        if let Some(rules) = data.get("rules").and_then(Value::as_array) {
            for rule in rules {
                if let Some(index) = rule.get("rhs").and_then(Value::as_u64) {
                    self.collect_expression_constants(index, &mut result)?;
                }
            }
        }
        for field in ["all", "ctors"] {
            if let Some(indexes) = data.get(field).and_then(Value::as_array) {
                for index in indexes {
                    result.insert(resolve_name(
                        &self.names,
                        index
                            .as_u64()
                            .with_context(|| format!("{field} contains a non-index"))?,
                    )?);
                }
            }
        }
        if let Some(index) = data.get("induct").and_then(Value::as_u64) {
            result.insert(resolve_name(&self.names, index)?);
        }
        Ok(result)
    }

    fn type_constants(&self, declaration: &Declaration) -> Result<BTreeSet<String>> {
        let data = declaration
            .data
            .as_object()
            .context("declaration is not an object")?;
        let index = data
            .get("type")
            .and_then(Value::as_u64)
            .context("declaration lacks a type expression")?;
        let mut result = BTreeSet::new();
        self.collect_expression_constants(index, &mut result)?;
        Ok(result)
    }

    fn collect_expression_constants(
        &self,
        index: u64,
        result: &mut BTreeSet<String>,
    ) -> Result<()> {
        self.collect_constants(index, result, &mut HashSet::new(), &mut HashSet::new())
    }

    fn collect_constants(
        &self,
        index: u64,
        result: &mut BTreeSet<String>,
        completed: &mut HashSet<u64>,
        active: &mut HashSet<u64>,
    ) -> Result<()> {
        if active.contains(&index) {
            bail!("cyclic dependency expression at index {index}");
        }
        if completed.contains(&index) {
            return Ok(());
        }
        active.insert(index);
        let item = self
            .expressions
            .get(&index)
            .with_context(|| format!("unknown expression index {index}"))?;
        if let Some(data) = item.get("const") {
            result.insert(resolve_name(
                &self.names,
                data.get("name")
                    .and_then(Value::as_u64)
                    .context("constant lacks name")?,
            )?);
        }
        for field in ["fn", "arg", "type", "value", "body", "struct", "expr"] {
            if let Some(index) = item.get(field).and_then(Value::as_u64) {
                self.collect_constants(index, result, completed, active)?;
            }
        }
        if let Some(data) = item
            .get("app")
            .or_else(|| item.get("lam"))
            .or_else(|| item.get("forallE"))
            .or_else(|| item.get("letE"))
            .or_else(|| item.get("proj"))
            .or_else(|| item.get("mdata"))
        {
            for field in ["fn", "arg", "type", "value", "body", "struct", "expr"] {
                if let Some(index) = data.get(field).and_then(Value::as_u64) {
                    self.collect_constants(index, result, completed, active)?;
                }
            }
        }
        active.remove(&index);
        completed.insert(index);
        Ok(())
    }
}

// Both exports share this exact structural interner. Child references are IDs in
// this arena, never expanded trees or digest-only identities. Hash collisions are
// resolved by full Value equality. Expression and universe nodes have disjoint tags.
#[derive(Default)]
struct CanonicalNodes {
    nodes: HashMap<(NodeKind, Value), u64>,
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
enum NodeKind {
    Expression,
    Level,
}

// One immutable export per context makes its ID cache export-specific. The
// normalization policy is fixed (validated lambda annotations only), and neither
// expression nor level canonicalization depends on binder scope. Only successful
// nodes enter completed; active nodes are checked first to reject cycles.
struct Canonicalizer<'a> {
    export: &'a Export,
    nodes: &'a std::cell::RefCell<CanonicalNodes>,
    completed: HashMap<(NodeKind, u64), Value>,
    active: HashSet<(NodeKind, u64)>,
}

impl<'a> Canonicalizer<'a> {
    fn new(export: &'a Export, nodes: &'a std::cell::RefCell<CanonicalNodes>) -> Self {
        Self {
            export,
            nodes,
            completed: HashMap::new(),
            active: HashSet::new(),
        }
    }

    fn expression(&mut self, index: u64) -> Result<Value> {
        self.node(NodeKind::Expression, index)
    }

    fn level(&mut self, index: u64) -> Result<Value> {
        self.node(NodeKind::Level, index)
    }

    fn node(&mut self, kind: NodeKind, index: u64) -> Result<Value> {
        let key = (kind, index);
        if self.active.contains(&key) {
            bail!("cyclic expression or universe at index {index}");
        }
        if let Some(value) = self.completed.get(&key) {
            return Ok(value.clone());
        }
        self.active.insert(key);
        let result = match kind {
            NodeKind::Expression => expression_node(self, index),
            NodeKind::Level => level_node(self, index),
        };
        self.active.remove(&key);
        let node = result?;
        let mut nodes = self.nodes.borrow_mut();
        let next = nodes.nodes.len() as u64;
        let id = *nodes.nodes.entry((kind, node)).or_insert(next);
        let value = json!(id);
        self.completed.insert(key, value.clone());
        Ok(value)
    }
}

fn level_node(context: &mut Canonicalizer<'_>, index: u64) -> Result<Value> {
    let export = context.export;
    if index == 0 {
        return Ok(json!({ "zero": true }));
    }
    let item = export
        .levels
        .get(&index)
        .with_context(|| format!("unknown level index {index}"))?;
    if let Some(value) = item.get("succ") {
        return Ok(
            json!({ "succ": context.level(value.as_u64().context("invalid successor level")?)? }),
        );
    }
    for tag in ["max", "imax"] {
        if let Some(values) = item.get(tag).and_then(Value::as_array) {
            return Ok(json!({ tag: [
                context.level(values.first().and_then(Value::as_u64).context("level is missing left operand")?)?,
                context.level(values.get(1).and_then(Value::as_u64).context("level is missing right operand")?)?
            ] }));
        }
    }
    if let Some(value) = item.get("param") {
        return Ok(
            json!({ "param": resolve_name(&export.names, value.as_u64().context("invalid level parameter")?)? }),
        );
    }
    bail!("invalid level index {index}")
}

fn expression_node(context: &mut Canonicalizer<'_>, index: u64) -> Result<Value> {
    let export = context.export;
    let item = export
        .expressions
        .get(&index)
        .with_context(|| format!("unknown expression index {index}"))?;
    if let Some(value) = item.get("bvar") {
        return Ok(json!({ "bvar": value }));
    }
    if let Some(value) = item.get("sort") {
        return Ok(
            json!({ "sort": context.level(value.as_u64().context("invalid sort level")?)? }),
        );
    }
    if let Some(data) = item.get("const") {
        let universes = data
            .get("us")
            .and_then(Value::as_array)
            .context("constant lacks universes")?
            .iter()
            .map(|level| context.level(level.as_u64().context("invalid universe")?))
            .collect::<Result<Vec<_>>>()?;
        return Ok(json!({ "const": {
            "name": resolve_name(&export.names, data.get("name").and_then(Value::as_u64).context("constant lacks name")?)?,
            "us": universes
        }}));
    }
    if let Some(data) = item.get("app") {
        return Ok(json!({ "app": {
            "fn": context.expression(data.get("fn").and_then(Value::as_u64).context("application lacks fn")?)?,
            "arg": context.expression(data.get("arg").and_then(Value::as_u64).context("application lacks arg")?)?
        }}));
    }
    for tag in ["lam", "forallE"] {
        if let Some(data) = item.get(tag) {
            let binder_info = data.get("binderInfo").context("binder lacks binderInfo")?;
            let binder_info = if tag == "lam" {
                // Lambda annotations guide elaboration, not kernel identity. Validate
                // the export before erasing only this annotation; forallE stays exact.
                match binder_info.as_str() {
                    Some("default" | "implicit" | "strictImplicit" | "instImplicit") => {
                        json!("default")
                    }
                    _ => bail!("invalid lambda binderInfo"),
                }
            } else {
                binder_info.clone()
            };
            return Ok(json!({ tag: {
                "type": context.expression(data.get("type").and_then(Value::as_u64).context("binder lacks type")?)?,
                "body": context.expression(data.get("body").and_then(Value::as_u64).context("binder lacks body")?)?,
                "binderInfo": binder_info
            }}));
        }
    }
    if let Some(data) = item.get("letE") {
        return Ok(json!({ "letE": {
            "type": context.expression(data.get("type").and_then(Value::as_u64).context("let lacks type")?)?,
            "value": context.expression(data.get("value").and_then(Value::as_u64).context("let lacks value")?)?,
            "body": context.expression(data.get("body").and_then(Value::as_u64).context("let lacks body")?)?,
            "nondep": data.get("nondep").cloned().context("let lacks nondep")?
        }}));
    }
    if let Some(data) = item.get("proj") {
        return Ok(json!({ "proj": {
            "typeName": resolve_name(&export.names, data.get("typeName").and_then(Value::as_u64).context("projection lacks typeName")?)?,
            "idx": data.get("idx").cloned().context("projection lacks idx")?,
            "struct": context.expression(data.get("struct").and_then(Value::as_u64).context("projection lacks struct")?)?
        }}));
    }
    for tag in ["natVal", "strVal"] {
        if let Some(value) = item.get(tag) {
            return Ok(json!({ tag: value }));
        }
    }
    bail!("unsupported expression index {index}")
}

#[cfg(test)]
fn reference_level(export: &Export, index: u64) -> Result<Value> {
    if index == 0 {
        return Ok(json!({ "zero": true }));
    }
    let item = export
        .levels
        .get(&index)
        .with_context(|| format!("unknown level index {index}"))?;
    if let Some(value) = item.get("succ") {
        return Ok(
            json!({ "succ": reference_level(export, value.as_u64().context("invalid successor level")?)? }),
        );
    }
    for tag in ["max", "imax"] {
        if let Some(values) = item.get(tag).and_then(Value::as_array) {
            return Ok(json!({ tag: [
                reference_level(export, values.first().and_then(Value::as_u64).context("level is missing left operand")?)?,
                reference_level(export, values.get(1).and_then(Value::as_u64).context("level is missing right operand")?)?
            ] }));
        }
    }
    if let Some(value) = item.get("param") {
        return Ok(
            json!({ "param": resolve_name(&export.names, value.as_u64().context("invalid level parameter")?)? }),
        );
    }
    bail!("invalid level index {index}")
}

#[cfg(test)]
fn reference_expression(export: &Export, index: u64) -> Result<Value> {
    let item = export
        .expressions
        .get(&index)
        .with_context(|| format!("unknown expression index {index}"))?;
    if let Some(value) = item.get("bvar") {
        return Ok(json!({ "bvar": value }));
    }
    if let Some(value) = item.get("sort") {
        return Ok(
            json!({ "sort": reference_level(export, value.as_u64().context("invalid sort level")?)? }),
        );
    }
    if let Some(data) = item.get("const") {
        let universes = data
            .get("us")
            .and_then(Value::as_array)
            .context("constant lacks universes")?
            .iter()
            .map(|level| reference_level(export, level.as_u64().context("invalid universe")?))
            .collect::<Result<Vec<_>>>()?;
        return Ok(json!({ "const": {
            "name": resolve_name(&export.names, data.get("name").and_then(Value::as_u64).context("constant lacks name")?)?,
            "us": universes
        }}));
    }
    if let Some(data) = item.get("app") {
        return Ok(json!({ "app": {
            "fn": reference_expression(export, data.get("fn").and_then(Value::as_u64).context("application lacks fn")?)?,
            "arg": reference_expression(export, data.get("arg").and_then(Value::as_u64).context("application lacks arg")?)?
        }}));
    }
    for tag in ["lam", "forallE"] {
        if let Some(data) = item.get(tag) {
            let binder_info = data.get("binderInfo").context("binder lacks binderInfo")?;
            let binder_info = if tag == "lam" {
                // Lambda annotations guide elaboration, not kernel identity. Validate
                // the export before erasing only this annotation; forallE stays exact.
                match binder_info.as_str() {
                    Some("default" | "implicit" | "strictImplicit" | "instImplicit") => {
                        json!("default")
                    }
                    _ => bail!("invalid lambda binderInfo"),
                }
            } else {
                binder_info.clone()
            };
            return Ok(json!({ tag: {
                "type": reference_expression(export, data.get("type").and_then(Value::as_u64).context("binder lacks type")?)?,
                "body": reference_expression(export, data.get("body").and_then(Value::as_u64).context("binder lacks body")?)?,
                "binderInfo": binder_info
            }}));
        }
    }
    if let Some(data) = item.get("letE") {
        return Ok(json!({ "letE": {
            "type": reference_expression(export, data.get("type").and_then(Value::as_u64).context("let lacks type")?)?,
            "value": reference_expression(export, data.get("value").and_then(Value::as_u64).context("let lacks value")?)?,
            "body": reference_expression(export, data.get("body").and_then(Value::as_u64).context("let lacks body")?)?,
            "nondep": data.get("nondep").cloned().context("let lacks nondep")?
        }}));
    }
    if let Some(data) = item.get("proj") {
        return Ok(json!({ "proj": {
            "typeName": resolve_name(&export.names, data.get("typeName").and_then(Value::as_u64).context("projection lacks typeName")?)?,
            "idx": data.get("idx").cloned().context("projection lacks idx")?,
            "struct": reference_expression(export, data.get("struct").and_then(Value::as_u64).context("projection lacks struct")?)?
        }}));
    }
    for tag in ["natVal", "strVal"] {
        if let Some(value) = item.get(tag) {
            return Ok(json!({ tag: value }));
        }
    }
    bail!("unsupported expression index {index}")
}

fn canonical_declaration(
    context: &mut Canonicalizer<'_>,
    declaration: &Declaration,
) -> Result<Value> {
    let export = context.export;
    let data = declaration
        .data
        .as_object()
        .context("declaration is not an object")?;
    let mut result = Map::new();
    result.insert("kind".into(), Value::String(declaration.kind.clone()));
    for (field, value) in data {
        let value = match field.as_str() {
            "name" | "induct" => Value::String(resolve_name(
                &export.names,
                value
                    .as_u64()
                    .with_context(|| format!("{field} is not a name index"))?,
            )?),
            "all" | "ctors" | "levelParams" => Value::Array(
                value
                    .as_array()
                    .with_context(|| format!("{field} is not a name-index array"))?
                    .iter()
                    .map(|index| {
                        Ok(Value::String(resolve_name(
                            &export.names,
                            index
                                .as_u64()
                                .with_context(|| format!("{field} contains a non-index"))?,
                        )?))
                    })
                    .collect::<Result<Vec<_>>>()?,
            ),
            "type" | "value" | "rhs" => context.expression(
                value
                    .as_u64()
                    .with_context(|| format!("{field} is not an expression index"))?,
            )?,
            "rules" => Value::Array(
                value
                    .as_array()
                    .context("rules is not an array")?
                    .iter()
                    .map(|rule| canonical_rule(context, rule))
                    .collect::<Result<Vec<_>>>()?,
            ),
            _ => value.clone(),
        };
        result.insert(field.clone(), value);
    }
    Ok(Value::Object(result))
}

fn canonical_rule(context: &mut Canonicalizer<'_>, rule: &Value) -> Result<Value> {
    let export = context.export;
    let rule = rule.as_object().context("recursor rule is not an object")?;
    Ok(json!({
        "ctor": resolve_name(&export.names, rule.get("ctor").and_then(Value::as_u64).context("rule lacks ctor")?)?,
        "nfields": rule.get("nfields").cloned().context("rule lacks nfields")?,
        "rhs": context.expression(rule.get("rhs").and_then(Value::as_u64).context("rule lacks rhs")?)?
    }))
}

fn insert_declaration(
    declarations: &mut HashMap<String, Declaration>,
    names: &HashMap<u64, Value>,
    kind: &str,
    data: &Value,
) -> Result<()> {
    let index = data
        .get("name")
        .and_then(Value::as_u64)
        .context("declaration lacks name")?;
    let name = resolve_name(names, index)?;
    if declarations
        .insert(
            name.clone(),
            Declaration {
                kind: kind.into(),
                data: data.clone(),
            },
        )
        .is_some()
    {
        bail!("duplicate declaration {name} in export");
    }
    Ok(())
}

fn resolve_name(names: &HashMap<u64, Value>, index: u64) -> Result<String> {
    if index == 0 {
        return Ok(String::new());
    }
    let item = names
        .get(&index)
        .with_context(|| format!("unknown name index {index}"))?;
    if let Some(data) = item.get("str") {
        let prefix = resolve_name(
            names,
            data.get("pre")
                .and_then(Value::as_u64)
                .context("name lacks prefix")?,
        )?;
        let segment = data
            .get("str")
            .and_then(Value::as_str)
            .context("name lacks string segment")?;
        return Ok(if prefix.is_empty() {
            segment.into()
        } else {
            format!("{prefix}.{segment}")
        });
    }
    let data = item.get("num").context("invalid name item")?;
    let prefix = resolve_name(
        names,
        data.get("pre")
            .and_then(Value::as_u64)
            .context("name lacks prefix")?,
    )?;
    let segment = data
        .get("i")
        .and_then(Value::as_u64)
        .context("name lacks numeric segment")?;
    Ok(if prefix.is_empty() {
        segment.to_string()
    } else {
        format!("{prefix}.{segment}")
    })
}

fn statement(context: &mut Canonicalizer<'_>, declaration: &Declaration) -> Result<Value> {
    let export = context.export;
    if !matches!(declaration.kind.as_str(), "thm" | "axiom") {
        bail!("target is not a theorem or axiom");
    }
    let mut result = Map::new();
    result.insert("kind".into(), Value::String(declaration.kind.clone()));
    result.insert(
        "name".into(),
        Value::String(resolve_name(
            &export.names,
            declaration
                .data
                .get("name")
                .and_then(Value::as_u64)
                .context("target lacks name")?,
        )?),
    );
    result.insert(
        "levelParams".into(),
        Value::Array(
            declaration
                .data
                .get("levelParams")
                .and_then(Value::as_array)
                .context("target lacks levelParams")?
                .iter()
                .map(|index| {
                    Ok(Value::String(resolve_name(
                        &export.names,
                        index.as_u64().context("invalid level parameter")?,
                    )?))
                })
                .collect::<Result<Vec<_>>>()?,
        ),
    );
    result.insert(
        "type".into(),
        context.expression(
            declaration
                .data
                .get("type")
                .and_then(Value::as_u64)
                .context("target lacks type")?,
        )?,
    );
    Ok(Value::Object(result))
}

fn definition_signature(
    context: &mut Canonicalizer<'_>,
    declaration: &Declaration,
) -> Result<Value> {
    if declaration.kind != "def" {
        bail!("definition target is not a definition");
    }
    let mut result = canonical_declaration(context, declaration)?
        .as_object()
        .cloned()
        .context("definition is not an object")?;
    result.remove("value");
    Ok(Value::Object(result))
}

fn compare_exports(challenge: &Export, solution: &Export, config: &Config) -> Result<()> {
    let nodes = std::cell::RefCell::new(CanonicalNodes::default());
    let mut left = Canonicalizer::new(challenge, &nodes);
    let mut right = Canonicalizer::new(solution, &nodes);
    let theorem_targets: HashSet<&str> = config.theorem_names.iter().map(String::as_str).collect();
    let definition_targets: HashSet<&str> =
        config.definition_names.iter().map(String::as_str).collect();
    let mut worklist: Vec<String> = PRIMITIVE_TARGETS
        .iter()
        .map(|name| (*name).into())
        .collect();
    worklist.extend(config.permitted_axioms.iter().cloned());

    for target in &config.theorem_names {
        let challenge_target = challenge.declaration(target)?;
        let solution_target = solution.declaration(target)?;
        if statement(&mut left, challenge_target)? != statement(&mut right, solution_target)? {
            bail!("challenge and solution theorem statements do not match: {target}");
        }
        worklist.extend(challenge.type_constants(challenge_target)?);
    }
    for target in &config.definition_names {
        let challenge_target = challenge.declaration(target)?;
        let solution_target = solution.declaration(target)?;
        if definition_signature(&mut left, challenge_target)?
            != definition_signature(&mut right, solution_target)?
        {
            bail!("definition-hole signature does not match: {target}");
        }
        worklist.push(target.clone());
    }

    let mut checked = HashSet::new();
    while let Some(name) = worklist.pop() {
        if !checked.insert(name.clone()) {
            continue;
        }
        let challenge_declaration = challenge.declaration(&name)?;
        let solution_declaration = solution.declaration(&name)?;
        if theorem_targets.contains(name.as_str()) || definition_targets.contains(name.as_str()) {
            worklist.extend(solution.type_constants(solution_declaration)?);
            continue;
        }
        let challenge_value = canonical_declaration(&mut left, challenge_declaration)?;
        let solution_value = canonical_declaration(&mut right, solution_declaration)?;
        if challenge_value != solution_value {
            let differing_field = challenge_value
                .as_object()
                .and_then(|left| {
                    solution_value.as_object().and_then(|right| {
                        left.iter()
                            .find(|(field, value)| right.get(*field) != Some(*value))
                            .map(|(field, _)| field)
                    })
                })
                .map_or("<structure>", String::as_str);
            bail!(
                "constant does not match between challenge and solution: {name} ({differing_field})"
            );
        }
        worklist.extend(solution.used_constants(solution_declaration)?);
    }
    Ok(())
}

fn check_axioms(solution: &Export, config: &Config) -> Result<()> {
    let permitted: HashSet<&str> = config.permitted_axioms.iter().map(String::as_str).collect();
    let mut worklist = config.theorem_names.clone();
    worklist.extend(config.definition_names.clone());
    let mut checked = HashSet::new();
    while let Some(name) = worklist.pop() {
        if !checked.insert(name.clone()) {
            continue;
        }
        let declaration = solution.declaration(&name)?;
        if declaration.kind == "axiom" && !permitted.contains(name.as_str()) {
            bail!("illegal axiom detected: {name}");
        }
        worklist.extend(solution.used_constants(declaration)?);
    }
    Ok(())
}

fn run_checked(mut command: Command, description: &str) -> Result<Output> {
    let output = command
        .output()
        .with_context(|| format!("could not start {description}"))?;
    if !output.status.success() {
        bail!(
            "{description} exited with {}\n{}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        );
    }
    Ok(output)
}

fn command_output(program: impl AsRef<OsStr>, args: &[&str], description: &str) -> Result<String> {
    let mut command = Command::new(program);
    command.args(args);
    let output = run_checked(command, description)?;
    String::from_utf8(output.stdout).context("command did not emit UTF-8")
}

fn env_or(variable: &str, default: &str) -> String {
    env::var(variable).unwrap_or_else(|_| default.into())
}

fn tools() -> Result<Tools> {
    let lean_prefix =
        PathBuf::from(command_output("lean", &["--print-prefix"], "querying Lean prefix")?.trim());
    let git = PathBuf::from(command_output("which", &["git"], "finding git")?.trim());
    Ok(Tools {
        landrun: env_or("COMPARATOR_LANDRUN", "landrun"),
        lean4export: env_or("COMPARATOR_LEAN4EXPORT", "lean4export"),
        lean_prefix,
        git,
    })
}

fn sandbox(
    tools: &Tools,
    project: &Path,
    writable_lake: bool,
    program: &str,
    args: &[String],
    readable: &[&Path],
) -> Command {
    let mut command = Command::new(&tools.landrun);
    command
        .args([
            "--best-effort",
            "--ro",
            "/",
            "--rw",
            "/dev",
            "-ldd",
            "-add-exec",
        ])
        .args([
            "--env",
            "PATH",
            "--env",
            "HOME",
            "--env",
            "LEAN_PATH",
            "--env",
            "LEAN_ABORT_ON_PANIC",
        ])
        .arg("--ro")
        .arg(project)
        .arg("--rox")
        .arg(&tools.lean_prefix)
        .arg("--rox")
        .arg(&tools.git);
    for path in readable {
        command.arg("--ro").arg(path);
    }
    if writable_lake {
        command.arg("--rwx").arg(project.join(".lake"));
    } else {
        command.arg("--ro").arg(project.join(".lake"));
    }
    command
        .arg("--")
        .arg(program)
        .args(args)
        .current_dir(project)
        .env("LEAN_ABORT_ON_PANIC", "1");
    command
}

fn build_module(tools: &Tools, project: &Path, module: &str) -> Result<()> {
    fs::create_dir_all(project.join(".lake")).context("creating .lake directory")?;
    let output = run_checked(
        sandbox(
            tools,
            project,
            true,
            "lake",
            &["build".into(), module.into()],
            &[],
        ),
        &format!("sandboxed lake build {module}"),
    )?;
    print!("{}", String::from_utf8_lossy(&output.stdout));
    eprint!("{}", String::from_utf8_lossy(&output.stderr));
    Ok(())
}

fn export_module(
    tools: &Tools,
    project: &Path,
    module: &str,
    targets: &[String],
) -> Result<String> {
    let mut args = vec![module.into(), "--".into()];
    args.extend(targets.iter().cloned());
    let output = run_checked(
        sandbox(tools, project, false, &tools.lean4export, &args, &[]),
        &format!("sandboxed export of {module}"),
    )?;
    String::from_utf8(output.stdout).context("lean4export did not emit UTF-8")
}

fn run_external_kernels(
    tools: &Tools,
    project: &Path,
    config: &Config,
    solution: &str,
) -> Result<()> {
    let mut kernels = config.external_kernels.clone();
    if config.enable_nanoda {
        if !kernels.is_empty() {
            bail!("cannot combine enable_nanoda with external_kernels");
        }
        kernels.insert(
            "nanoda".into(),
            vec![env_or("COMPARATOR_NANODA", "nanoda_bin")],
        );
    }
    for (name, command) in kernels {
        let (program, supplied_args) = command
            .split_first()
            .with_context(|| format!("{name} has an empty command"))?;
        let temporary = tempdir().context("creating temporary kernel directory")?;
        let export_path = temporary.path().join("solution.ndjson");
        let config_path = temporary.path().join("config.json");
        let mut kernel_permitted_axioms = config.permitted_axioms.clone();
        // Lean's prelude declaration graph uses propositional extensionality even
        // when the advertised result does not. The Rust closure check above is
        // the policy authority; NanoDa needs this declaration available to
        // reconstruct the exported environment.
        if !kernel_permitted_axioms
            .iter()
            .any(|axiom| axiom == "propext")
        {
            kernel_permitted_axioms.push("propext".into());
        }
        fs::write(&export_path, solution).context("writing solution export")?;
        fs::write(
            &config_path,
            serde_json::to_vec(&json!({
                "use_stdin": false,
                "export_file_path": export_path,
                "permitted_axioms": kernel_permitted_axioms,
                "unpermitted_axiom_hard_error": true,
                "nat_extension": true,
                "string_extension": true
            }))?,
        )
        .context("writing kernel configuration")?;
        let input = if name.contains("noda") {
            &config_path
        } else {
            &export_path
        };
        let mut args = supplied_args.to_vec();
        args.push(input.display().to_string());
        println!("Running {name} kernel on solution");
        run_checked(
            sandbox(
                tools,
                project,
                false,
                program,
                &args,
                &[&export_path, &config_path],
            ),
            &format!("{name} kernel"),
        )?;
        println!("{name} kernel accepts the solution");
    }
    Ok(())
}

fn verify(path: &Path) -> Result<()> {
    let config: Config = serde_json::from_str(
        &fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?,
    )
    .context("invalid comparator JSON")?;
    if config.theorem_names.is_empty() {
        bail!("theorem_names must not be empty");
    }
    let project = env::current_dir().context("reading current directory")?;
    let tools = tools()?;
    let mut targets: Vec<String> = ["Nat", "String", "String.mk", "Char"]
        .into_iter()
        .map(str::to_owned)
        .collect();
    if config
        .permitted_axioms
        .iter()
        .any(|axiom| axiom == "Quot.sound")
    {
        targets.extend(
            ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"]
                .into_iter()
                .map(str::to_owned),
        );
    }
    targets.extend(config.theorem_names.iter().cloned());
    targets.extend(config.permitted_axioms.iter().cloned());
    targets.extend(PRIMITIVE_TARGETS.iter().map(|name| (*name).into()));
    targets.extend(config.definition_names.iter().cloned());

    println!("Building {}", config.challenge_module);
    build_module(&tools, &project, &config.challenge_module)?;
    let challenge_export = export_module(&tools, &project, &config.challenge_module, &targets)?;
    println!("Building {}", config.solution_module);
    build_module(&tools, &project, &config.solution_module)?;
    let solution_export = export_module(&tools, &project, &config.solution_module, &targets)?;
    let challenge = Export::parse(&challenge_export).context("parsing challenge export")?;
    let solution = Export::parse(&solution_export).context("parsing solution export")?;
    compare_exports(&challenge, &solution, &config)?;
    check_axioms(&solution, &config)?;
    run_external_kernels(&tools, &project, &config, &solution_export)?;
    println!("Your solution is okay!");
    Ok(())
}

fn main() {
    let mut arguments = env::args_os();
    let executable = arguments.next().unwrap_or_default();
    let Some(config) = arguments.next() else {
        eprintln!("usage: {} <CONFIG.json>", Path::new(&executable).display());
        std::process::exit(2);
    };
    if arguments.next().is_some() {
        eprintln!("usage: {} <CONFIG.json>", Path::new(&executable).display());
        std::process::exit(2);
    }
    if let Err(error) = verify(Path::new(&config)) {
        eprintln!("comparator error: {error:#}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn name(prefix: u64, segment: &str) -> Value {
        json!({ "str": { "pre": prefix, "str": segment } })
    }

    fn canonical_expression(export: &Export, index: u64) -> Result<Value> {
        let nodes = std::cell::RefCell::new(CanonicalNodes::default());
        let root = Canonicalizer::new(export, &nodes).expression(index)?;
        let mut ordered: Vec<_> = nodes.into_inner().nodes.into_iter().collect();
        ordered.sort_by_key(|(_, id)| *id);
        Ok(
            json!({ "root": root, "nodes": ordered.into_iter().map(|((_, node), _)| node).collect::<Vec<_>>() }),
        )
    }

    fn dag(depth: u64, offset: u64, split: bool) -> (Export, u64) {
        let mut export = Export {
            names: HashMap::from([(0, json!("_")), (1, name(0, "Nat")), (2, name(1, "add"))]),
            levels: HashMap::new(),
            expressions: HashMap::from([
                (offset, json!({"natVal": 0})),
                (offset + 1, json!({"const": {"name": 2, "us": []}})),
            ]),
            declarations: HashMap::new(),
        };
        let mut term = offset;
        for i in 0..depth {
            let a = offset + 2 + 3 * i;
            let b = a + 1;
            let copy = a + 2;
            export
                .expressions
                .insert(a, json!({"app": {"fn": offset + 1, "arg": term}}));
            let arg = if split {
                export
                    .expressions
                    .insert(copy, export.expressions[&term].clone());
                copy
            } else {
                term
            };
            export
                .expressions
                .insert(b, json!({"app": {"fn": a, "arg": arg}}));
            term = b;
        }
        (export, term)
    }

    fn compact_equal(left: &Export, a: u64, right: &Export, b: u64) -> Result<bool> {
        let nodes = std::cell::RefCell::new(CanonicalNodes::default());
        let a = Canonicalizer::new(left, &nodes).expression(a)?;
        let b = Canonicalizer::new(right, &nodes).expression(b)?;
        Ok(a == b)
    }

    fn complete_export(depth: u64, offset: u64, split: bool) -> Export {
        let (mut export, root) = dag(depth, offset, split);
        for (i, target) in PRIMITIVE_TARGETS.iter().chain(["goal"].iter()).enumerate() {
            let index = 100 + i as u64;
            // resolve_name accepts a complete segment, including periods.
            export.names.insert(index, name(0, target));
            export.declarations.insert(
                (*target).into(),
                Declaration {
                    kind: if *target == "goal" { "thm" } else { "def" }.into(),
                    data: json!({"name": index, "levelParams": [], "type": root, "value": root}),
                },
            );
        }
        export
    }

    fn test_config() -> Config {
        Config {
            challenge_module: "Challenge".into(),
            solution_module: "Solution".into(),
            theorem_names: vec!["goal".into()],
            definition_names: vec![],
            permitted_axioms: vec![],
            enable_nanoda: false,
            external_kernels: BTreeMap::new(),
        }
    }

    #[test]
    fn compare_exports_handles_shared_dags_and_still_rejects_changes() {
        let left = complete_export(32, 0, false);
        let mut right = complete_export(32, 1000, true);
        let config = test_config();
        compare_exports(&left, &right, &config).unwrap();
        right.declarations.get_mut("Nat.sub").unwrap().data["isUnsafe"] = json!(true);
        assert!(compare_exports(&left, &right, &config).is_err());
        right
            .declarations
            .get_mut("Nat.sub")
            .unwrap()
            .data
            .as_object_mut()
            .unwrap()
            .remove("isUnsafe");
        right.expressions.insert(1000, json!({"natVal": 1}));
        assert!(compare_exports(&left, &right, &config).is_err());
    }

    #[test]
    fn declaration_and_recursor_fields_remain_exact() {
        let left = complete_export(1, 0, false);
        let mut right = complete_export(1, 1000, true);
        let nodes = std::cell::RefCell::new(CanonicalNodes::default());
        let mut a = Canonicalizer::new(&left, &nodes);
        let mut b = Canonicalizer::new(&right, &nodes);
        let declaration = left.declarations["Nat.sub"].clone();
        let expected = canonical_declaration(&mut a, &declaration).unwrap();
        assert_eq!(
            expected,
            canonical_declaration(&mut b, &right.declarations["Nat.sub"]).unwrap()
        );
        for field in ["kindFlag", "isUnsafe", "numParams"] {
            let mut changed = right.declarations["Nat.sub"].clone();
            changed.data[field] = json!(1);
            assert_ne!(expected, canonical_declaration(&mut b, &changed).unwrap());
        }
        let rule = json!({"ctor": 2, "nfields": 0, "rhs": 0});
        let equivalent = json!({"ctor": 2, "nfields": 0, "rhs": 1000});
        assert_eq!(
            canonical_rule(&mut a, &rule).unwrap(),
            canonical_rule(&mut b, &equivalent).unwrap()
        );
        drop(b);
        right.names.insert(3, name(0, "Other"));
        let mut b = Canonicalizer::new(&right, &nodes);
        for changed in [
            json!({"ctor": 3, "nfields": 0, "rhs": 1000}),
            json!({"ctor": 2, "nfields": 1, "rhs": 1000}),
            json!({"ctor": 2, "nfields": 0, "rhs": 1001}),
        ] {
            assert_ne!(
                canonical_rule(&mut a, &rule).unwrap(),
                canonical_rule(&mut b, &changed).unwrap()
            );
        }
    }

    #[test]
    fn shared_dag_storage_and_dependency_work_are_bounded() {
        // The old canonicalizer expands 26 nodes to 376,752 bytes at depth12.
        // Exercise the same public canonicalization seam at much greater depth.
        let (export, root) = dag(32, 0, false);
        let actual = canonical_expression(&export, root).unwrap();
        assert!(serde_json::to_vec(&actual).unwrap().len() < 50_000);
        let nodes = std::cell::RefCell::new(CanonicalNodes::default());
        let mut context = Canonicalizer::new(&export, &nodes);
        let id = context.expression(root).unwrap();
        assert_eq!(context.completed.len(), export.expressions.len());
        assert_eq!(nodes.borrow().nodes.len(), export.expressions.len());
        assert_eq!(context.expression(root).unwrap(), id);
        assert_eq!(context.completed.len(), export.expressions.len());
        let mut constants = BTreeSet::new();
        let mut completed = HashSet::new();
        export
            .collect_constants(root, &mut constants, &mut completed, &mut HashSet::new())
            .unwrap();
        assert_eq!(constants, BTreeSet::from(["Nat.add".into()]));
        assert_eq!(completed.len(), export.expressions.len());
    }

    #[test]
    fn compact_equality_matches_expansion_across_ids_and_sharing() {
        for depth in 0..7 {
            let (left, a) = dag(depth, 0, false);
            let (mut right, b) = dag(depth, 1000, true);
            assert_eq!(
                compact_equal(&left, a, &right, b).unwrap(),
                reference_expression(&left, a).unwrap() == reference_expression(&right, b).unwrap()
            );
            assert!(compact_equal(&left, a, &right, b).unwrap());
            right.expressions.insert(1000, json!({"natVal": 1}));
            assert_eq!(
                compact_equal(&left, a, &right, b).unwrap(),
                reference_expression(&left, a).unwrap() == reference_expression(&right, b).unwrap()
            );
            assert!(!compact_equal(&left, a, &right, b).unwrap());
        }
    }

    #[test]
    fn every_constructor_and_semantic_field_matches_reference_equality() {
        let (mut export, _) = dag(0, 0, false);
        export.names.insert(3, name(0, "u"));
        export.names.insert(4, name(0, "v"));
        export.levels.extend([
            (1, json!({"succ": 0})),
            (2, json!({"max": [0, 1]})),
            (3, json!({"imax": [0, 1]})),
            (4, json!({"param": 3})),
            (5, json!({"param": 4})),
        ]);
        let mut variants = vec![
            json!({"bvar": 0}),
            json!({"bvar": 1}),
            json!({"natVal": 0}),
            json!({"natVal": 1}),
            json!({"strVal": "a"}),
            json!({"strVal": "b"}),
        ];
        for level in 0..6 {
            variants.push(json!({"sort": level}));
            variants.push(json!({"const": {"name": 2, "us": [level]}}));
        }
        variants.push(json!({"const": {"name": 3, "us": []}}));
        for annotation in ["default", "implicit", "strictImplicit", "instImplicit"] {
            for tag in ["lam", "forallE"] {
                for body in [0, 1] {
                    for ty in [0, 1] {
                        variants.push(
                            json!({tag: {"type": ty, "body": body, "binderInfo": annotation}}),
                        );
                    }
                }
            }
        }
        for a in [0, 1] {
            for b in [0, 1] {
                variants.push(json!({"app": {"fn": a, "arg": b}}));
                for nondep in [false, true] {
                    variants.push(
                        json!({"letE": {"type": a, "value": b, "body": 0, "nondep": nondep}}),
                    );
                }
                variants.push(json!({"proj": {"typeName": 2 + a, "idx": b, "struct": a}}));
            }
        }
        for (i, value) in variants.into_iter().enumerate() {
            export.expressions.insert(10 + i as u64, value);
        }
        let roots: Vec<_> = export
            .expressions
            .keys()
            .copied()
            .filter(|i| *i >= 10)
            .collect();
        let nodes = std::cell::RefCell::new(CanonicalNodes::default());
        let mut context = Canonicalizer::new(&export, &nodes);
        let reference: Vec<_> = roots
            .iter()
            .map(|i| reference_expression(&export, *i).unwrap())
            .collect();
        let compact: Vec<_> = roots
            .iter()
            .map(|i| context.expression(*i).unwrap())
            .collect();
        for i in 0..roots.len() {
            for j in 0..roots.len() {
                assert_eq!(
                    compact[i] == compact[j],
                    reference[i] == reference[j],
                    "roots {} and {}",
                    roots[i],
                    roots[j]
                );
            }
        }
    }

    #[test]
    fn cycles_and_failed_nodes_are_never_cached_as_successes() {
        let (mut export, _) = dag(0, 0, false);
        export.expressions.extend([
            (2, json!({"app": {"fn": 0, "arg": 3}})),
            (3, json!({"app": {"fn": 0, "arg": 2}})),
            (4, json!({"sort": 1})),
            (5, json!({"app": {"fn": 0}})),
            (6, json!({"const": {"name": 2, "us": [9]}})),
        ]);
        export.levels.insert(1, json!({"succ": 1}));
        let nodes = std::cell::RefCell::new(CanonicalNodes::default());
        let mut context = Canonicalizer::new(&export, &nodes);
        for _ in 0..2 {
            for root in [2, 3, 4, 5, 6, 99] {
                assert!(context.expression(root).is_err());
                assert!(
                    !context
                        .completed
                        .contains_key(&(NodeKind::Expression, root))
                );
                assert!(context.active.is_empty());
            }
        }
        assert!(
            export
                .collect_expression_constants(2, &mut BTreeSet::new())
                .is_err()
        );
    }

    #[test]
    fn repeated_universe_dag_is_compact_and_node_kinds_are_distinct() {
        let (mut export, _) = dag(0, 0, false);
        for i in 1..128 {
            export.levels.insert(i, json!({"max": [i - 1, i - 1]}));
        }
        export.expressions.insert(2, json!({"sort": 127}));
        let nodes = std::cell::RefCell::new(CanonicalNodes::default());
        let mut context = Canonicalizer::new(&export, &nodes);
        context.expression(2).unwrap();
        assert_eq!(context.completed.len(), 129);
        assert_eq!(nodes.borrow().nodes.len(), 129);
    }

    #[test]
    fn expression_comparison_ignores_binder_names() {
        let base = Export {
            names: HashMap::from([(0, Value::String("_".into())), (1, name(0, "left"))]),
            levels: HashMap::from([(0, json!({ "zero": true }))]),
            expressions: HashMap::from([
                (0, json!({ "sort": 0 })),
                (
                    1,
                    json!({ "forallE": { "name": 1, "type": 0, "body": 0, "binderInfo": "default" } }),
                ),
            ]),
            declarations: HashMap::new(),
        };
        let renamed = Export {
            names: HashMap::from([(0, Value::String("_".into())), (7, name(0, "right"))]),
            levels: HashMap::from([(0, json!({ "zero": true }))]),
            expressions: HashMap::from([
                (0, json!({ "sort": 0 })),
                (
                    1,
                    json!({ "forallE": { "name": 7, "type": 0, "body": 0, "binderInfo": "default" } }),
                ),
            ]),
            declarations: HashMap::new(),
        };

        assert_eq!(
            canonical_expression(&base, 1).unwrap(),
            canonical_expression(&renamed, 1).unwrap()
        );
    }

    #[test]
    fn lambda_annotations_are_validated_then_normalized() {
        let mut export = Export {
            names: HashMap::new(),
            levels: HashMap::new(),
            expressions: HashMap::from([
                (0, json!({ "bvar": 0 })),
                (
                    1,
                    json!({ "lam": { "type": 0, "body": 0, "binderInfo": "default" } }),
                ),
            ]),
            declarations: HashMap::new(),
        };
        let expected = canonical_expression(&export, 1).unwrap();
        for annotation in ["default", "implicit", "strictImplicit", "instImplicit"] {
            export.expressions.get_mut(&1).unwrap()["lam"]["binderInfo"] = json!(annotation);
            assert_eq!(canonical_expression(&export, 1).unwrap(), expected);
        }
        for invalid in [json!("unknown"), Value::Null, json!(42)] {
            export.expressions.get_mut(&1).unwrap()["lam"]["binderInfo"] = invalid;
            assert!(canonical_expression(&export, 1).is_err());
        }
        export.expressions.get_mut(&1).unwrap()["lam"]
            .as_object_mut()
            .unwrap()
            .remove("binderInfo");
        assert!(canonical_expression(&export, 1).is_err());
    }

    #[test]
    fn axiom_check_follows_a_theorem_body() {
        let names = HashMap::from([
            (0, Value::String("_".into())),
            (1, name(0, "forbidden")),
            (2, name(0, "goal")),
        ]);
        let solution = Export {
            names,
            levels: HashMap::from([(0, json!({ "zero": true }))]),
            expressions: HashMap::from([(0, json!({ "const": { "name": 1, "us": [] } }))]),
            declarations: HashMap::from([
                (
                    "goal".into(),
                    Declaration {
                        kind: "thm".into(),
                        data: json!({ "name": 2, "levelParams": [], "type": 0, "value": 0, "all": [] }),
                    },
                ),
                (
                    "forbidden".into(),
                    Declaration {
                        kind: "axiom".into(),
                        data: json!({ "name": 1, "levelParams": [], "type": 0, "isUnsafe": false }),
                    },
                ),
            ]),
        };
        let config = Config {
            challenge_module: "Challenge".into(),
            solution_module: "Solution".into(),
            theorem_names: vec!["goal".into()],
            definition_names: vec![],
            permitted_axioms: vec![],
            enable_nanoda: false,
            external_kernels: BTreeMap::new(),
        };

        assert!(check_axioms(&solution, &config).is_err());
    }
}
