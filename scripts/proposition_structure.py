"""Derived elaborated-expression presentation; never a proof or identity registry."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
from typing import Any

SCHEMA_VERSION = 1
CORPUS_KINDS = ("statements", "definitions", "disambiguations", "arguments", "results", "relations", "claims", "inferences")
FIRST_SLICE = (
    "STMT-CAUSE-PRINCIPLE-BROAD",
    "STMT-CAUSE-PRINCIPLE-DISTINCT",
    "STMT-GOD-HAS-CLASSICAL-DIVINE-ATTRIBUTES",
    "STMT-CLASSICAL-ATTRIBUTES-SUFFICE",
)
NOTES = [
    "Derived presentation of elaborated Lean expressions, not proof support or semantic equivalence.",
    "Unfolding is explicit, one project declaration at a time. Named library boundaries remain named.",
    "A primitive parameter or field is intentional vocabulary; an unsupported node is an extraction limitation. Neither supplies an independent-atom semantics.",
    "Disjunction preserves alternatives and selects no branch. Structural presentation discharges no root premise.",
]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module_for(root: Path, declaration: str) -> str:
    """Discover the source module; Lean still resolves and validates the name.

    Namespaces need not match file names (Catholicism lives in Root/StageTwo).
    This small source locator follows the explorer's lean-source.ts conventions;
    it is not a parser or a semantic binding authority.
    """
    candidates = []
    header = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*(?:def|abbrev|theorem|lemma|structure|inductive|class|opaque|axiom|instance)\s+([^\s(:{\[]+)")
    for path in sorted((root / "TruthCore").rglob("*.lean")):
        namespaces = []
        comment_depth = 0
        for line in path.read_text().splitlines():
            was_comment = comment_depth > 0
            comment_depth = max(0, comment_depth + line.count("/-") - line.count("-/"))
            if was_comment or comment_depth:
                continue
            line = line.strip()
            match = re.match(r"namespace\s+(\S+)", line)
            if match:
                namespaces.append(match[1])
                continue
            match = re.match(r"end\s+(\S+)", line)
            if match and namespaces and namespaces[-1] == match[1]:
                namespaces.pop()
                continue
            match = header.match(line)
            if match:
                local = match[1]
                name = local[7:] if local.startswith("_root_.") else ".".join(namespaces + [local])
                if declaration == name or declaration.startswith(name + "."):
                    candidates.append((len(name), path))
    if not candidates:
        raise ValueError(f"cannot locate project module for {declaration}")
    best = max(length for length, _ in candidates)
    paths = {path for length, path in candidates if length == best}
    if len(paths) != 1:
        raise ValueError(f"ambiguous source module for {declaration}: {sorted(map(str, paths))}")
    return str(paths.pop().relative_to(root).with_suffix("")).replace("/", ".")


def project_sources(root: Path, modules: list[str]) -> list[Path]:
    pending, found = list(modules), set()
    while pending:
        module = pending.pop()
        path = root / (module.replace(".", "/") + ".lean")
        if module in found or not path.is_file() or not module.startswith("TruthCore."):
            continue
        found.add(module)
        pending.extend(re.findall(r"^(?:public\s+)?import\s+(\S+)", path.read_text(), re.M))
    return sorted(root / (m.replace(".", "/") + ".lean") for m in found)


def input_manifest(root: Path, modules: list[str], records: dict[str, list[tuple[Path, dict]]]) -> list[dict]:
    # Canonical frontier transcription classification can inspect any Solution.lean.
    paths = set((root / "TruthCore").rglob("*.lean"))
    paths.update(project_sources(root, modules))
    paths.update(root / p for p in ("lean-toolchain", "lake-manifest.json", "scripts/PropositionStructure.lean", "scripts/proposition_structure.py", "scripts/corpus.py", "scripts/worker_env.py", "lakefile.toml"))
    for values in records.values():
        paths.update(path for path, _ in values)
    return [{"path": str(p.relative_to(root)), "sha256": digest(p)} for p in sorted(paths) if p.is_file()]


def run_extractor(root: Path, request: dict) -> list[dict]:
    # Lake owns compiled/source freshness, including transitive dependencies.
    built = subprocess.run(["python3", "scripts/worker_env.py", "--", "lake", "build", *request["modules"]],
                           cwd=root, capture_output=True, text=True, timeout=600)
    if built.returncode:
        raise ValueError(f"structure module build failed: {built.stderr.strip() or built.stdout.strip()}")
    with tempfile.NamedTemporaryFile("w", suffix=".json") as handle:
        json.dump(request, handle)
        handle.flush()
        completed = subprocess.run(
            ["python3", "scripts/worker_env.py", "--", "lake", "env", "lean", "--run", "scripts/PropositionStructure.lean", handle.name],
            cwd=root, capture_output=True, text=True, timeout=180,
        )
    if completed.returncode:
        raise ValueError(f"structure extraction failed: {completed.stderr.strip() or completed.stdout.strip()}")
    try:
        output = json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise ValueError(f"structure extractor returned invalid JSON: {completed.stdout[:500]}") from exc
    if not isinstance(output, list) or any(not isinstance(row, dict) or "declaration" not in row or "error" in row for row in output):
        raise ValueError(f"structure extractor returned invalid declarations: {output}")
    return output


def nodes(value: Any):
    if isinstance(value, dict):
        if "id" in value and "kind" in value:
            yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


def semantic_links(statement: dict, declarations: list[dict], definitions: list[dict], disambiguations: list[dict]) -> dict:
    expression_nodes = list(nodes(declarations))
    names = {n["declaration"] for n in expression_nodes if n.get("declaration")}
    definitions = [dict(d, expression_ids=[n["id"] for n in expression_nodes if d.get("lean_declaration") and n.get("declaration") == d["lean_declaration"]])
                   for d in definitions if d["id"] in statement.get("definition_ids", []) or d.get("lean_declaration") in names]
    ids = {d["id"] for d in definitions}
    disambiguations = [d for d in disambiguations if d["id"] in statement.get("disambiguation_ids", []) or ids.intersection(d.get("sense_definition_ids", []))]
    disambiguations = [dict(d, expression_ids=sorted({node_id for definition in definitions if definition["id"] in d.get("sense_definition_ids", []) for node_id in definition["expression_ids"]})) for d in disambiguations]
    return {"definitions": definitions, "disambiguations": disambiguations}


def build_reports(root: Path, records: dict[str, list[tuple[Path, dict]]], statement_ids: list[str], unfold: list[str], frontier: dict, runner=run_extractor) -> dict:
    statements = {r["id"]: r for _, r in records["statements"]}
    definitions = [r for _, r in records["definitions"]]
    selected = []
    requested = set(unfold)
    for sid in statement_ids:
        if sid not in statements:
            raise ValueError(f"unknown statement: {sid}")
        statement = statements[sid]
        if not statement.get("lean_declaration"):
            raise ValueError(f"{sid} has no Lean declaration; extraction unavailable (binding remains authoritative)")
        selected.append(statement)
    declaration_names = {s["lean_declaration"] for s in selected} | requested
    # Include linked semantic boundary declarations as separately inspectable types.
    definition_ids = {d for s in selected for d in s.get("definition_ids", [])}
    declaration_names.update(d["lean_declaration"] for d in definitions if d["id"] in definition_ids and d.get("lean_declaration", "").startswith("TruthCore."))
    if any(not n.startswith("TruthCore.") for n in requested):
        raise ValueError("only project-owned TruthCore definitions may be unfolded")
    modules = sorted({module_for(root, n) for n in declaration_names})
    request = {"modules": modules, "declarations": sorted(declaration_names), "unfold": sorted(requested)}
    manifest = input_manifest(root, modules, records)
    request_hash = hashlib.sha256(json.dumps({"request": request, "inputs": manifest}, sort_keys=True).encode()).hexdigest()
    try:
        raw = runner(root, request)
    except subprocess.TimeoutExpired as exc:
        raise ValueError("structure extraction timed out; inspect the built modules and retry") from exc
    # Refuse a report if inputs were edited while Lean was running.
    if manifest != input_manifest(root, modules, records):
        raise ValueError("structure inputs changed during extraction; retry")
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    built_inputs = [{"path": str(path.relative_to(root)), "sha256": digest(path)} for module in modules
                    if (path := root / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")).is_file()]
    reports = []
    arguments = [r for _, r in records["arguments"]]
    results = [r for _, r in records["results"]]
    for statement in selected:
        sid = statement["id"]
        root_name = statement["lean_declaration"]
        root_description = next((row for row in raw if row["declaration"] == root_name), None)
        if root_description is None:
            raise ValueError(f"extractor omitted requested declaration {root_name}")
        linked_names = {d.get("lean_declaration") for d in definitions if d["id"] in statement.get("definition_ids", [])}
        referenced_names = {n.get("declaration") for n in nodes(root_description)}
        referenced_names.update(r.get("declaration") for r in root_description.get("references", []))
        chosen = [root_description] + [row for row in raw if row["declaration"] != root_name and row["declaration"] in linked_names | referenced_names]
        scoped = json.loads(json.dumps(chosen))
        prefix = f"{sid}@{request_hash[:16]}:"
        for node in nodes(scoped):
            node["id"] = prefix + node["id"]
            if node.get("binding"):
                node["binding"] = prefix + node["binding"]
        related_args = [a for a in arguments if sid in a.get("premise_statement_ids", []) or sid == a.get("conclusion_statement_id")]
        arg_ids = {a["id"] for a in related_args}
        links = semantic_links(statement, scoped, definitions, [r for _, r in records["disambiguations"]])
        related_names = {d["lean_declaration"] for d in links["definitions"] if d.get("lean_declaration")}
        related = [{"statement_id": s["id"], "lean_declaration": s.get("lean_declaration"), "paraphrase": s["paraphrase"],
                    "frontier_status": frontier.get("closed_statements", {}).get(s["id"], "open")}
                   for s in statements.values() if s.get("lean_declaration") in related_names]
        reports.append({"statement_id": sid, "lean_declaration": statement["lean_declaration"],
                        "revision": {"head": head, "input_digest": request_hash, "inputs": manifest, "request": request, "built_inputs": built_inputs},
                        "declarations": scoped, "semantic_links": links,
                        "support": {"arguments": related_args, "results": [r for r in results if r["argument_id"] in arg_ids], "related_statements": related},
                        "coverage_notes": NOTES})
    return {"schema_version": SCHEMA_VERSION, "reports": reports}


def check_artifact(root: Path, artifact: dict) -> None:
    if artifact.get("schema_version") != SCHEMA_VERSION or not artifact.get("reports"):
        raise ValueError("invalid structure artifact schema")
    for report in artifact["reports"]:
        revision = report["revision"]
        saved_corpus = {item["path"] for item in revision["inputs"] if item["path"].startswith("corpus/")}
        if saved_corpus:
            current_corpus = {str(path.relative_to(root)) for kind in CORPUS_KINDS for path in (root / "corpus" / kind).glob("*.json")}
            if saved_corpus != current_corpus:
                raise ValueError("stale structure artifact corpus inventory")
        saved_lean = {item["path"] for item in revision["inputs"] if item["path"].startswith("TruthCore/") and item["path"].endswith(".lean")}
        if saved_lean and saved_lean != {str(path.relative_to(root)) for path in (root / "TruthCore").rglob("*.lean")}:
            raise ValueError("stale structure artifact Lean source inventory")
        for item in revision["inputs"]:
            path = root / item["path"]
            if not path.is_file() or digest(path) != item["sha256"]:
                raise ValueError(f"stale structure artifact input: {item['path']}")
        expected = hashlib.sha256(json.dumps({"request": revision["request"], "inputs": revision["inputs"]}, sort_keys=True).encode()).hexdigest()
        if expected != revision["input_digest"]:
            raise ValueError("invalid structure artifact input digest")
