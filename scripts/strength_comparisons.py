"""Semantic owner of evidence-backed strength-comparison relation metadata.

Corpus statements/results and their existing verifier remain authoritative. This
module validates registrations and produces disposable presentation, not proofs.
"""
from __future__ import annotations

import json
from pathlib import Path
import subprocess
import tempfile

from configuration_explorer import input_digest, input_manifest as configuration_inputs, source_head
from proposition_structure import module_for

PREDICATE = "strength_comparison"
SCHEMA_VERSION = 2
ROLES = {"implication", "delta_forward", "reconstruction", "equivalence", "converse", "allowed_cases", "remainder_identity"}
EXACT_DELTA_ROLES = {"implication", "delta_forward", "reconstruction", "equivalence"}
TRUST = "Trusted live producer; freshness validation is not fresh proof execution. Existing result verifiers remain authoritative."


def string(value, label):
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{label} must be nonempty text")
    return value


def validate_registration(relation, statements, results, arguments, configs=None):
    """Only identity/evidence reference validation; Lean binds complete applications."""
    if relation.get("predicate") != PREDICATE:
        return
    label = relation.get("id", "strength comparison")
    if relation.get("subject_kind") != "statement" or relation.get("object_kind") != "statement":
        raise ValueError(f"{label}: strength comparisons relate statements")
    for field in ("subject_id", "object_id", "delta_statement_id"):
        sid = relation.get(field)
        if sid not in statements or not statements[sid].get("lean_declaration"):
            raise ValueError(f"{label}: {field} needs a known statement with a Lean declaration")
    if "remainder_statement_id" in relation and (relation["remainder_statement_id"] not in statements or not statements[relation["remainder_statement_id"]].get("lean_declaration")):
        raise ValueError(f"{label}: remainder_statement_id needs a known Lean statement")
    background = relation.get("background_statement_ids")
    if not isinstance(background, list) or any(not isinstance(sid, str) for sid in background) or len(set(background)) != len(background) or any(sid not in statements or not statements[sid].get("lean_declaration") for sid in background):
        raise ValueError(f"{label}: background_statement_ids must list distinct known Lean statements in binder order")
    fields = {"stronger", "weaker", "delta"} | {f"background.{i}" for i in range(len(background))}
    if relation.get("remainder_statement_id"):
        fields.add("remainder")
    maps = relation.get("statement_parameter_indices")
    if not isinstance(maps, dict) or set(maps) != fields or any(
        not isinstance(indices, list) or any(type(i) is not int or i < 0 for i in indices)
        or indices != sorted(set(indices)) for indices in maps.values()
    ):
        raise ValueError(f"{label}: statement_parameter_indices must give each field an ordered subsequence of the shared telescope")
    string(relation.get("comparison_spec"), f"{label}: comparison_spec")
    string(relation.get("note"), f"{label}: note")
    for forbidden in ("verified", "status", "strictly_stronger", "strict", "minimal", "unique_delta"):
        if forbidden in relation:
            raise ValueError(f"{label}: {forbidden} is not registration authority; status is derived from checked evidence")
    evidence = relation.get("evidence_result_ids")
    if not isinstance(evidence, dict) or not evidence or set(evidence) - ROLES:
        raise ValueError(f"{label}: evidence_result_ids needs named supported certificate roles")
    if ("allowed_cases" in evidence or "remainder_identity" in evidence) and not relation.get("remainder_statement_id"):
        raise ValueError(f"{label}: remainder certificates need a named remainder_statement_id")
    separator = relation.get("separator")
    if separator is not None:
        if not isinstance(separator, dict):
            raise ValueError(f"{label}: separator must name a setting and result_id")
        string(separator.get("setting"), f"{label}: separator.setting")
        string(separator.get("result_id"), f"{label}: separator.result_id")
    controls = relation.get("explanatory_control_result_ids", [])
    if not isinstance(controls, list) or any(not isinstance(rid, str) for rid in controls) or len(set(controls)) != len(controls):
        raise ValueError(f"{label}: explanatory controls must be distinct result IDs")
    selected = controls + list(evidence.values()) + ([separator["result_id"]] if separator else [])
    for rid in selected:
        if not isinstance(rid, str) or rid not in results:
            raise ValueError(f"{label}: unknown evidence result {rid}")
        result = results[rid]
        if result.get("argument_id") not in arguments:
            raise ValueError(f"{label}: result {rid} has no canonical argument")
        if configs is not None and result.get("theorem") not in configs[rid].get("theorem_names", []):
            raise ValueError(f"{label}: result theorem is not a Comparator obligation: {rid}")


def input_manifest(root):
    """Reuse the existing dependency manifest and include relation interpretation inputs."""
    import hashlib
    manifest = configuration_inputs(root)
    paths = {root / p for p in (
        "scripts/strength_comparisons.py", "scripts/CheckStrength.lean", "scripts/proposition_structure.py", "scripts/PropositionStructure.lean", "scripts/worker_env.py",
    )}
    for kind in ("relations", "inferences", "definitions", "disambiguations", "claims"):
        paths.update((root / "corpus" / kind).glob("*.json"))
    for path in sorted(paths):
        if path.is_symlink() or not path.is_file():
            raise ValueError(f"strength input missing or symlink: {path.relative_to(root)}")
        manifest[path.relative_to(root).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    return dict(sorted(manifest.items()))


def run(root, command, timeout=1200):
    try:
        result = subprocess.run(["python3", "scripts/worker_env.py", "--", *command], cwd=root,
                                text=True, capture_output=True, timeout=timeout)
    except (OSError, subprocess.SubprocessError) as exc:
        raise ValueError(f"strength verification unavailable: {exc}") from exc
    if result.returncode:
        raise ValueError(f"strength verification failed ({command}):\n{result.stdout}\n{result.stderr}")
    return result


def json_tool(root, tool, request):
    with tempfile.NamedTemporaryFile("w", suffix=".json", encoding="utf-8") as handle:
        json.dump(request, handle)
        handle.flush()
        output = run(root, ["lake", "env", "lean", "--run", tool, handle.name])
    try:
        return json.loads(output.stdout)
    except json.JSONDecodeError as exc:
        raise ValueError(f"{tool} did not return JSON: {output.stdout[:500]}") from exc


def context(root, load_dir):
    data = {kind: {r["id"]: r for _, r in load_dir(kind)} for kind in
            ("statements", "results", "arguments", "relations", "definitions", "disambiguations")}
    data["comparisons"] = sorted((r for r in data["relations"].values() if r.get("predicate") == PREDICATE), key=lambda r: r["id"])
    for relation in data["comparisons"]:
        validate_registration(relation, data["statements"], data["results"], data["arguments"])
    selected = {rid for relation in data["comparisons"] for rid in [*relation["evidence_result_ids"].values(), *relation.get("explanatory_control_result_ids", [])]} | {
        relation["separator"]["result_id"] for relation in data["comparisons"] if relation.get("separator")}
    # Reuse the canonical executable-gate contract, including theorem coverage,
    # Challenge/Solution paths, axiom policy and enabled NanoDa.
    from corpus import validate_result_config
    data["configs"] = {rid: validate_result_config(root / "corpus/results" / f"{rid}.json", data["results"][rid], data["arguments"]) for rid in selected}
    for relation in data["comparisons"]:
        validate_registration(relation, data["statements"], data["results"], data["arguments"], data["configs"])
    return data


def checker_request(root, relations, data):
    modules, comparisons = set(), []
    for relation in relations:
        modules.update(data["results"][rid]["solution_module"] for rid in relation.get("explanatory_control_result_ids", []))
        spec = relation["comparison_spec"]
        modules.add(module_for(root, spec))
        certs = []
        for role, rid in sorted(relation["evidence_result_ids"].items()):
            result = data["results"][rid]
            modules.add(result["solution_module"])
            certs.append({"role": role, "theorem": result["theorem"]})
        declarations = {role: data["statements"][relation[field]]["lean_declaration"] for role, field in
                        (("stronger", "subject_id"), ("weaker", "object_id"), ("delta", "delta_statement_id"))}
        declarations["background"] = [data["statements"][sid]["lean_declaration"] for sid in relation["background_statement_ids"]]
        if relation.get("remainder_statement_id"):
            declarations["remainder"] = data["statements"][relation["remainder_statement_id"]].get("lean_declaration")
        item = {"id": relation["id"], "specification": spec, "certificates": certs, "statement_declarations": declarations, "statement_parameter_indices": relation["statement_parameter_indices"]}
        if relation.get("separator"):
            setting = relation["separator"]["setting"]
            result = data["results"][relation["separator"]["result_id"]]
            modules.update((module_for(root, setting), result["solution_module"]))
            item["separator"] = {"setting": setting, "theorem": result["theorem"]}
        comparisons.append(item)
    return {"modules": sorted(modules), "comparisons": comparisons}


def projection(relation, data, binding=None, *, verified=False):
    """Only checked roles produce claims; a sufficient condition is never exact content."""
    if verified:
        validate_binding(relation, data, binding)
    evidence = relation["evidence_result_ids"]
    roles = set(evidence) if verified else set()
    strict = "implication" in roles and relation.get("separator") is not None
    equivalent = {"implication", "converse"} <= roles
    if strict and equivalent:
        raise ValueError(f"{relation['id']}: contradictory converse and separating evidence")
    exact = EXACT_DELTA_ROLES <= roles
    if exact and binding and binding.get("delta_degenerate"):
        raise ValueError(f"{relation['id']}: delta is definitionally S or W → S, excluded by the definitional degeneracy guard; explanatory usefulness is not certified")
    obligations = []
    bound_by_role = {c["role"]: c for c in (binding or {}).get("certificates", [])}
    for role, rid in sorted(evidence.items()):
        result = data["results"][rid]
        obligations.append({**bound_by_role.get(role, {}), "role": role, "result_id": rid, "argument_id": result["argument_id"], "theorem": result["theorem"], "verified": verified,
                            "permitted_axioms": data.get("configs", {}).get(rid, {}).get("permitted_axioms", [])})
    statement_ids = {relation["subject_id"], relation["object_id"], relation["delta_statement_id"], *relation["background_statement_ids"]}
    if relation.get("remainder_statement_id"):
        statement_ids.add(relation["remainder_statement_id"])
    definitions = [d for d in data["definitions"].values() if any(d["id"] in data["statements"][sid].get("definition_ids", []) for sid in statement_ids)]
    definition_ids = {d["id"] for d in definitions}
    disambiguations = [d for d in data["disambiguations"].values() if definition_ids.intersection(d.get("sense_definition_ids", [])) or any(d["id"] in data["statements"][sid].get("disambiguation_ids", []) for sid in statement_ids)]
    report = {"id": relation["id"], "stronger_statement_id": relation["subject_id"], "weaker_statement_id": relation["object_id"],
              "delta_statement_id": relation["delta_statement_id"], "background_statement_ids": relation["background_statement_ids"],
              "comparison_spec": relation["comparison_spec"], "note": relation["note"], "verified": verified,
              "comparison_status": "strict strengthening" if strict else "proved equivalence" if equivalent else "proved implication" if "implication" in roles else "unresolved",
              "converse_status": "refuted by separating setting" if strict else "proved" if "converse" in roles else "unresolved",
              "delta_status": "exact factorization proved" if exact else "sufficient only; exactness unresolved" if "reconstruction" in roles else "unresolved",
              "explanatory_controls": [{"result_id": rid, "argument_id": data["results"][rid]["argument_id"], "theorem": data["results"][rid]["theorem"], "description": data["results"][rid]["description"]} for rid in relation.get("explanatory_control_result_ids", [])],
              "explanatory_status": "reviewed interpretation; informative explanation is not certified by factorization",
              "obligations": obligations, "binding": binding, "remaining_obligations": sorted(EXACT_DELTA_ROLES - roles),
              "definitions": definitions, "disambiguations": disambiguations,
              "scope_notes": ["Comparison is under the displayed shared background and vocabulary, not the entire theorem environment.",
                              "Exact factorization S ↔ (W ∧ D) does not certify that D is informative: even S ∧ True can be an exact factorization.",
                              "The degeneracy guard detects only definitional matches to S or W → S; a negative check proves no semantic nonredundancy.",
                              "A checked separating instance refutes the general converse under this comparison, not the converse for every fixed domain or interpretation. Current examples use Type 0; closed settings need not use universe zero.",
                              "D is a proposed additional requirement; W ∧ ¬S denotes cases admitted only by W. They are distinct roles.",
                              "No unique or minimal delta is claimed. Proof-term use does not establish premise necessity.",
                              "The artifact is derived presentation; corpus results, Comparator and NanoDa remain the proof authorities."]}
    if relation.get("remainder_statement_id"):
        report["remainder_statement_id"] = relation["remainder_statement_id"]
        report["remainder_status"] = "exact admitted-only remainder proved" if {"allowed_cases", "remainder_identity"} <= roles else "unresolved"
    if relation.get("separator"):
        result = data["results"][relation["separator"]["result_id"]]
        report["separator"] = {**relation["separator"], **((binding or {}).get("separator") or {}), "theorem": result["theorem"], "verified": verified}
    if verified:
        report["provenance"] = {"result_ids": sorted(set(evidence.values()) | ({relation["separator"]["result_id"]} if relation.get("separator") else set())),
                                "bind_check": "bound", "semantic_binding": "definitional equality", "comparator": "passed"}
    return report


def validate_binding(relation, data, binding):
    """Refuse incomplete checker responses; equality itself remains Lean's job."""
    if not isinstance(binding, dict) or binding.get("bound") is not True or binding.get("id") != relation["id"] or binding.get("specification") != relation["comparison_spec"]:
        raise ValueError(f"{relation['id']}: complete theorem application/background mismatch: {binding}")
    certificates = binding.get("certificates", [])
    expected = relation["evidence_result_ids"]
    if len(certificates) != len(expected) or {c.get("role") for c in certificates} != set(expected):
        raise ValueError(f"{relation['id']}: incomplete certificate role bindings")
    for certificate in certificates:
        if certificate.get("bound") is not True or certificate.get("theorem") != data["results"][expected[certificate["role"]]]["theorem"]:
            raise ValueError(f"{relation['id']}: mismatched certificate arguments/theorem")
    declarations = {role: data["statements"][relation[field]]["lean_declaration"] for role, field in
                    (("stronger", "subject_id"), ("weaker", "object_id"), ("delta", "delta_statement_id"))}
    declarations.update({f"background.{i}": data["statements"][sid]["lean_declaration"] for i, sid in enumerate(relation["background_statement_ids"])})
    if relation.get("remainder_statement_id"):
        declarations["remainder"] = data["statements"][relation["remainder_statement_id"]]["lean_declaration"]
    fields = binding.get("field_bindings", [])
    if len(fields) != len(declarations) or {f.get("role") for f in fields} != set(declarations):
        raise ValueError(f"{relation['id']}: incomplete statement/background bindings")
    for field in fields:
        if field.get("bound") is not True or field.get("declaration") != declarations[field["role"]] or field.get("parameter_indices") != relation["statement_parameter_indices"][field["role"]] or not field.get("expected_application"):
            raise ValueError(f"{relation['id']}: mismatched statement/background binding")
    if relation.get("separator"):
        separator = binding.get("separator", {})
        if separator.get("bound") is not True or separator.get("setting") != relation["separator"]["setting"] or separator.get("theorem") != data["results"][relation["separator"]["result_id"]]["theorem"]:
            raise ValueError(f"{relation['id']}: unsupported strictness without same-background separating application")


def verify(root, data, relations):
    """Fresh producer: build, bind full applications, then existing result verification."""
    from corpus import bind_result, bind_tool_input
    request = checker_request(root, relations, data)
    if not relations:
        return []
    run(root, ["lake", "build", *request["modules"]])
    ids = sorted({rid for relation in relations for rid in [*relation["evidence_result_ids"].values(), *relation.get("explanatory_control_result_ids", [])]} |
                 {relation["separator"]["result_id"] for relation in relations if relation.get("separator")})
    selected = [(root / "corpus/results" / f"{rid}.json", data["results"][rid]) for rid in ids]
    described = json_tool(root, "scripts/BindTypes.lean", bind_tool_input(selected))
    by_theorem = {d["theorem"]: d for d in described}
    statement_index = {sid: (root / "corpus/statements" / f"{sid}.json", statement) for sid, statement in data["statements"].items()}
    for _, result in selected:
        bound = bind_result(result, data["arguments"][result["argument_id"]], statement_index, by_theorem.get(result["theorem"], {"error": "missing theorem"}))
        if bound["status"] != "bound":
            raise ValueError(f"{result['id']}: canonical result binding failed: {bound}")
    bindings = json_tool(root, "scripts/CheckStrength.lean", request)
    if not isinstance(bindings, list) or {b.get("id") for b in bindings} != {r["id"] for r in relations}:
        raise ValueError("strength semantic checker did not cover the selected comparisons")
    indexed = {b["id"]: b for b in bindings}
    for relation in relations:
        binding = indexed[relation["id"]]
        validate_binding(relation, data, binding)
        # Reject degenerate explanatory claims before spending time in the verifier.
        projection(relation, data, binding, verified=True)
    # Reuse the preceding inspector instead of inventing another formula AST.
    from proposition_structure import run_extractor
    relevant = {}
    for relation in relations:
        sids = [relation["subject_id"], relation["object_id"], relation["delta_statement_id"], *relation["background_statement_ids"]]
        if relation.get("remainder_statement_id"):
            sids.append(relation["remainder_statement_id"])
        relevant[relation["id"]] = list(dict.fromkeys([relation["comparison_spec"], *[data["statements"][sid]["lean_declaration"] for sid in sids]]))
    declarations = sorted({name for names in relevant.values() for name in names})
    structures = run_extractor(root, {"modules": request["modules"], "declarations": declarations,
                                     "unfold": [name for name in declarations if name.startswith("TruthCore.")]})
    structure_index = {description["declaration"]: description for description in structures}
    for relation in relations:
        indexed[relation["id"]]["structure"] = [structure_index[name] for name in relevant[relation["id"]]]
    for rid in ids:
        run(root, ["scripts/verify-result.sh", rid])
    return [projection(relation, data, indexed[relation["id"]], verified=True) for relation in relations]


def write_bundle(root, path, data):
    if path.is_symlink() or (root / ".cache").is_symlink() or not path.resolve().is_relative_to((root / ".cache").resolve()):
        raise ValueError("strength output must be a regular file inside the clone .cache")
    before = input_manifest(root)
    reports = verify(root, data, data["comparisons"])
    after = input_manifest(root)
    if before != after:
        raise ValueError("strength inputs changed during verification; discard and rerun")
    bundle = {"schema_version": SCHEMA_VERSION, "producer": {"mode": "live-verified", "source_head": source_head(root),
              "input_digest": input_digest(after), "inputs": after, "trust": TRUST}, "comparisons": reports}
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", dir=path.parent, encoding="utf-8", delete=False) as handle:
        temporary = Path(handle.name)
        json.dump(bundle, handle, ensure_ascii=False, sort_keys=True)
        handle.write("\n")
    try:
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)
    return bundle


def read_bundle(root, path, data):
    """Validate a trusted producer artifact, never infer fresh verification from hashes."""
    if path.is_symlink():
        raise ValueError("strength report symlinks are unsupported")
    bundle = json.loads(path.read_text())
    producer = bundle.get("producer", {})
    if bundle.get("schema_version") != SCHEMA_VERSION or producer.get("mode") != "live-verified" or producer.get("trust") != TRUST:
        raise ValueError("invalid strength report producer/schema")
    manifest = input_manifest(root)
    if producer.get("inputs") != manifest or producer.get("input_digest") != input_digest(manifest):
        raise ValueError("stale strength report: current dependency inputs differ")
    reports = bundle.get("comparisons")
    if not isinstance(reports, list) or [r.get("id") for r in reports] != [r["id"] for r in data["comparisons"]]:
        raise ValueError("strength report does not cover exact registered comparisons")
    for relation, actual in zip(data["comparisons"], reports):
        binding = actual.get("binding")
        validate_binding(relation, data, binding)
        if actual != projection(relation, data, binding, verified=True):
            raise ValueError(f"{relation['id']}: strength projection differs from canonical evidence references")
    return bundle
