#!/usr/bin/env python3
"""Batch certification helper: one TOML spec -> all corpus records, and a frozen
Challenge generated from a Solution module (owner decision 2026-11-07).

    python3 scripts/argument_batch.py records SPEC.toml [--write] [--fix]
    python3 scripts/argument_batch.py challenge SOLUTION.lean THEOREM... [--write]
    python3 scripts/argument_batch.py map MAP.toml [--mermaid]

`map` checks an exploration map (explorations/*.toml): the whole argument DAG
proposed for a target in one pass. Nodes are existing statement IDs or new
candidates (`new = true` with `text`); edges name premises, a conclusion, a kind
(`derivation`, `source`, `bridge`, `rival`) and a status (`mapped`,
`certified`, `rejected`). It reports unknown IDs, new nodes, and which edges are
already certified by an existing argument with the same conclusion.

Identity (owner decision 2026-11-07): ids are opaque uuids. A spec names
records by handle: a uuid, or the legacy id (`STMT-…`) or label of an existing
record. A handle that names no record makes a new one with a uuid4 id and the
label `label = "..."` (default: the handle, which must then be a plain name
with no id-like text); a rerun finds it again by that label. New files are
`corpus/<kind>/<uuid>.json` and `results/<uuid>/comparator.json`. Existing
specs and exploration maps keep their legacy handles, which resolve.

`records` writes statements, inferences, arguments, results, comparator configs
and relations named by the spec. Missing `definition_ids` / `disambiguation_ids`
of an argument default to the union of those of its premises and conclusion
(existing corpus statements or statements of the same spec). It refuses to
overwrite an existing record with a different body. `--fix` then runs
`corpus.py check` and adds every disambiguation the check reports as missing
from a spec argument, until the check passes or no such error remains.

`challenge` turns a Solution module into the ordinary (non-module) Challenge
file next to it: `public import` becomes `import`, `module` and
`@[expose] public section` are dropped, `open` lines and the namespace are kept,
only the named theorems are kept, and each keeps its exact signature with the
proof replaced by `sorry`. Every other declaration of the Solution (helper
lemmas, sections, controls proofs not named) is omitted.

The spec format:

    [batch]
    vocab = "TruthCore.Causality.Foo"           # prefix for relative `lean` names
    results = "TruthCore.Results.Causality.Foo"  # Challenge/Solution module prefix
    definitions = []                             # added to every argument
    disambiguations = []

    [[statement]]
    id = "..."                   # handle: uuid, legacy id or label; new: any handle
    label = "Act is PRIOR_1 to potency"   # required for a new record unless the handle is the label
    lean = "FooReading"          # relative to batch.vocab unless it starts with TruthCore.
    paraphrase = "..."
    definitions = ["DEF-..."]
    disambiguations = ["DISAMB-..."]

    [[argument]]
    id = "..."
    label = "Act is PRIOR_1 to potency, from the priority fork"
    theorem = "fooFromBar"       # in batch.results
    premises = ["STMT-..."]
    conclusion = "STMT-..."
    rule = "..."
    meaning = "..."              # also the result description

    [[relation]]
    id = "..."
    label = "..."
    subject_kind = "argument"
    subject_id = "FOO-FROM-BAR"
    predicate = "refutes"
    object_kind = "statement"
    object_id = "STMT-..."
    note = "..."
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tomllib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from corpus_ids import Aliases, AmbiguousId, idlike_text, new_uuid  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "corpus"


def load_ids(kind: str) -> dict[str, tuple[Path, dict]]:
    out = {}
    for path in sorted((CORPUS / kind).glob("*.json")):
        record = json.loads(path.read_text())
        out[record["id"]] = (path, record)
    return out


def dump(path: Path, record: dict, write: bool, planned: list[str]) -> None:
    text = json.dumps(record, indent=2, ensure_ascii=False) + "\n"
    if path.exists() and path.read_text() == text:
        return
    if path.exists():
        existing = json.loads(path.read_text())
        if existing.get("id") != record.get("id"):
            raise SystemExit(f"refusing to overwrite {path}: it holds {existing.get('id')}")
    planned.append(str(path.relative_to(ROOT)))
    if write:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)


def lean_name(batch: dict, name: str) -> str:
    return name if name.startswith("TruthCore.") else f"{batch['vocab']}.{name}"


class Handles:
    """Spec handles -> uuids (uuid identity, owner decision 2026-11-07).

    A spec names records by handle: a uuid, the legacy id or label of an
    existing record, or a new handle. A new record gets a uuid4 and the label
    `label` (default: the handle), and a rerun finds it again by that label,
    so `records --write` is idempotent without writing ids back into the spec.
    Readable handles are never ids."""

    def __init__(self) -> None:
        self.aliases = Aliases.load(ROOT)
        self.minted: dict[tuple[str, str], str] = {}

    def existing(self, kind: str, *tokens: str | None) -> str | None:
        for token in tokens:
            if token:
                try:
                    found = self.aliases.resolve(token, (kind,))
                except AmbiguousId as exc:
                    raise SystemExit(str(exc)) from exc
                if found:
                    return found
        return None

    def get(self, kind: str, handle: str, label: str | None = None) -> str:
        key = (kind, handle)
        if key not in self.minted:
            found = self.existing(kind, handle, label)
            if found is None and idlike_text(label or handle):
                raise SystemExit(f"new {kind} {handle!r} needs a label: a plain name with no id-like text "
                                 "(set `label` in the spec)")
            self.minted[key] = found or new_uuid()
        return self.minted[key]

    def ref(self, kind: str, handle: str) -> str:
        """A reference: a handle of this spec, else an existing record."""
        if (kind, handle) in self.minted:
            return self.minted[(kind, handle)]
        found = self.existing(kind, handle)
        if found is None:
            raise SystemExit(f"unknown {kind} {handle}")
        return found


def record_path(existing: dict[str, tuple[Path, dict]], directory: str, record_id: str) -> Path:
    return existing.get(record_id, (CORPUS / directory / f"{record_id}.json",))[0]


def identity(record_id: str, label: str, existing: dict[str, tuple[Path, dict]]) -> dict:
    """id, label and (for a migrated record) legacy_id, as the record has them."""
    old = existing.get(record_id, (None, {}))[1]
    out = {"id": record_id, "label": old.get("label", label)}
    if "legacy_id" in old:
        out["legacy_id"] = old["legacy_id"]
    return out


def build_records(spec: dict, write: bool) -> list[str]:
    batch = spec["batch"]
    planned: list[str] = []
    existing = {kind: load_ids(kind) for kind in ("statements", "arguments", "inferences", "results", "relations")}
    handles = Handles()
    for s in spec.get("statement", []):
        handles.get("statement", s["id"], s.get("label"))
    for a in spec.get("argument", []):
        handles.get("argument", a["id"], a.get("label"))
    spec_statements = {handles.ref("statement", s["id"]): s for s in spec.get("statement", [])}

    def refs(kind: str, handles_: list[str]) -> list[str]:
        return [handles.ref(kind, handle) for handle in handles_]

    for s in spec.get("statement", []):
        sid = handles.ref("statement", s["id"])
        record = {**identity(sid, s.get("label") or s["id"], existing["statements"]), "paraphrase": s["paraphrase"]}
        if "lean" in s:
            record["lean_declaration"] = lean_name(batch, s["lean"])
        if s.get("definitions"):
            record["definition_ids"] = refs("definition", s["definitions"])
        if s.get("disambiguations"):
            record["disambiguation_ids"] = refs("disambiguation", s["disambiguations"])
        dump(record_path(existing["statements"], "statements", sid), record, write, planned)

    def senses(statement_id: str, key: str) -> list[str]:
        if statement_id in spec_statements:
            kind = key[:-1]
            return refs(kind, spec_statements[statement_id].get(key, []))
        if statement_id in existing["statements"]:
            return existing["statements"][statement_id][1].get(f"{key[:-1]}_ids", [])
        raise SystemExit(f"unknown statement {statement_id}")

    for a in spec.get("argument", []):
        aid = handles.ref("argument", a["id"])
        label = existing["arguments"].get(aid, (None, {}))[1].get("label") or a.get("label") or a["id"]
        premises = refs("statement", a["premises"])
        conclusion = handles.ref("statement", a["conclusion"])
        ids = premises + [conclusion]
        # Sorted by legacy id, else uuid (corpus_ids.order_key), as before the migration.
        definitions = (refs("definition", a["definitions"]) if a.get("definitions") else sorted(
            {d for i in ids for d in senses(i, "definitions")} | set(refs("definition", batch.get("definitions", []))),
            key=handles.aliases.legacy))
        disambiguations = (refs("disambiguation", a["disambiguations"]) if a.get("disambiguations") else sorted(
            {d for i in ids for d in senses(i, "disambiguations")}
            | set(refs("disambiguation", batch.get("disambiguations", []))), key=handles.aliases.legacy))
        old_argument = existing["arguments"].get(aid, (None, {}))[1]
        iid = (old_argument.get("inference_ids") or [None])[0] or handles.get("inference", f"{label} (inference)",
                                                                               f"{label} (inference)")
        inference = {**identity(iid, f"{label} (inference)", existing["inferences"]),
                     "input_statement_ids": premises, "output_statement_id": conclusion, "rule": a["rule"],
                     "meaning": a["meaning"], "assumption_statement_ids": [], "discharged_statement_ids": []}
        argument = {**identity(aid, label, existing["arguments"]), "premise_statement_ids": premises,
                    "conclusion_statement_id": conclusion, "inference_ids": [iid], "meaning": a["meaning"]}
        if definitions:
            argument["definition_ids"] = definitions
        if disambiguations:
            argument["disambiguation_ids"] = disambiguations
        if "strong_version_needed" in a:
            argument["strong_version_needed"] = {handles.ref("statement", key): value
                                                 for key, value in a["strong_version_needed"].items()}
        if "commitment_statement_ids" in a:
            argument["commitment_statement_ids"] = refs("statement", a["commitment_statement_ids"])
        if aid in existing["arguments"]:
            argument = {**old_argument, **{k: v for k, v in argument.items() if k not in ("disambiguation_ids",)}}
        rid = handles.get("result", a["id"], label)
        result_identity = identity(rid, label, existing["results"])
        comparator = f"results/{result_identity.get('legacy_id', rid)}/comparator.json"
        result = {**result_identity, "argument_id": aid, "challenge_module": f"{batch['results']}.Challenge",
                  "solution_module": f"{batch['results']}.Solution", "theorem": f"{batch['results']}.{a['theorem']}",
                  "comparator_config": comparator, "status": "solution-present", "description": a["meaning"]}
        if "transcription" in a:
            result["transcription"] = a["transcription"]
        dump(record_path(existing["inferences"], "inferences", iid), inference, write, planned)
        dump(record_path(existing["arguments"], "arguments", aid), argument, write, planned)
        dump(record_path(existing["results"], "results", rid), result, write, planned)
        dump(ROOT / comparator, {"challenge_module": result["challenge_module"],
                                 "solution_module": result["solution_module"],
                                 "theorem_names": [result["theorem"]], "permitted_axioms": a.get("axioms", []),
                                 "enable_nanoda": True}, write, planned)

    for r in spec.get("relation", []):
        rel_id = handles.get("relation", r["id"], r.get("label"))
        record = {**identity(rel_id, r.get("label") or r["id"], existing["relations"]),
                  "subject_kind": r["subject_kind"], "subject_id": handles.ref(r["subject_kind"], r["subject_id"]),
                  "predicate": r["predicate"], "object_kind": r["object_kind"],
                  "object_id": handles.ref(r["object_kind"], r["object_id"])}
        for key in ("verification_result_id", "strictness_result_id"):
            if key in r:
                record[key] = handles.ref("result", r[key])
        if "note" in r:
            record["note"] = r["note"]
        dump(record_path(existing["relations"], "relations", rel_id), record, write, planned)
    return planned


MISSING = re.compile(r"corpus error: (\S+): .*does not link ([0-9a-f-]{36})")


def fix_disambiguations(spec: dict) -> int:
    handles = Handles()
    ours = set()
    for a in spec.get("argument", []):
        found = handles.existing("argument", a["id"], a.get("label"))
        if found:
            path = load_ids("arguments")[found][0]
            ours.add(str(path.relative_to(ROOT)))
    for _ in range(50):
        check = subprocess.run([sys.executable, str(ROOT / "scripts" / "corpus.py"), "check"],
                               cwd=ROOT, capture_output=True, text=True)
        errors = [line for line in (check.stdout + check.stderr).splitlines() if line.startswith("corpus error")]
        fixable = [m for m in map(MISSING.match, errors) if m and m.group(1) in ours]
        if not fixable:
            print("\n".join(errors) if errors else "corpus check: ok")
            return 1 if errors else 0
        path = ROOT / fixable[0].group(1)
        record = json.loads(path.read_text())
        record.setdefault("disambiguation_ids", []).append(fixable[0].group(2))
        path.write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n")
        print(f"added {fixable[0].group(2)} to {fixable[0].group(1)}")
    return 1


DECL = re.compile(r"^(?:private\s+|protected\s+)?(theorem|lemma|def|abbrev|instance|structure|inductive)\s+(\S+)")


def challenge_text(solution: str, theorems: list[str]) -> str:
    lines = solution.splitlines()
    header, body = [], []
    for line in lines:
        if line.strip() in ("module", "@[expose] public section"):
            continue
        if line.startswith("public import "):
            header.append("import " + line[len("public import "):])
        elif line.startswith("import "):
            header.append(line)
        else:
            body.append(line)
    out, i, kept = [], 0, set()
    namespaces: list[str] = []
    while i < len(body):
        line = body[i]
        if line.startswith("/-!"):
            # module docstring: copy verbatim up to its closing -/
            j = i
            while j < len(body) and "-/" not in body[j][3 if j == i else 0:]:
                j += 1
            out.extend(body[i:j + 1])
            i = j + 1
            continue
        m = DECL.match(line)
        if m:
            j = i + 1
            while j < len(body) and (body[j].startswith((" ", "\t")) or body[j] == ""):
                if body[j] == "" and j + 1 < len(body) and not body[j + 1].startswith((" ", "\t")):
                    break
                j += 1
            block = body[i:j]
            # drop a preceding doc comment unless the declaration is kept
            if m.group(1) in ("theorem", "lemma") and m.group(2) in theorems:
                text = "\n".join(block)
                head = text.split(":=", 1)[0].rstrip()
                out.append(f"{head} := by\n  sorry")
                kept.add(m.group(2))
            else:
                while out and (out[-1].startswith(("/--", " ", "-/")) or out[-1].endswith("-/")) \
                        and any(o.startswith("/--") for o in out[-6:]):
                    # remove the doc comment attached to an omitted declaration
                    k = len(out) - 1
                    while k >= 0 and not out[k].startswith("/--"):
                        k -= 1
                    if k < 0:
                        break
                    del out[k:]
                    break
            i = j
            continue
        if line.startswith("namespace "):
            namespaces.append(line.split()[1])
        elif line.startswith("end ") and namespaces and line.split()[1] == namespaces[-1]:
            namespaces.pop()
        elif line.startswith(("section", "end ", "variable")):
            i += 1
            continue
        out.append(line)
        i += 1
    missing = set(theorems) - kept
    if missing:
        raise SystemExit(f"theorems not found in the Solution: {sorted(missing)}")
    text = "\n".join(header) + "\n\n" + "\n".join(out).strip() + "\n"
    return re.sub(r"\n{3,}", "\n\n", text)


def check_map(path: Path, mermaid: bool) -> int:
    data = tomllib.loads(path.read_text())
    handles = Handles()
    arguments = [record for _, record in load_ids("arguments").values()]
    nodes = {n["id"]: n for n in data.get("node", [])}
    resolved: dict[str, str] = {}
    problems = []
    for node_id, node in nodes.items():
        found = handles.existing("statement", node_id)
        if node.get("new"):
            if not node.get("text"):
                problems.append(f"new node {node_id} has no text")
            if found:
                problems.append(f"new node {node_id} already exists as statement {handles.aliases.show(found)}")
        elif found is None:
            problems.append(f"unknown statement {node_id} (mark it new = true with text)")
        else:
            resolved[node_id] = found
    concluded = {}
    for argument in arguments:
        concluded.setdefault(argument["conclusion_statement_id"], []).append(argument)

    def show(node_id: str) -> str:
        return handles.aliases.show(resolved[node_id]) if node_id in resolved else node_id

    lines = [f"exploration map {path.name}: target {data.get('target')}, "
             f"{len(nodes)} nodes ({sum(1 for n in nodes.values() if n.get('new'))} new), "
             f"{len(data.get('edge', []))} edges"]
    for edge in data.get("edge", []):
        for node_id in edge["premises"] + [edge["conclusion"]]:
            if node_id not in nodes:
                problems.append(f"edge to {edge['conclusion']} uses undeclared node {node_id}")
        premises = {resolved.get(node_id, node_id) for node_id in edge["premises"]}
        certified = [handles.aliases.show(a["id"]) for a in concluded.get(resolved.get(edge["conclusion"], ""), [])
                     if set(a["premise_statement_ids"]) == premises]
        lines.append(f"  [{edge.get('kind', 'derivation')}/{edge.get('status', 'mapped')}] "
                     f"{' + '.join(map(show, edge['premises']))} -> {show(edge['conclusion'])}"
                     + (f"  (certified by {', '.join(certified)})" if certified else ""))
    print("\n".join(lines))
    if mermaid:
        print("graph TD")
        for edge in data.get("edge", []):
            for premise in edge["premises"]:
                print(f"  {premise.replace('-', '_')} --> {edge['conclusion'].replace('-', '_')}")
    for problem in problems:
        print(f"problem: {problem}")
    return 1 if problems else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    records = sub.add_parser("records")
    records.add_argument("spec")
    records.add_argument("--write", action="store_true")
    records.add_argument("--fix", action="store_true")
    challenge = sub.add_parser("challenge")
    challenge.add_argument("solution")
    challenge.add_argument("theorems", nargs="+")
    challenge.add_argument("--write", action="store_true")
    exploration = sub.add_parser("map")
    exploration.add_argument("map")
    exploration.add_argument("--mermaid", action="store_true")
    args = parser.parse_args()
    if args.command == "map":
        return check_map(Path(args.map), args.mermaid)
    if args.command == "records":
        spec = tomllib.loads(Path(args.spec).read_text())
        planned = build_records(spec, args.write)
        print(("wrote" if args.write else "would write") + f" {len(planned)} files")
        for path in planned:
            print(f"  {path}")
        if args.write and args.fix:
            return fix_disambiguations(spec)
        return 0
    solution = Path(args.solution).resolve()
    text = challenge_text(solution.read_text(), args.theorems)
    target = solution.with_name("Challenge.lean")
    if args.write:
        target.write_text(text)
        print(f"wrote {target.relative_to(ROOT)}")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
