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
    id = "STMT-..."
    lean = "FooReading"          # relative to batch.vocab unless it starts with TruthCore.
    paraphrase = "..."
    definitions = ["DEF-..."]
    disambiguations = ["DISAMB-..."]

    [[argument]]
    id = "FOO-FROM-BAR"
    theorem = "fooFromBar"       # in batch.results
    premises = ["STMT-..."]
    conclusion = "STMT-..."
    rule = "..."
    meaning = "..."              # also the result description
    senses = {PRIOR = "PRIOR_1"} # term_senses: one sense per disambiguated term
                                 # (TERM_n label or sense uuid; written as uuids)

    # An argument that works with several senses of a term becomes one
    # argument per sense (owner direction 2026-11-07). Each case has its own
    # sense-specific statements and Lean theorem; the generator gives every
    # case a fresh uuid4 argument/result id with a human `label`, and reuses
    # it on later runs (matched by label and term_senses).
    [[argument]]
    label = "Act is prior from incorruptible facts"
    for_each_sense = {term = "PRIOR", senses = ["PRIOR_1", "PRIOR_3"]}
    rule = "..."
    meaning = "..."
    [argument.cases.PRIOR_1]
    theorem = "actPriorSimply"
    premises = ["STMT-..."]
    conclusion = "STMT-..."
    [argument.cases.PRIOR_3]
    theorem = "actPriorInSubstance"
    premises = ["STMT-..."]
    conclusion = "STMT-..."

    [[relation]]
    id = "REL-..."
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
import uuid
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "corpus"
UUID4 = re.compile(r"[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}")


def slug(identifier: str) -> str:
    return re.sub(r"^(STMT|REL|INF)-", "", identifier).lower()


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


def sense_table() -> dict[str, dict[str, str]]:
    """term_label -> {label or uuid: uuid} from the disambiguations' senses."""
    table: dict[str, dict[str, str]] = {}
    for _, (_, record) in load_ids("disambiguations").items():
        for sense in record.get("senses", []):
            entry = table.setdefault(record["term_label"], {})
            entry[sense["label"]] = sense["id"]
            entry[sense["id"]] = sense["id"]
    return table


def resolve_senses(spec_senses: dict[str, str], table: dict[str, dict[str, str]], where: str) -> dict[str, str]:
    resolved = {}
    for term, sense in sorted(spec_senses.items()):
        if sense not in table.get(term, {}):
            raise SystemExit(f"{where}: {sense} is not a sense of {term}")
        resolved[term] = table[term][sense]
    return resolved


def expand_sense_forks(spec: dict, existing_arguments: dict[str, tuple[Path, dict]]) -> list[dict]:
    """One argument spec per sense for every `for_each_sense` argument."""
    table = sense_table()
    expanded = []
    for a in spec.get("argument", []):
        fork = a.get("for_each_sense")
        if fork is None:
            expanded.append({**a, "term_senses": resolve_senses(a.get("senses", {}), table, a["id"])})
            continue
        where = a.get("label", "for_each_sense argument")
        if "id" in a or not a.get("label"):
            raise SystemExit(f"{where}: a for_each_sense argument has a label and no id (each sense gets a uuid)")
        cases = a.get("cases", {})
        if sorted(cases) != sorted(fork["senses"]) or len(fork["senses"]) < 2:
            raise SystemExit(f"{where}: give one [argument.cases.<SENSE>] per sense in for_each_sense")
        for label in fork["senses"]:
            case = {**{k: v for k, v in a.items() if k not in ("for_each_sense", "cases")}, **cases[label]}
            term_senses = resolve_senses({**a.get("senses", {}), fork["term"]: label}, table, where)
            case["label"] = f"{a['label']} [{label}]"
            case["term_senses"] = term_senses
            match = [aid for aid, (_, record) in existing_arguments.items()
                     if record.get("label") == case["label"] and record.get("term_senses") == term_senses]
            case["id"] = case.get("id") or (match[0] if match else str(uuid.uuid4()))
            if match:
                case["inference_id"] = existing_arguments[match[0]][1]["inference_ids"][0]
            expanded.append(case)
    return expanded


def lean_name(batch: dict, name: str) -> str:
    return name if name.startswith("TruthCore.") else f"{batch['vocab']}.{name}"


def build_records(spec: dict, write: bool) -> list[str]:
    batch = spec["batch"]
    planned: list[str] = []
    existing = {kind: load_ids(kind) for kind in ("statements", "arguments", "inferences", "results", "relations")}
    spec_statements = {s["id"]: s for s in spec.get("statement", [])}

    for s in spec.get("statement", []):
        record = {"id": s["id"], **({"label": s["label"]} if "label" in s else {}), "paraphrase": s["paraphrase"]}
        if "lean" in s:
            record["lean_declaration"] = lean_name(batch, s["lean"])
        if s.get("definitions"):
            record["definition_ids"] = s["definitions"]
        if s.get("disambiguations"):
            record["disambiguation_ids"] = s["disambiguations"]
        path = existing["statements"].get(s["id"], (CORPUS / "statements" / f"{slug(s['id'])}.json",))[0]
        dump(path, record, write, planned)

    def senses(statement_id: str, key: str) -> list[str]:
        if statement_id in spec_statements:
            return spec_statements[statement_id].get(key, [])
        if statement_id in existing["statements"]:
            return existing["statements"][statement_id][1].get(f"{key[:-1]}_ids", [])
        raise SystemExit(f"unknown statement {statement_id}")

    table = sense_table()
    for a in expand_sense_forks(spec, existing["arguments"]):
        ids = a["premises"] + [a["conclusion"]]
        definitions = a.get("definitions") or sorted(
            {d for i in ids for d in senses(i, "definitions")} | set(batch.get("definitions", [])))
        disambiguations = a.get("disambiguations") or sorted(
            {d for i in ids for d in senses(i, "disambiguations")} | set(batch.get("disambiguations", [])))
        name = slug(a["id"])
        inference_id = a.get("inference_id") or (
            str(uuid.uuid4()) if UUID4.fullmatch(a["id"]) else f"INF-{a['id']}")
        inference = {"id": inference_id, "input_statement_ids": a["premises"],
                     "output_statement_id": a["conclusion"], "rule": a["rule"], "meaning": a["meaning"],
                     "assumption_statement_ids": [], "discharged_statement_ids": []}
        if "label" in a:
            inference["label"] = a["label"]
        labelled = {"label": a["label"]} if "label" in a else {}
        argument = {"id": a["id"], **labelled, "premise_statement_ids": a["premises"],
                    "conclusion_statement_id": a["conclusion"], "inference_ids": [inference_id],
                    "meaning": a["meaning"]}
        if a["term_senses"]:
            argument["term_senses"] = a["term_senses"]
        if definitions:
            argument["definition_ids"] = definitions
        if disambiguations:
            argument["disambiguation_ids"] = disambiguations
        for key in ("strong_version_needed", "commitment_statement_ids", "sense_mixing_control"):
            if key in a:
                argument[key] = a[key]
        if "sense_bridges" in a:
            argument["sense_bridges"] = [
                {**bridge, **{end: resolve_senses({bridge["term"]: bridge[end]}, table, a["id"])[bridge["term"]]
                              for end in ("from", "to")}}
                for bridge in a["sense_bridges"]]
        if a["id"] in existing["arguments"]:
            argument = {**existing["arguments"][a["id"]][1], **{k: v for k, v in argument.items()
                                                               if k not in ("disambiguation_ids",)}}
        comparator = f"results/{a['id']}/comparator.json"
        result = {"id": a["id"], **labelled, "argument_id": a["id"], "challenge_module": f"{batch['results']}.Challenge",
                  "solution_module": f"{batch['results']}.Solution", "theorem": f"{batch['results']}.{a['theorem']}",
                  "comparator_config": comparator, "status": "solution-present", "description": a["meaning"]}
        if a.get("label"):
            result["label"] = a["label"]
        if "transcription" in a:
            result["transcription"] = a["transcription"]
        inference_file = inference_id if UUID4.fullmatch(inference_id) else name
        dump(existing["inferences"].get(inference["id"], (CORPUS / "inferences" / f"{inference_file}.json",))[0],
             inference, write, planned)
        dump(existing["arguments"].get(a["id"], (CORPUS / "arguments" / f"{name}.json",))[0],
             argument, write, planned)
        dump(existing["results"].get(a["id"], (CORPUS / "results" / f"{a['id']}.json",))[0],
             result, write, planned)
        dump(ROOT / comparator, {"challenge_module": result["challenge_module"],
                                 "solution_module": result["solution_module"],
                                 "theorem_names": [result["theorem"]], "permitted_axioms": a.get("axioms", []),
                                 "enable_nanoda": True}, write, planned)

    for r in spec.get("relation", []):
        record = {k: r[k] for k in ("id", "label", "subject_kind", "subject_id", "predicate", "object_kind", "object_id")
                  if k in r}
        for key in ("verification_result_id", "strictness_result_id", "note"):
            if key in r:
                record[key] = r[key]
        dump(existing["relations"].get(r["id"], (CORPUS / "relations" / f"{slug(r['id'])}.json",))[0],
             record, write, planned)
    return planned


MISSING = re.compile(r"corpus error: (\S+): .*does not link (DISAMB-[A-Z0-9-]+)")


def fix_disambiguations(spec: dict) -> int:
    ours = {f"corpus/arguments/{slug(a['id'])}.json" for a in spec.get("argument", [])}
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
    statements = load_ids("statements")
    arguments = [record for _, record in load_ids("arguments").values()]
    nodes = {n["id"]: n for n in data.get("node", [])}
    problems = []
    for node_id, node in nodes.items():
        if node.get("new"):
            if not node.get("text"):
                problems.append(f"new node {node_id} has no text")
            if node_id in statements:
                problems.append(f"new node {node_id} already exists as a statement")
        elif node_id not in statements:
            problems.append(f"unknown statement {node_id} (mark it new = true with text)")
    concluded = {}
    for argument in arguments:
        concluded.setdefault(argument["conclusion_statement_id"], []).append(argument)
    lines = [f"exploration map {path.name}: target {data.get('target')}, "
             f"{len(nodes)} nodes ({sum(1 for n in nodes.values() if n.get('new'))} new), "
             f"{len(data.get('edge', []))} edges"]
    for edge in data.get("edge", []):
        for node_id in edge["premises"] + [edge["conclusion"]]:
            if node_id not in nodes:
                problems.append(f"edge to {edge['conclusion']} uses undeclared node {node_id}")
        certified = [a["id"] for a in concluded.get(edge["conclusion"], [])
                     if set(a["premise_statement_ids"]) == set(edge["premises"])]
        lines.append(f"  [{edge.get('kind', 'derivation')}/{edge.get('status', 'mapped')}] "
                     f"{' + '.join(edge['premises'])} -> {edge['conclusion']}"
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
