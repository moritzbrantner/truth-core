#!/usr/bin/env python3
"""Find finite omission countermodels for a Lean theorem (docs/countermodels.md).

For `thm (Carriers) (Predicates) (h₁ : P₁) … (hₙ : Pₙ) : C`, the omission model
for premise k interprets the carriers as `Fin m` and the predicates as finite
tables so that every Pᵢ with i ≠ k holds and C fails. The search grounds the
first-order skeleton that `scripts/Countermodel.lean` extracts, encodes it in
CNF and runs a small DPLL solver. A found model is only a candidate: the tool
renders it as Lean `abbrev`s with a `delta …; decide` certificate and, unless
`--no-check` is given, has Lean check it. "No model within bounds" is reported
as unresolved; it never shows that the premise is needed.
"""
from __future__ import annotations

import argparse
from itertools import product
import json
import re
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from proposition_structure import module_for  # noqa: E402

LEAN_ENV = ["python3", "scripts/worker_env.py", "--", "lake"]


# --- extraction -------------------------------------------------------------

def locate(root: Path, theorem: str) -> str:
    """Module declaring `theorem`; a Challenge/Solution pair resolves to the Solution."""
    try:
        return module_for(root, theorem)
    except ValueError as exc:
        solutions = re.findall(r"'([^']*/Solution)\.lean'", str(exc))
        if "ambiguous" in str(exc) and len(solutions) == 1:
            return str(Path(solutions[0]).relative_to(root)).replace("/", ".")
        raise


def extract(theorem: str, root: Path = ROOT, module: str | None = None) -> dict:
    """Elaborated first-order skeleton of `theorem` (built module required)."""
    module = module or locate(root, theorem)
    built = subprocess.run(LEAN_ENV + ["build", module], cwd=root, capture_output=True, text=True)
    if built.returncode:
        raise ValueError(f"build of {module} failed: {built.stderr.strip() or built.stdout.strip()}")
    with tempfile.NamedTemporaryFile("w", suffix=".json") as handle:
        json.dump({"modules": [module], "theorem": theorem}, handle)
        handle.flush()
        done = subprocess.run(LEAN_ENV + ["env", "lean", "--run", "scripts/Countermodel.lean", handle.name],
                              cwd=root, capture_output=True, text=True, timeout=300)
    if done.returncode:
        raise ValueError(f"extraction failed: {done.stderr.strip() or done.stdout.strip()}")
    skeleton = json.loads(done.stdout)
    if "error" in skeleton:
        raise ValueError(f"{theorem}: {skeleton['error']}")
    skeleton["module"] = module
    return skeleton


# --- propositional layer ----------------------------------------------------
# Formulas: True, False, ("var", i), ("not", f), ("and", (f, …)), ("or", (f, …)).

def neg(f):
    if f is True or f is False:
        return not f
    if f[0] == "not":
        return f[1]
    return ("not", f)


def conj(fs):
    out = []
    for f in fs:
        if f is False:
            return False
        if f is not True:
            out.extend(f[1] if f[0] == "and" else [f])
    return True if not out else out[0] if len(out) == 1 else ("and", tuple(out))


def disj(fs):
    out = []
    for f in fs:
        if f is True:
            return True
        if f is not False:
            out.extend(f[1] if f[0] == "or" else [f])
    return False if not out else out[0] if len(out) == 1 else ("or", tuple(out))


def iff(a, b):
    return disj([conj([a, b]), conj([neg(a), neg(b)])])


class Grounding:
    """Ground formulas over `Fin` carriers; atoms become propositional variables."""

    def __init__(self, skeleton: dict, sizes: dict[str, int], constants: dict[str, int]):
        self.sizes = sizes
        self.constants = constants
        self.preds = {p["name"]: p["args"] for p in skeleton["predicates"]}
        self.atoms: dict[tuple, int] = {}

    def domain(self, sorts):
        return list(product(*(range(self.sizes[s]) for s in sorts)))

    def values(self, sort):
        """Concrete values of an argument sort: elements, or subsets as tuples of points."""
        if isinstance(sort, str):
            return list(range(self.sizes[sort]))
        points = self.domain(sort["set"])
        return [tuple(p for p, bit in zip(points, bits) if bit) for bits in product((False, True), repeat=len(points))]

    def atom(self, key):
        if key not in self.atoms:
            self.atoms[key] = len(self.atoms) + 1
        return ("var", self.atoms[key])

    def term(self, t, env):
        if "v" in t:
            name = t["v"]
            return env[name] if name in env else self.constants[name]
        sorts = [v["sort"] for v in t["lam"]]
        names = [v["v"] for v in t["lam"]]
        return {point: self.formula(t["body"], {**env, **dict(zip(names, point))}) for point in self.domain(sorts)}

    def formula(self, f, env):
        kind = f["t"]
        if kind == "true":
            return True
        if kind == "false":
            return False
        if kind == "not":
            return neg(self.formula(f["a"], env))
        if kind in ("and", "or", "imp", "iff"):
            a, b = self.formula(f["a"], env), self.formula(f["b"], env)
            return {"and": lambda: conj([a, b]), "or": lambda: disj([a, b]),
                    "imp": lambda: disj([neg(a), b]), "iff": lambda: iff(a, b)}[kind]()
        if kind in ("forall", "exists"):
            values = (False, True) if f["sort"] == "Prop" else range(self.sizes[f["sort"]])
            parts = [self.formula(f["body"], {**env, f["v"]: x}) for x in values]
            return conj(parts) if kind == "forall" else disj(parts)
        if kind == "eq":
            return self.term(f["a"], env) == self.term(f["b"], env)
        if kind == "atom":
            if f["p"] in env:  # a bound propositional variable
                return env[f["p"]]
            return self.apply(f["p"], [self.term(t, env) for t in f["args"]])
        raise ValueError(f"unknown formula node {kind}")

    def apply(self, pred, args):
        """`pred(args)`; a symbolic set argument is matched against every concrete subset."""
        options = []
        for sort, arg in zip(self.preds[pred], args):
            if isinstance(arg, dict):
                choices = []
                for subset in self.values(sort):
                    members = set(subset)
                    choices.append((subset, conj([arg[p] if p in members else neg(arg[p]) for p in arg])))
                options.append(choices)
            else:
                options.append([(arg, True)])
        return disj([conj([cond for _, cond in combo] + [self.atom((pred, tuple(v for v, _ in combo)))])
                     for combo in product(*options)])


def tseitin(f, clauses, counter):
    """Literal equivalent to `f`, adding defining clauses."""
    if f[0] == "var":
        return f[1]
    if f[0] == "not":
        return -tseitin(f[1], clauses, counter)
    lits = [tseitin(g, clauses, counter) for g in f[1]]
    counter[0] += 1
    x = counter[0]
    if f[0] == "and":
        clauses.extend([-x, lit] for lit in lits)
        clauses.append([x] + [-lit for lit in lits])
    else:
        clauses.append([-x] + lits)
        clauses.extend([x, -lit] for lit in lits)
    return x


def solve(clauses, nvars, prefer=None):
    """DPLL with unit propagation; branches on `prefer` variables first, false first."""
    assign: dict[int, bool] = {}
    order = list(prefer or []) + [v for v in range(1, nvars + 1) if v not in set(prefer or [])]

    def value(lit):
        v = assign.get(abs(lit))
        return None if v is None else v == (lit > 0)

    def propagate(trail):
        changed = True
        while changed:
            changed = False
            for clause in clauses:
                unassigned, sat = None, False
                count = 0
                for lit in clause:
                    val = value(lit)
                    if val is True:
                        sat = True
                        break
                    if val is None:
                        count += 1
                        unassigned = lit
                if sat:
                    continue
                if count == 0:
                    return False
                if count == 1:
                    assign[abs(unassigned)] = unassigned > 0
                    trail.append(abs(unassigned))
                    changed = True
        return True

    def search():
        trail: list[int] = []
        if not propagate(trail):
            for v in trail:
                del assign[v]
            return False
        var = next((v for v in order if v not in assign), None)
        if var is None:
            return True
        for choice in (False, True):
            assign[var] = choice
            if search():
                return True
            del assign[var]
        for v in trail:
            del assign[v]
        return False

    sys.setrecursionlimit(max(10000, 4 * nvars + 100))
    return dict(assign) if search() else None


# --- search -----------------------------------------------------------------

def size_assignments(carriers, max_size):
    combos = list(product(range(1, max_size + 1), repeat=len(carriers)))
    combos.sort(key=lambda c: (sum(c), c))
    return [dict(zip(carriers, c)) for c in combos]


def find_model(skeleton: dict, holds: list[dict], fails: list[dict], max_size: int = 2):
    """Smallest model (by total carrier size) with every `holds` true and every `fails` false."""
    for sizes in size_assignments(skeleton["carriers"], max_size):
        names = [c["name"] for c in skeleton["constants"]]
        for values in product(*(range(sizes[c["sort"]]) for c in skeleton["constants"])):
            constants = dict(zip(names, values))
            g = Grounding(skeleton, sizes, constants)
            target = conj([g.formula(f, {}) for f in holds] + [neg(g.formula(f, {})) for f in fails])
            if target is False:
                continue
            clauses: list[list[int]] = []
            if target is not True:
                counter = [len(g.atoms)]
                clauses.append([tseitin(target, clauses, counter)])
                nvars = counter[0]
            else:
                nvars = len(g.atoms)
            assignment = solve(clauses, nvars, prefer=list(range(1, len(g.atoms) + 1)))
            if assignment is None:
                continue
            tables = {p["name"]: set() for p in skeleton["predicates"]}
            for (pred, args), var in g.atoms.items():
                if assignment.get(var, False):
                    tables[pred].add(args)
            model = {"sizes": sizes, "constants": constants, "tables": tables}
            if not all(evaluate(skeleton, model, f) for f in holds) or any(evaluate(skeleton, model, f) for f in fails):
                raise AssertionError("solver model does not satisfy its own encoding")
            return model
    return None


def evaluate(skeleton: dict, model: dict, f: dict) -> bool:
    """Direct evaluation of a formula in a concrete model (independent of the CNF)."""
    g = Grounding(skeleton, model["sizes"], model["constants"])
    g.atom = lambda key: key[1] in model["tables"][key[0]]
    return bool(g.formula(f, {}))


def omission_targets(skeleton: dict, omit: list[str] | None = None):
    premises = skeleton["premises"]
    chosen = premises if omit is None else [p for p in premises if p["name"] in omit]
    for p in chosen:
        others = [q["formula"] for q in premises if q is not p]
        yield p["name"], others, [skeleton["conclusion"]["formula"]]


# --- Lean rendering ---------------------------------------------------------

def lean_type(sort):
    if isinstance(sort, str):
        return sort
    return "(" + " → ".join(sort["set"] + ["Prop"]) + ")"


def render_predicate(name, sorts, table, sizes):
    params = [f"x{i}" for i in range(len(sorts))]
    if not sorts:
        return f"abbrev {name} : Prop := {'True' if table else 'False'}"
    signature = " → ".join([lean_type(s) for s in sorts] + ["Prop"])
    total = 1
    for s in sorts:
        if isinstance(s, str):
            total *= sizes[s]
        else:
            n = 1
            for c in s["set"]:
                n *= sizes[c]
            total *= 2 ** n
    if not table or len(table) == total:
        body = "True" if table else "False"
        return f"abbrev {name} : {signature} := fun {' '.join('_' for _ in sorts)} => {body}"
    rows = []
    for row in sorted(table):
        parts = []
        for var, sort, value in zip(params, sorts, row):
            if isinstance(sort, str):
                parts.append(f"{var} = {value}")
            else:
                points = list(product(*(range(sizes[c]) for c in sort["set"])))
                members = set(value)
                for p in points:
                    app = f"{var} {' '.join(map(str, p))}"
                    parts.append(app if p in members else f"¬ {app}")
        rows.append("(" + " ∧ ".join(parts) + ")")
    head = f"abbrev {name} : {signature} := fun {' '.join(params)} =>"
    return f"{head} {rows[0]}" if len(rows) == 1 else f"{head}\n  " + " ∨\n  ".join(rows)


def render_model(skeleton: dict, model: dict) -> list[str]:
    lines = [f"abbrev {c} := Fin {model['sizes'][c]}" for c in skeleton["carriers"]]
    for c in skeleton["constants"]:
        lines.append(f"abbrev {c['name']} : {c['sort']} := {model['constants'][c['name']]}")
    for p in skeleton["predicates"]:
        lines.append(render_predicate(p["name"], p["args"], model["tables"][p["name"]], model["sizes"]))
    return lines


def render_certificate(skeleton: dict, label: str, model: dict, omitted: str | None) -> str:
    conjuncts = []
    for p in skeleton["premises"]:
        text = f"({p['lean']})"
        conjuncts.append(f"¬ {text}" if p["name"] == omitted else text)
    concl = f"({skeleton['conclusion']['lean']})"
    conjuncts.append(concl if omitted is None else f"¬ {concl}")
    statement = " ∧\n    ".join(conjuncts)
    what = (f"Omission model for `{omitted}`: the other premises hold and the conclusion fails."
            if omitted else "Joint witness: every premise and the conclusion hold.")
    delta = f"  delta {' '.join(skeleton['unfolded'])}\n" if skeleton["unfolded"] else ""
    # One `decide` per conjunct keeps each Decidable instance problem small.
    holes = ", ".join("?_" for _ in conjuncts)
    closer = "decide"
    if '"sort": "Prop"' in json.dumps(skeleton):
        # `∀ P : Prop, P ∨ ¬ P` is not decidable; it is closed by `Classical.em`.
        closer = "first | decide | exact Classical.em"
    proof = f"{delta}  refine ⟨{holes}⟩ <;> {closer}"
    return "\n".join([f"namespace {label}", f"/-! {what} Candidate from scripts/countermodel.py; checked by `decide`. -/",
                      *render_model(skeleton, model),
                      f"theorem certificate :\n    {statement} := by", proof, f"end {label}"])


def lean_check(skeleton: dict, snippet: str, root: Path = ROOT) -> tuple[bool, str]:
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "CountermodelCheck.lean"
        path.write_text(f"import {skeleton['module']}\n\n{snippet}\n")
        done = subprocess.run(LEAN_ENV + ["env", "lean", str(path)], cwd=root, capture_output=True, text=True, timeout=600)
    output = (done.stdout + done.stderr).strip()
    return done.returncode == 0 and "error" not in output, output


# --- command ----------------------------------------------------------------

def run(skeleton: dict, omit: list[str] | None, max_size: int, witness: bool, check: bool, root: Path = ROOT) -> list[dict]:
    reports = []
    short = skeleton["theorem"].rsplit(".", 1)[-1]
    targets = list(omission_targets(skeleton, omit))
    if witness:
        targets.append((None, [p["formula"] for p in skeleton["premises"]] + [skeleton["conclusion"]["formula"]], []))
    for omitted, holds, fails in targets:
        label = f"Countermodel.{short}.{'omit_' + omitted if omitted else 'witness'}"
        model = find_model(skeleton, holds, fails, max_size)
        report = {"omitted": omitted, "kind": "omission" if omitted else "witness", "max_size": max_size}
        if model is None:
            report["status"] = "unresolved"
            report["note"] = f"no model with carriers of size ≤ {max_size}; this does not show the premise is needed"
            if omitted and find_model(skeleton, [], [next(p["formula"] for p in skeleton["premises"] if p["name"] == omitted)], max_size) is None:
                report["note"] += " (the premise itself holds in every model within these bounds)"
        else:
            snippet = render_certificate(skeleton, label, model, omitted)
            report.update(status="candidate", sizes=model["sizes"], lean=snippet)
        reports.append(report)
    candidates = [r for r in reports if r["status"] == "candidate"]
    if check and candidates:
        # One Lean run for all candidates; only on failure is each checked alone.
        ok, _ = lean_check(skeleton, "\n\n".join(r["lean"] for r in candidates), root)
        for r in candidates:
            if not ok:
                ok_one, output = lean_check(skeleton, r["lean"], root)
                if not ok_one:
                    r["lean_output"] = output
            r["status"] = "lean-checked" if ok or "lean_output" not in r else "lean-rejected"
    return reports


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("theorem", help="fully qualified Lean theorem name")
    parser.add_argument("--omit", action="append", metavar="HYP",
                        help="premise binder name or 1-based position to omit (repeatable; default: all)")
    parser.add_argument("--all", action="store_true", help="every premise (the default) plus the joint witness")
    parser.add_argument("--size", type=int, default=2, help="largest carrier size tried (default 2)")
    parser.add_argument("--module", help="module declaring the theorem (default: located from source)")
    parser.add_argument("--no-check", action="store_true", help="do not have Lean check the candidates")
    parser.add_argument("--json", action="store_true", help="machine-readable output")
    args = parser.parse_args(argv)
    try:
        skeleton = extract(args.theorem, module=args.module)
    except ValueError as exc:
        print(f"unsupported or unavailable: {exc}", file=sys.stderr)
        return 2
    omit = None
    if args.omit:
        names = [p["name"] for p in skeleton["premises"]]
        omit = [names[int(o) - 1] if o.isdigit() and 0 < int(o) <= len(names) else o for o in args.omit]
        unknown = [o for o in omit if o not in names]
        if unknown:
            print(f"unknown premise {unknown}; premises are {names}", file=sys.stderr)
            return 2
    reports = run(skeleton, omit, args.size, witness=args.all, check=not args.no_check)
    if args.json:
        print(json.dumps({"theorem": args.theorem, "module": skeleton["module"], "reports": reports}, indent=2, default=sorted))
    else:
        for r in reports:
            head = f"{r['kind']} {r['omitted'] or ''}: {r['status']}".replace("  ", " ")
            print(f"-- {head}" + (f" (sizes {r['sizes']})" if "sizes" in r else ""))
            if "note" in r:
                print(f"-- {r['note']}")
            if "lean" in r:
                print(r["lean"])
            if "lean_output" in r:
                print("/- Lean output:\n" + r["lean_output"] + "\n-/")
            print()
    return 1 if any(r["status"] == "lean-rejected" for r in reports) else 0


if __name__ == "__main__":
    sys.exit(main())
