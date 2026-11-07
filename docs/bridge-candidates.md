# Bridge candidates

Mode 3 of #415: propose statements that might compose into a derivation of an
underived root-path statement, rank them, and optionally try them in Lean.
The output is a list of **candidates**. It never writes corpus records. A
closed Lean goal is not a verified result and says nothing about the fidelity
of any reading (invariants 6 and 16); a goal that stays open is not a
refutation. An accepted bridge is recorded the usual way ([Bridges](bridges.md)):
inference, argument, frozen Challenge, Solution, result, binding, Comparator
and NanoDa.

## Pipeline

```sh
# 1. Vocabulary: TruthCore constants mentioned by every statement declaration
#    (after lake build, under the heavy-job lock; ~15 s, ~5 GB).
python3 -c 'import json,glob; print("\n".join(sorted({json.load(open(f)).get("lean_declaration") or "" for f in glob.glob("corpus/statements/*.json")} - {""})))' > /tmp/decls.txt
flock /tmp/moenarch/truth-core-heavy.lock python3 scripts/worker_env.py -- \
  lake env lean --run scripts/StatementConstants.lean TruthCore /tmp/decls.txt > /tmp/constants.json

# 2. Targets and ranking (Rust, under a second).
cargo build --locked -p truth
target/debug/truth thickness --queue --json > /tmp/queue.json   # or: python3 scripts/corpus.py thickness --queue --json
target/debug/truth --json bridges --constants /tmp/constants.json \
  --queue-file /tmp/queue.json --targets 30 --top 3 > /tmp/bridges.json
target/debug/truth bridges --constants /tmp/constants.json --target STMT-EXISTING-IN-ACT-AT

# 3. Optional Lean trial (one Lean process; ~80 s and ~3 GB for 86 trials).
flock /tmp/moenarch/truth-core-heavy.lock python3 scripts/bridge_trial.py \
  --bridges /tmp/bridges.json --constants /tmp/constants.json --per-target 3 > /tmp/trials.json
```

## Ranking (`truth bridges`)

Each statement's vocabulary is the sorted set of TruthCore constants that
occur in its `lean_declaration`'s type and stored body, itself included;
nothing is unfolded. Single candidates rank by exact Jaccard similarity with
the target's set. Pairs and triples are formed from the best `--pool` singles
(default 12); each member must cover a target constant the others lack, and
they rank by the number of covered target constants, then Jaccard. Each
candidate lists its shared and missing target constants.

Excluded, with counts per target: the target itself, statements with the same
declaration, statements that already reach the target or are reached from it
through recorded arguments (premises and commitments), its `alternative_to`
and `attacks` rivals, and combinations whose members are already connected.
The Jaccard and BFS kernels are vendored from the owner's `rust-kernels`
(MIT) in `truth/src/kernels.rs` rather than depended on (invariant 19).

## Lean trial (`scripts/bridge_trial.py`)

The script generates one throwaway Lean file that imports the declarations'
modules and Aesop and runs the `#bridge_try` command of
`scripts/BridgeTrial.lean` once per candidate. The command opens the target's
binders and instantiates each premise's binders by the target binder of the
same name and definitionally equal type (instance binders by type or
synthesis). An unmatched binder is universally quantified and reported in
`generalized`: that is a stronger reading than the premise. The goal
`∀ binders, premises → target` is tried after `intros` and unfolding exactly
the named declarations, with `assumption`, `solve_by_elim`, `simp_all`,
`aesop` and `grind` separately under `--heartbeats`. A closing proof is
kernel-checked on an auxiliary name and its axioms are reported; `grind`,
`aesop` and `simp_all` may use classical axioms that a non-Mathlib result may
not.

Two controls run on the same instantiation: the target with no premises and
`False` from the premises. Statuses:

| status | meaning |
| --- | --- |
| `closed` | closed with every premise binder matched, both controls open |
| `closed_generalized` | closed only with some premise binders quantified |
| `closed_without_premises` | the target closed alone (classically, perhaps): the candidate is not needed |
| `closed_vacuous` | the premises prove `False` under this instantiation |
| `open` | no tactic closed the goal; not a refutation |
| `error` | the trial could not be built |

## Limits

- Constant overlap is a weak signal. Model and control statements share their
  fork's vocabulary and rank high although they rarely serve as premises.
- Binder matching by name misses premises stated over differently named
  vocabulary, and quantifying unmatched binders can make a premise trivially
  strong; read `generalized` before taking a closure seriously.
- `bridges` reads the queue from a file rather than calling the thickness
  module in-process.
- No `exact?` or library search: it is costly with Mathlib imported.
