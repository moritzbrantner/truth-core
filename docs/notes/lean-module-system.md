# Lean module system: rebuild savings and verification boundary (2026-11-05)

Engineering investigation, lane C. No premise or frontier change. It records
measurements on the pinned toolchain (`leanprover/lean4:v4.35.0`, Mathlib
`v4.35.0`) and a pilot conversion of the Third Man area. The owner adopted
the module system repository-wide on #986; the decision record is
`docs/decisions/2026-11-05-01-lean-module-system.md`, and the migration waves
are recorded in [§5](#5-migration-waves).

**Short answer.** On v4.35 the module system is on by default. Lake rebuilds a
`module` importer from the imported module's *public* `.olean`. A theorem's
proof is not in that file, so editing only a proof does not rebuild module
importers. Every verification gate still reads the full proof terms. Comparator,
lean4export, NanoDa, bind-check and the other `importModules` tools load
`.olean.private`, which has them. The saving reaches only importers that are
modules themselves: a non-`module` importer still rebuilds on every change.
So the payoff depends on converting whole downstream cones, bottom-up.

## 1. Status and requirements on v4.35

- **Default, not experimental.** In the v4.35 sources,
  `register_builtin_option experimental.module` is documented as `"no-op, deprecated"`
  (`Lean/Language/Lean.lean`). A file opts in with a `module` first line and
  needs no lakefile option. The repository has used one module since #367:
  `TruthCore/Case/Catholicism/StageOne/CausalFinitism.lean`. It uses
  `public import Mathlib.Order.WellFoundedSet` and `@[expose] public section`.
- **Visibility.** Declarations in a module are private by default.
  `public section` or `public` makes them public. A `def` body is visible to
  importing *modules* only with `@[expose]`. `theorem` and `opaque` bodies are
  never exported; `abbrev` and `instance` bodies always are
  ([reference: Visibility](https://lean-lang.org/doc/reference/4.26.0-rc2/The-Module-System/Visibility/)).
  The public `.olean` stores a public theorem without its proof, and an
  unexposed `def` without its body (checked by reading `Pilot/A.olean` with
  `readModuleData`).
- **Import direction.** A module cannot import a non-module file:
  `cannot import non-module Pilot.L from module` (measured). A non-module file
  can import modules. It then sees their public names, private bodies included:
  it can `unfold` an unexposed `def`, which a module importer cannot. So
  conversion must go **bottom-up** in the import graph, and unconverted
  importers keep working.
- **Mathlib.** 8,812 of Mathlib's 9,220 files are modules. Mathlib sets Lake's
  `requiresModuleSystem`, so every non-module TruthCore file that imports
  Mathlib prints a Lake warning that suggests adding `module` (93 warnings in a
  179 s incremental build). Of the 54 distinct external modules TruthCore
  imports, only `Mathlib.Tactic` (in 2 files) is not a module. Those 2 files
  must import specific tactic modules before they can be converted.

## 2. Does Lake skip downstream rebuilds?

How it works (Lake `Build/Module.lean`, v4.35): a `module` importer's trace
mixes only the imported module's public `.olean` hash and the public traces of
its imports (`artsTrace`, `transTrace`). A non-module importer's trace mixes
`allArtsTrace`, which includes `.olean.private`, and `legacyTransTrace`, which
does the same transitively.

**Scratch chain** (no Mathlib): module `A` has theorems; modules `B` (imports `A`)
and `C` (imports `B`); non-module `L` imports `A`; non-module root.

| Edit in `A` | Public `A.olean` | Rebuilt |
| --- | --- | --- |
| Proof body, same axioms (several variants, including one that shifts lines) | unchanged | `A`, `L`, root |
| Unexposed `def` body | unchanged | `A`, `L`, root |
| Proof changes its axiom set (adds `propext`; `simp` vs `exact`) | changed | everything |
| Theorem statement | changed | everything (`B` re-elaborates and fails) |

A proof's axiom set is part of the interface: the public `.olean` keeps an
`exportedAxiomsExt` entry, so downstream `#print axioms` stays exact.

**Truth-core pilot** (§4: `Forms`, `ThirdMan`, `ThirdMan.Sensitivity`, 4
Solutions). The edit changes one proof line in `ThirdMan.consCases`. Wall
times are on the shared machine (`LEAN_NUM_THREADS=2`, heavy lock) and are
noisy. Module counts are exact.

| State | Edit | Modules rebuilt | Wall |
| --- | --- | --- | --- |
| main (non-module) | no-op | 0 | 12.6 s |
| main (non-module) | proof line | 9: `ThirdMan`, `Sensitivity`, 4 Solutions, 2 area aggregators, root | 44.9 s; 21.4 s for the revert |
| pilot (module) | same proof line | 4: `ThirdMan`, 2 aggregators, root | 11.2 s; 7.4 s for the revert |
| pilot (module) | docstring of a public `def` | 4 | 5.6 s |
| pilot (module) | new public theorem | 9 | 6.6 s |
| pilot (module) | `pairCases` statement | `ThirdMan` + importers, which re-elaborate and fail as expected | — |
| pilot (module) | `sorry` in the proof (changes axioms) | 9 | 19.3 s |

The one-time conversion build rebuilt 31 modules (`Forms`' dependents) in 29.5 s.
Artifacts grow slightly per module (`.olean` + `.olean.private` + `.olean.server` + `.ir`):
58 KB against 56 KB for `ThirdMan`.

The pilot saves little in absolute terms. Its dependents compile in under a
second each, and the fixed costs stay: about 12 s for Lake's no-op trace walk
over 4,457 jobs, plus the non-module aggregators (root 2.5–28 s under load).
The structural potential is large at hubs. Counting non-aggregator,
non-Challenge reverse dependents of the 1,232 library modules gives a median of
2, a mean of 27.5 and a p90 of 85. The largest hubs are `Modal.Kripke` (782),
`…Question2.Article3` (714), `Logic.ExcludedMiddle` (683) and
`…Question3.Article1` (616). After a full conversion, a proof-only edit in
`Modal.Kripke` would rebuild 1 module plus aggregators instead of 782.

## 3. Verification boundary

Every independent tool loads the environment with `importModules … {}`. Its
default level is `OLeanLevel.private`, which reads `.olean.private`. This holds
for `lean4export` (`Main.lean`), `scripts/TruthCoreConstants.lean`,
`BindTypes.lean`, `UnusedPremises.lean`, `LeanReuse.lean`,
`PropositionStructure.lean` and `CheckStrength.lean`. Comparator builds and
exports through `lean4export`. Measured on the pilot:

- **Comparator + NanoDa:** `scripts/verify-result.sh` passes for
  `THIRD-MAN-REGRESS`, `LIKENESS-REGRESS`, `THIRD-MAN-NOT-UNIQUE` and
  `THIRD-MAN-SENSITIVITY` (all zero-axiom). The Challenges stay non-module and
  unchanged; the Solutions are modules.
- **Proof terms exported:** the `lean4export` output for
  `…Regress.Solution` has `thm` records **with values** for `regress` and for
  the module lemmas `ThirdMan.consCases` / `pairCases`. It has `def` records
  with bodies for the vocabulary, and no axioms.
- **Negative control:** with a `sorry` inside `ThirdMan.consCases`'s proof (a
  module), Comparator fails (`illegal axiom detected: sorryAx`). Scoped NanoDa
  (`verify-library.sh --modules`) fails on `sorryAx`. `#print axioms` of the
  downstream Solution theorem reports `[sorryAx]` from both a module and a
  non-module file. A private helper's body is exported and checked too: in the
  scratch chain, `_private…helper` is in the dependency closure and NanoDa
  accepts it.
- **NanoDa root set:** `TruthCoreConstants.lean` over the 7 pilot modules lists
  the same 92 constants before and after conversion. `@[expose] public section`
  keeps every declaration public. Files that relied on private-by-default would
  lose roots: private names are internal and are skipped, as they already are
  for the 443 existing `private` declarations. Their bodies are still checked
  wherever a public declaration uses them.
- **bind-check, corpus check, tests and generated files:** with the pilot
  built, `corpus.py bind-check` reports 891 bound, 2 pinned, 0 mismatch (the
  two pinned results are the existing Timaeus ones). `corpus.py check`, the
  offline unit tests, `scripts/root-imports.sh` and `scripts/docs_index.py`
  pass. The aggregators stay non-module and import the converted modules
  unchanged. `verify-library.sh --modules` over the 7 pilot modules checks 306
  declarations with no typechecker errors.
- **Tooling parsers:** `affected_results.py`, `corpus.py` and
  `proposition_structure.py` already accept `public import`.
  `argument_context.py` did not: it read no imports or `public theorem`s from a
  module file. This PR fixes its regexes and adds a test.

Conclusion: under this conversion style the module system hides proofs only
from Lean's elaborator in importing modules, which is what saves the rebuilds.
It does not hide them from the kernel export.

## 4. Pilot conversion and migration cost

Pilot (in this PR): `TruthCore/Greek/Plato/Forms.lean`, `ThirdMan.lean`,
`ThirdMan/Sensitivity.lean` and the four `Results/Greek/Plato/ThirdMan/*/Solution.lean`.
Each change is mechanical: a `module` first line, `import` → `public import`,
and `@[expose] public section` after the imports and the module docstring.
Challenges are frozen and stay non-module: Comparator compares a non-module
Challenge with a module Solution correctly. Forms' 31 other dependents stay
non-module and build unchanged.

Repository-wide cost:

| Item | Count |
| --- | --- |
| Library files (non-Challenge, non-aggregator) | 1,232 (1 already a module, 7 in this pilot) |
| Challenges (stay non-module) | 730 |
| Generated aggregators (`TruthCore/Imports/*`, `TruthCore.lean`) | 57 + root |
| Files with `private` declarations (may break if referenced from an exposed body or public statement) | 64 (443 declarations) |
| Files importing non-module `Mathlib.Tactic` | 2 |
| Files with `syntax`/`macro`/`elab`/`#eval` (may need `meta` imports) | 2 |
| Longest import chain | 42 |

Most of the conversion is mechanical (the three-line header edit). Manual
fixes are expected in the few categories above. Each wave is gated by the
ordinary `lake build`. It can be done incrementally, but only **bottom-up**:
a file can become a module only once every TruthCore file it imports is one.
The savings appear only once a module's entire downstream cone is converted.
Converting areas top-down is impossible, and converting a leaf area alone
saves nothing.

## 5. Migration waves

Waves are generated by `python3 scripts/convert_to_module.py`: `plan --max-level N` lists the
non-module library files at topological level ≤ N (longest chain of TruthCore imports below
them) whose imports are all modules or convert in the same run; `convert --max-level N`
applies the three-line header change to exactly those. Challenges and aggregators are never
selected.

**Rebuild model, measured.** Lake rebuilds a *module* importer only when a directly imported
public interface changes. A *non-module* file rebuilds when anything in its transitive import
closure changed, also through module intermediates (`legacyTransTrace`). So a proof-only edit
in a hub rebuilds the hub plus every non-module file that transitively imports it. This model
predicted every measurement below exactly (module sets compared for `Modal.Kripke`), so the
savings grow with the converted part of each hub's downstream cone and reach "hub plus
aggregators" only once the whole cone is converted.

Hub edits: a no-op `skip` in a proof (`Modal.Kripke.axiomK_valid`,
`Logic.ExcludedMiddle.excludedMiddle_iff_predicative`). The Aquinas hubs contain only
definitions, so their edit is a docstring change (`SomethingIsMovedReading`, `PureAct`). Wall
times are with a warm build on the shared machine (`LEAN_NUM_THREADS=2`, heavy lock) and are
noisy; the first measured build after a seed took 1,308 s for the same 519 modules.

| Hub | Before: rebuilt / wall | After wave 1 | After wave 2 |
| --- | --- | --- | --- |
| `Modal.Kripke` (proof) | 519 / 255 s | 471 / 252 s | 30 / 15 s |
| `Logic.ExcludedMiddle` (proof) | 437 / 226 s | 413 / 244 s | 25 / 13 s |
| `…Question2.Article3` (docstring) | 476 (model) | 432 / 262 s | 27 / 14 s |
| `…Question3.Article1` (docstring) | 411 (model) | 404 / 240 s | 23 / 13 s |

After wave 2 the rebuilt set is the hub, the generated aggregators that import it
transitively, and the root: the aggregators are the only non-module library files left.
Converting them (`root_imports.py` emitting `module` + `public import`) reduces a
proof-only edit to the hub alone (below).

**Wave 1** (levels 0–2, 385 files, including the four hubs). Manual cases:

- `Politics.DistrictMajority` imported the non-module `Mathlib.Tactic`; it now imports
  `Mathlib.Data.Fintype.Pi`, which its `decide` proofs need. Comparator passes.
- `Greek.Plato.ParticipationGrounding` had `private instance : NeZero 4`. A module's exposed
  `def` cannot use a private instance, so the `Fin 4` literals in `AssignmentUnderdetermined`
  and `GroundingIndependent` silently fell back to core's `NeZero (3 + 1)`, whose proof uses
  `propext`. Comparator caught it (`illegal axiom detected: propext` for
  `PARTICIPATION-UNDERDETERMINED` and `PARTICIPATION-GROUNDING-INDEPENDENT`). The instance is
  now public, which restores the zero-axiom results. **Private instances are the one silent
  hazard of the conversion**: any other private declaration that an exposed body needs is an
  elaboration error.
- NanoDa roots (`TruthCoreConstants.lean` over the whole library): the 13,923 non-auxiliary
  names are identical before and after. Only compiler-generated `match_N` matcher names differ
  (47 removed, 3 added), because modules share matchers differently. Matchers are still
  checked through the dependency closure of the declarations that use them.

**Wave 2** (all remaining levels, 852 files; every non-Challenge, non-aggregator file is now a
module). Manual cases:

- `Causality.TemporalEventControls` dropped its unused `import Mathlib.Tactic`; its 105
  dependents build unchanged.
- `Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer.Solution`: five `private instance`
  `Decidable` declarations are public. `NecessaryClassicalGodRootFromAsymmetry` decides with
  them: an ordinary file's private instance stays active in importers, a module's does not.
  They are the only new NanoDa roots.
- `Modal.ResearchFinite`, `Modal.DResearch.Language` and `Modal.DResearch.Witnesses` run
  `#guard` checks, which evaluate code at compile time; they `meta import` the module that
  defines it.
- Verification: full build, bind-check (918 bound, 2 pinned, 0 mismatch), scoped NanoDa over
  the 849 converted modules (32,095 declarations), Comparator over the 137 results that
  depend on a manual case, and an axiom scan of all 1,122 result theorems against their
  `permitted_axioms` (none exceeds them). Roots: the non-auxiliary names are identical
  apart from the five instances; only `match_N` auxiliaries differ.
- Negative control: a `sorry` hidden in `Models.ModalExistenceDegrees` makes scoped NanoDa
  and `verify-result.sh MODAL-DEGREE-UNBOUNDED-WORLD-CONTROL` fail (`sorryAx`).
- Operational note: do not change sources while `lake build` runs. Lake hashes a file before
  Lean reads it, so an edit (or `git stash`/checkout) in between leaves outputs that do not
  match their traces; Lake then replays them as fresh. A clean rebuild of `.lake/build/lib/lean/TruthCore` fixes it.

**Module aggregators** (#986, last step). `scripts/root_imports.py` now emits an area's
aggregator as a module (`module`, `public import`) once every file of the area is a module,
and the root `TruthCore.lean` once every aggregator is one; an area with an ordinary file keeps
an ordinary aggregator. Challenges are not imported by aggregators and stay ordinary. With
every area converted, all 62 aggregators and the root are modules. Measured with the same
no-op `skip` edits (warm build, shared machine; wall times very noisy):

| Hub (proof edit) | Before: rebuilt / wall | After: rebuilt / wall |
| --- | --- | --- |
| `Modal.Kripke` | 33 / 99 s | 1 / 7 s |
| `Logic.ExcludedMiddle` | 26 / 1,008 s (machine under load) | 1 / 4 s |

Verification: full `lake build`; `TruthCoreConstants.lean` lists the same 16,368 NanoDa roots
from the module root as from the ordinary one (empty diff); bind-check 1032 bound, 2 pinned,
0 mismatch; Comparator passes for `GROUNDING-NECESSITATION-INCOMPATIBLE` (uses
`Modal.axiomK_valid`) and `MODAL-STANDARD-CORRESPONDENCE-CERTIFICATE`; scoped NanoDa over
`Modal.Kripke`, `Logic.ExcludedMiddle` and `GroundingBaseline.Solution` passes. Negative
control: a `sorry` in `axiomK_valid` makes `verify-result.sh GROUNDING-NECESSITATION-INCOMPATIBLE`
fail (`illegal axiom detected: sorryAx`).

## Decision points

Recommended plan, as put to the owner (decided on #986: points 1–4 and 6 as
recommended; new Solutions and vocabulary files are modules):

1. **Adopt at all?** Recommended: yes, as an engineering change. It hides no
   proof from the checkers, and Lake and Mathlib already push in this
   direction (the `requiresModuleSystem` warnings).
2. **Conversion style.** Recommended: `@[expose] public section` in every
   converted file, which keeps names, `def` unfolding and the NanoDa root set
   unchanged. Private-by-default (narrower interfaces, more savings on `def`
   edits) would need a review of each file. It would also need a
   `TruthCoreConstants` change so private declarations stay NanoDa roots.
   Not recommended now.
3. **Challenges.** Recommended: leave them non-module (they are frozen and not
   in the default target). Comparator handles a mixed pair.
4. **Waves.** In topological order by import depth, one PR per wave of a few
   hundred files, generated by a checked-in converter. Each wave runs a full
   `lake build` and full Comparator (`scripts/verify-all.sh`), since a header
   change selects everything anyway. Hubs (`Modal.Kripke`,
   `Logic.ExcludedMiddle`, Aquinas Q2–3) and their cones give the payoff.
5. **Aggregators.** Once an area is fully converted, `root_imports.py` could
   emit `module` + `public import` aggregators, so that they too skip on
   proof-only edits. A later step, after the waves.
6. **New files.** Whether `scripts/scaffold_result.py` and the worker contract
   should require `module` for new Solutions/vocabulary once their imports are
   modules.
