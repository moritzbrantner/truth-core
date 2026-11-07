# Omission countermodel finder

An omission countermodel for premise k of a theorem
`thm (carriers) (predicates) (h₁ : P₁) … (hₙ : Pₙ) : C` is a finite
interpretation in which every Pᵢ with i ≠ k holds and C fails. It shows that the
remaining premises do not entail C under the encoded vocabulary. Workers used to
write these models and their `Control.Certificate` proofs by hand.
`scripts/countermodel.py` searches for them.

```bash
python3 scripts/countermodel.py TruthCore.Results.Causality.SelfOperationLife.pureActLives
python3 scripts/countermodel.py THEOREM --omit hLife      # by binder name or 1-based position
python3 scripts/countermodel.py THEOREM --all --size 3    # every premise plus a joint witness
python3 scripts/countermodel.py THEOREM --json --no-check
```

## How it works

1. `scripts/Countermodel.lean` (run with `lake env lean --run`) opens the
   elaborated theorem type. It sorts the binders into carriers (`B : Type`,
   `Sort u`), predicate parameters (into `Prop`, over carriers or over
   carrier predicates `T → Prop`), element constants (`esse : R`) and premises.
   It unfolds each premise and the conclusion through their definitions into
   `∀ ∃ ∧ ∨ ¬ → ↔ = ≠ True False` over predicate atoms. A quantifier over `Prop`,
   as in `ExcludedMiddle`, ranges over the two truth values.
2. The finder grounds these formulas over `Fin m` carriers (smallest total size
   first, each carrier up to `--size`, default 2) and every choice of the
   element constants. It encodes the target in CNF and solves it with a small
   DPLL solver, preferring false atoms, so the models are sparse. A
   predicate-of-predicates argument (`Possible (fun t => ¬ IsAt x t)`) is
   matched against every concrete subset. The found model is evaluated again
   directly before it is reported.
3. The model is rendered as Lean `abbrev`s and a `certificate` theorem
   `¬ Pₖ ∧ P₁ ∧ … ∧ ¬ C`, proved by `delta <unfolded definitions>; decide`.
   A premise quantified over `Prop` is closed by `Classical.em`. Unless
   `--no-check` is given, Lean checks every certificate. Statuses: `lean-checked`,
   `lean-rejected` (with the Lean output), `candidate` (not checked) or
   `unresolved`. `--all` adds a joint witness in which every premise and the
   conclusion hold.

A checked certificate can be pasted into a `Control` namespace, renamed and
cited from the result's `controls` theorem. Copy the statement, not just the
model: the certificate's Lean check is the evidence, not the solver.

## Boundaries

- The solver proposes; Lean decides. An unchecked candidate is not evidence.
- `unresolved` means only that no model exists within the size bound. It does
  not show that the premise is needed. When the omitted premise itself holds in
  every model within the bounds (for example excluded middle), the report says
  so: no omission model of this kind can exist there.
- A countermodel is relative to the formal vocabulary. It says nothing about
  whether the interpretation is metaphysically possible or about other readings
  of the premises.
- The joint witness is the first model found. It may be trivial, for example
  with every antecedent empty. A certificate that needs a nontrivial witness
  (such as `comp false true` in `ComponentFirstness`) still needs a hand-added
  conjunct.
- Unsupported, and reported as such: function-valued parameters (`f : B → B`),
  structure-bundled vocabulary (`M.MovedIn`), concrete carriers in the theorem
  (`Nat`, `Bool`), typeclass arguments, quantifiers over predicates other than
  `Prop`, and definitions that unfold outside the fragment.
- The solver is exhaustive over the bound and has no symmetry breaking. A size 3
  search over ternary relations can be slow.

## Rediscovered examples

`scripts/test_countermodel.py` rediscovers and Lean-checks the omission models
of `SelfOperationLife`, `PerfectionOfBeing`, `NecessaryBeingInAct` and
`ComponentFirstness` (`TruthCore/Results/Causality/*/Solution.lean`).
