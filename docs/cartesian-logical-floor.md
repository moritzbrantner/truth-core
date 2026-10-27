# Cartesian logical floor: independent constructive propositions

This deliberately narrow slice establishes three facts about Lean's `Prop`:
`∀ p, ¬(p ∧ ¬p)`, `∃ p, ¬p`, and `¬∀ p, p`. The first is
non-contradiction in intuitionistic logic. The second is witnessed by `False`;
the third is derived from the second. No source-derived philosophical
attribution or metaphysical interpretation is made.

Reuse: `TruthCore.Logic.TruthPilot.SomePropositionHolds` already proves
`∃ p : Prop, p`; `TruthCore.Logic.ExcludedMiddle` already distinguishes
`¬¬(p ∨ ¬p)` from the stronger excluded middle principle. Do not duplicate
those nodes.

These results exclude universal truth/falsity *within the formal language*,
not global epistemic skepticism, ontological nihilism, a world with no concrete
entities, or the claim that a thinker exists. A Cogito-style performed denial
requires an independent occurrence witness; see #509 and PR #516.

The two witness propositions (`True` and `False`) do not by themselves
establish objective truth in an independently interpreted natural language.
Any such bridge remains open. No Catholicism root premise is discharged.

Verification obligations before merge: run `lake build`, the corpus and
binding checks, Comparator/NanoDa for the new results, and the relevant
regression tests. Until then this branch is a draft, not certified.
