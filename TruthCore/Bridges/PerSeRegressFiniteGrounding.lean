import TruthCore.Causality.EssentialPower
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia

/-!
Bridge vocabulary (#401, bridge batch 1): the secunda via's per se link
`CausesAsCaused` read through the finite-path vocabulary of
`TruthCore.Causality.EssentialPower`.

This file adds one proposition and no axiom. It is not a source reading: no
claim attributes it to Aquinas. It is the conclusion of the bridge result
`BRIDGE-PER-SE-REGRESS-FINITE-GROUNDING`, which derives it from the secunda
via's no-regress premise (`STMT-NO-INFINITE-PER-SE-EFFICIENT-CAUSE-SERIES`),
excluded middle and `STMT-FINITE-GROUNDING-HAS-SOURCE`.

`FinitelyGroundedPower` is used here only for its inductive path structure,
with "intrinsic" read as "has no upstream per se cause". The bridge does not
identify Aquinas' per se link with any power-transmission semantics
(`DISAMB-CAUSAL-POWER-GROUNDING`).
-/

namespace TruthCore.Bridges

open TruthCore.Causality

/-- Every being reaches, by a finite path of per se links `causesAsCaused y x`
(`y` causes `x` as a caused cause), a being that has no per se cause upstream.
The path may have length zero: a being with no per se cause is its own end
point. Nothing is said about whether that end point is one being for all
paths, or whether it is uncaused in every respect. -/
def EveryBeingHasFinitePerSePathToUncaused {Being : Type}
    (causesAsCaused : Being → Being → Prop) : Prop :=
  ∀ x, ∃ source, FiniteCausalPath causesAsCaused x source ∧
    ¬ ∃ y, causesAsCaused y source

end TruthCore.Bridges
