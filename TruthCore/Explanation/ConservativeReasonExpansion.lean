import TruthCore.Modal.WorldwiseExplanation
import TruthCore.Modal.NecessaryVariableEffects

/-!
# Conservative enrichment by weak explanatory tokens

An analyst-defined model-expansion result for #312 and #319. This reuses the
existing `ExistencePSR.Model`, tagged existence facts and candidate reasons.
No reason is proved metaphysically sufficient, intrinsic by nature, productive,
or an efficient cause. The construction diagnoses what the existing weak
clauses alone constrain; it does not refute an adequately interpreted PSR.
-/
namespace TruthCore.Explanation.ConservativeReasonExpansion

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Explanation.ExistencePSR
open TruthCore.Modal.WorldwiseExplanation
open TruthCore.Modal.NecessaryContingentActivity
open TruthCore.Modal.NecessaryVariableEffects

/-- The conjunction of existing factivity, existence-fact token coverage,
rigid-token stability and **existence-guarded** explanatory invariance. This
adds no independent criterion of explanatory adequacy or actual reasonhood.
In particular, it is not unconditional persistence of `explains` into worlds
where its target does not exist. -/
def CoverageAndGuardedStability (m : Model W B) : Prop :=
  Sound m ∧ ExistencePSR m ∧
  (∀ x, StableExplanation m x) ∧ (∀ x, ReasonInvariant m x)

/-- Each existing individual is assigned its matching `intrinsic` candidate
token. The underlying ontology, frame, existence and causes are literally
unchanged. The constructor name is only a syntactic tag, not an explanation
of why an essence is instantiated. -/
def canonical (o : Ontic W B) : Model W B where
  ontic := o
  explains := fun w r f => match f with
    | .fact x => r = .intrinsic x ∧ o.ExistsAt w x

/-- Generic conservative expansion, preservation of every ontic property,
and two controls on existing, unchanged named ontologies. The property
parameter in the second conjunct ranges over model-theoretic properties of
the whole `Ontic` structure; it is not a fresh philosophical bridge premise.

The fixed-effect control has two actual necessary individuals, a sound
distinct causal edge to the selected effect, and weak intrinsic-tag coverage.
The alternating-effect control retains coverage and guarded stability even
though the selected actual effect is absent at the other world. Factivity
then forbids that same token explaining its existence there. Neither control
establishes real intrinsic explanatory sufficiency or causal conservation. -/
def Certificate : Prop :=
  (∀ (W B : Type) (o : Ontic W B),
    ∃ m : Model W B, m.ontic = o ∧ CoverageAndGuardedStability m) ∧
  (∀ (W B : Type) (P : Ontic W B → Prop),
    (∀ m : Model W B, CoverageAndGuardedStability m → P m.ontic) ↔
      ∀ o : Ontic W B, P o) ∧
  (∃ m : Model Bool (Option Bool),
    m.ontic = fixedEffects ∧ CoverageAndGuardedStability m ∧
    SoundDistinctCauses m.ontic ∧
    NecessaryAt m.ontic false source ∧
    NecessaryAt m.ontic false firstEffect ∧
    m.explains false (.intrinsic firstEffect) (.fact firstEffect) ∧
    m.ontic.ExistsAt false source ∧ m.ontic.ExistsAt false firstEffect ∧
    source ≠ firstEffect ∧ m.ontic.Causes false source firstEffect) ∧
  (∃ m : Model Bool (Option Bool),
    m.ontic = alternatingEffects ∧ CoverageAndGuardedStability m ∧
    SoundDistinctCauses m.ontic ∧
    ContingentAt m.ontic false firstEffect ∧
    m.explains false (.intrinsic firstEffect) (.fact firstEffect) ∧
    ¬m.explains true (.intrinsic firstEffect) (.fact firstEffect))

end TruthCore.Explanation.ConservativeReasonExpansion
