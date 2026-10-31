import TruthCore.Causality.PossibleCauseOfContingency
import TruthCore.Causality.NecessarilyUnderived
import TruthCore.Results.Causality.ExternalCandidateNecessity.Solution
import TruthCore.Results.Modal.NecessaryIfExistent.Solution

/-! Source-free frame-scope weakening of the existing possible-external-cause
route. Keep the original Scenario and world-independent concrete predicate.
No claim that beginnings or external causal opportunity are possible is proved.
The classical logical basis is inherited from external-candidate equivalence. -/
namespace TruthCore.Causality.LocalFramePossibleExternalCause
open TruthCore.Causality.PossibleCauseOfContingency
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Modal (Euclidean Reflexive)

/-- Preserve a supplied external candidate, rather than substituting an
arbitrary witness of the imported existential equivalence. Restrict only its
auxiliary concrete predicate to equality with `c`, retaining original concrete
proof `hc` for subsequent use. Ontic, identity and existence are unchanged. -/
theorem necessaryOfExternalCandidate {W B : Type} (s : Scenario W B) (v : W) (c : B)
    (hc : s.concrete c) (he : s.ontic.ExistsAt v c)
    (hOutside : OutsideContingentTotalityAt s v c) : NecessaryAt s.ontic v c := by
  let selected : Scenario W B := { s with concrete := fun x => x = c }
  have hSelected : ExternalCandidateAt selected v := by
    refine ⟨c, rfl, he, ?_⟩
    intro x hx hCont
    have hxC : x = c := hx
    subst x
    exact hOutside c hc hCont
  obtain ⟨d, hd, _, hNecessary⟩ :=
    (TruthCore.Results.Causality.ExternalCandidateNecessity.checks W B selected v).mp hSelected
  have hdC : d = c := hd
  subst d
  exact hNecessary

/-- The old global universal accessibility assumption supplies the entire
new frame bundle, with the original Scenario and chosen actual world. -/
theorem localFrameOfUniversal {W B : Type} (s : Scenario W B) (w : W)
    (hUniversal : UniversalFrame s) :
    Euclidean s.ontic.frame ∧ ActualReflexive s.ontic w := by
  exact ⟨fun _ a b _ _ => hUniversal a b, hUniversal w w⟩

/-- Reuse the ALREADY EXISTING Boolean identity frame and its checked S5
control. It satisfies the new frame conditions but is not globally universal.
This separates frame assumptions only, not the full causal-premise bundles. -/
theorem identityFrameSeparation :
    Reflexive TruthCore.Modal.NecessaryIfExistent.identity ∧
    Euclidean TruthCore.Modal.NecessaryIfExistent.identity ∧
    ¬ (∀ a b, TruthCore.Modal.NecessaryIfExistent.identity.access a b) := by
  have hS5 := TruthCore.Results.Modal.NecessaryIfExistent.controls.2.2.2.1.1
  refine ⟨hS5.1, hS5.2, ?_⟩
  intro hAll
  have hImpossible : (false : Bool) = true := hAll false true
  exact Bool.noConfusion hImpossible

end TruthCore.Causality.LocalFramePossibleExternalCause
