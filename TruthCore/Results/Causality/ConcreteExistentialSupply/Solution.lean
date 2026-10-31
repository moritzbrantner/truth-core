import TruthCore.Causality.ConcreteExistentialSupply
import TruthCore.Results.Causality.DerivativeJointPower.Solution
import TruthCore.Results.Causality.NecessaryRootFork.Solution
import TruthCore.Results.Causality.NecessaryConcreteUnderived.Solution

namespace TruthCore.Results.Causality.ConcreteExistentialSupply
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.ConcreteExistentialSupply
open TruthCore.Logic (ExcludedMiddle)

private theorem rootOfSupply {W B : Type} (m : Profile W B) (w : W)
    (hSupply : ActualConcreteSupply m w) : ∃ source, ActualRoot m w source := by
  obtain ⟨target, hTarget⟩ := hSupply
  obtain ⟨source, _, hSource⟩ :=
    TruthCore.Results.Causality.DerivativeJointPower.source_path
      (TruthCore.Causality.JointGroups.recorded (graph m w)) (graph m w).Source
      (fun g _ => g.property) target hTarget
  have hRoot : ActualRoot m w source.val := by
    refine ⟨source.property, ?_⟩
    intro candidate hGround
    exact hSource ⟨⟨candidate, hGround.1, hGround.2.1⟩, hGround.2.2⟩
  exact ⟨source.val, hRoot⟩

/-- Cumulative argument: existing joint supply extracts an actual concrete
source; contingent dependence excludes its contingency. The conclusion is
necessary concrete existence, not uniqueness, permanent underivedness or God.
Actual supply already includes actual population; global WF is not assumed. -/
theorem necessaryConcreteOfSupply {W B : Type} (m : Profile W B) (w : W)
    (hSupply : ActualConcreteSupply m w)
    (hDep : EveryContingentGroundedAt m w)
    (hEM : ExcludedMiddle) : NecessaryConcreteAt m w := by
  obtain ⟨source, hRoot⟩ := rootOfSupply m w hSupply
  cases hEM (TruthCore.German.Kant.CosmologicalInference.NecessaryAt m.ontic w source) with
  | inl hNecessary => exact ⟨source, hRoot.1.1, hRoot.1.2, hNecessary⟩
  | inr hNotNecessary =>
    exact False.elim
      ((everyContingentGrounded_iff_noContingentRoot m w hEM).mp hDep
        (contingentRootOfNonnecessary m w hEM ⟨source, hRoot, hNotNecessary⟩))

/-- Existing joint model retains an actual contingent concrete effect. -/
theorem jointWitness : TruthCore.Causality.ConcreteExistentialSupply.JointWitness := by
  let m := TruthCore.Causality.NecessaryConcreteUnderived.witnessProfile
  have old := TruthCore.Results.Causality.NecessaryConcreteUnderived.jointWitness
  refine ⟨?_, old.2.2.1, old.2.2.2.2.2.2⟩
  refine ⟨⟨false, trivial, Or.inl rfl⟩, ?_⟩
  apply TruthCore.Causality.DerivativeJointPower.Supply.intrinsic
  rintro ⟨candidate, hEdge⟩
  exact Bool.noConfusion hEdge.2.1

theorem supplyRootEquivalence : SupplyRootEquivalence := by
  intro W B m w
  constructor
  · exact rootOfSupply m w
  · rintro ⟨source, hRoot⟩
    refine ⟨⟨source, hRoot.1⟩,
      TruthCore.Causality.DerivativeJointPower.Supply.intrinsic _ ?_⟩
    rintro ⟨candidate, hEdge⟩
    exact hRoot.2 candidate.val ⟨candidate.property.1, candidate.property.2, hEdge⟩

theorem necessaryConcreteOfBorrowingEscape {W B : Type} (m : Profile W B) (w : W)
    (hPop : TruthCore.Logic.CogitoConcrete.InhabitedConcreteAt m.ontic m.concrete w)
    (hEscape : ActualConcreteBorrowingEscape m w)
    (hDep : EveryContingentGroundedAt m w)
    (hEM : ExcludedMiddle) : NecessaryConcreteAt m w := by
  have hSupply : ActualConcreteSupply m w := by
    obtain ⟨initial, hc, he⟩ := hPop
    rcases hEscape Set.univ (fun _ _ => trivial)
        ⟨⟨initial, hc, he⟩, trivial⟩ with ⟨source, _, hSource⟩ | ⟨g, _, _, hOutside⟩
    · exact ⟨source, TruthCore.Causality.DerivativeJointPower.Supply.intrinsic _ hSource⟩
    · obtain ⟨contributor, hMember⟩ := g.property
      exact False.elim (hOutside contributor hMember trivial)
  exact necessaryConcreteOfSupply m w hSupply hDep hEM

theorem borrowingEscapeWFEquivalence : BorrowingEscapeWFEquivalence := by
  intro W B m w hEM
  constructor
  · intro hCut
    constructor
    intro initial
    cases hEM (Acc (graph m w).edge initial) with
    | inl h => exact h
    | inr hNotAcc =>
      let D : Set {b // ActualConcrete m w b} := {b | ¬ Acc (graph m w).edge b}
      rcases hCut D (fun _ _ => trivial) ⟨initial, hNotAcc⟩ with
          ⟨source, hD, hSource⟩ | ⟨g, _, hD, hOutside⟩
      · apply False.elim
        apply hD
        apply Acc.intro
        intro parent hEdge
        exact False.elim (hSource ⟨parent, hEdge⟩)
      · apply False.elim
        apply hD
        apply Acc.intro
        intro parent hEdge
        cases hEM (Acc (graph m w).edge parent) with
        | inl h => exact h
        | inr h => exact False.elim (hOutside parent hEdge h)
  · intro hWF D _ hNonempty
    have findMinimal : ∀ x : {b // ActualConcrete m w b}, x ∈ D →
        ∃ selected, selected ∈ D ∧ ∀ parent, (graph m w).edge parent selected → parent ∉ D := by
      intro x
      induction x using hWF.induction with
      | h x ih =>
        intro hx
        cases hEM (∃ parent, (graph m w).edge parent x ∧ parent ∈ D) with
        | inl h =>
          obtain ⟨parent, hEdge, hMember⟩ := h
          exact ih parent hEdge hMember
        | inr h => exact ⟨x, hx, fun parent hEdge hMember => h ⟨parent, hEdge, hMember⟩⟩
    obtain ⟨initial, hInitial⟩ := hNonempty
    obtain ⟨selected, hSelected, hNoParent⟩ := findMinimal initial hInitial
    cases hEM (∃ parent, (graph m w).edge parent selected) with
    | inl hParent =>
      exact Or.inr ⟨⟨selected, hParent⟩, trivial, hSelected, hNoParent⟩
    | inr hSource => exact Or.inl ⟨selected, hSelected, hSource⟩

/-- Corpus-facing connection into the existing actual-grounding WF premise. -/
theorem actualWfOfBorrowingEscape {W B : Type} (m : Profile W B) (w : W)
    (hEscape : ActualConcreteBorrowingEscape m w)
    (hEM : ExcludedMiddle) : ActualGroundingWF m w := by
  exact (borrowingEscapeWFEquivalence W B m w hEM).mp hEscape

end TruthCore.Results.Causality.ConcreteExistentialSupply
