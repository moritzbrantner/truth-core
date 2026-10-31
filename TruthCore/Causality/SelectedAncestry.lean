import TruthCore.Causality.NecessaryRootFork

/-! One selected existent's COMPLETE actual grounding ancestry (#311/#613).
Reuse ActualConcreteGround and Mathlib ReflTransGen. No observed prefix, new
ontology or thought occurrence is substituted for this cone. All application
hypotheses remain explicit and source-free. -/
namespace TruthCore.Causality.SelectedAncestry
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.CogitoNecessaryConcrete
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Logic (ExcludedMiddle)

variable {W B : Type}

/-- Every actual concrete finite ground-ancestor, including the selected being.
The reflexive endpoint is required actual/concrete explicitly. -/
def Cone (m : Profile W B) (w : W) (selected : B) (x : B) : Prop :=
  ActualConcrete m w x ∧ GroundAncestor m w x selected

/-- Well-foundedness only on the complete cone; unrelated grounding can regress. -/
def ConeWellFounded (m : Profile W B) (w : W) (selected : B) : Prop :=
  WellFounded fun a b : {x // Cone m w selected x} => m.grounds w a.val b.val

/-- Contingent dependence only for actual concrete members of this full cone. -/
def ConeContingentGrounded (m : Profile W B) (w : W) (selected : B) : Prop :=
  ∀ x, Cone m w selected x → ContingentAt m.ontic w x →
    ∃ y, ActualConcreteGround m w y x

/-- The existing GLOBAL actual-grounding premises imply both cone-local ones.
This compares scopes only; it does not establish any instance of either pair. -/
def ScopeComparison : Prop :=
  ∀ (W B : Type) (m : Profile W B) (w : W) (selected : B),
    (ActualGroundingWF m w → ConeWellFounded m w selected) ∧
    (EveryContingentGroundedAt m w → ConeContingentGrounded m w selected)

/-- One actual concrete necessary ancestor, with no incoming actual concrete
ground at the selected world. It may have non-concrete/unmodelled explanation
or incoming grounds elsewhere; neither uniqueness nor God is asserted. -/
def NecessaryRootAncestor (m : Profile W B) (w : W) (selected : B) : Prop :=
  ∃ x, Cone m w selected x ∧ NecessaryAt m.ontic w x ∧
    ∀ y, ¬ ActualConcreteGround m w y x

/-- The alternative actual contingent root has the same ancestry/minimality. -/
def ContingentRootAncestor (m : Profile W B) (w : W) (selected : B) : Prop :=
  ∃ x, Cone m w selected x ∧ ContingentAt m.ontic w x ∧
    ∀ y, ¬ ActualConcreteGround m w y x

/-- Shared descent extracted from the existing thinker-local proof. This is
not an extra foundation assumption: accessibility and actual population are
explicit inputs. Both horns retain selected-world rootness. -/
theorem rootForkOfAccessibility (m : Profile W B) (w : W) (selected : B)
    (hActual : ActualConcrete m w selected)
    (hAcc : Acc (ActualConcreteGround m w) selected) (hEM : ExcludedMiddle) :
    NecessaryRootAncestor m w selected ∨ ContingentRootAncestor m w selected := by
  have walk : ∀ x, Acc (ActualConcreteGround m w) x → GroundAncestor m w x selected →
      m.concrete x → m.ontic.ExistsAt w x →
      (NecessaryRootAncestor m w selected ∨ ContingentRootAncestor m w selected) := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      intro hanc hc hex
      rcases hEM (∃ y, ActualConcreteGround m w y x) with ⟨y, hy⟩ | hnone
      · exact ih y hy (Relation.ReflTransGen.head hy hanc) hy.1 hy.2.1
      · rcases hEM (ContingentAt m.ontic w x) with hcont | hncont
        · exact Or.inr ⟨x, ⟨⟨hc, hex⟩, hanc⟩, hcont, fun y hy => hnone ⟨y, hy⟩⟩
        · refine Or.inl ⟨x, ⟨⟨hc, hex⟩, hanc⟩, ?_, fun y hy => hnone ⟨y, hy⟩⟩
          intro v hv
          rcases hEM (m.ontic.ExistsAt v x) with h | h
          · exact h
          · exact (hncont ⟨hex, v, hv, h⟩).elim
  exact walk selected hAcc Relation.ReflTransGen.refl hActual.1 hActual.2

/-- Completeness matters: every actual predecessor of a cone member remains
in the cone, so its restricted WF lifts to accessibility of the selected being. -/
theorem accessibleOfConeWellFounded (m : Profile W B) (w : W) (selected : B)
    (hActual : ActualConcrete m w selected) (hWF : ConeWellFounded m w selected) :
    Acc (ActualConcreteGround m w) selected := by
  have lift : ∀ a : {x // Cone m w selected x},
      Acc (fun a b : {x // Cone m w selected x} => m.grounds w a.val b.val) a →
      Acc (ActualConcreteGround m w) a.val := by
    intro a ha
    induction ha with
    | intro a _ ih =>
      apply Acc.intro
      intro parent hEdge
      exact ih ⟨parent, ⟨hEdge.1, hEdge.2.1⟩,
        Relation.ReflTransGen.head hEdge a.property.2⟩ hEdge.2.2
  exact lift ⟨selected, hActual, Relation.ReflTransGen.refl⟩ (hWF.apply _)

end TruthCore.Causality.SelectedAncestry
