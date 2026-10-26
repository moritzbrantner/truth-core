import Mathlib.Order.FixedPoints
import Mathlib.Order.WellFounded
import TruthCore.Causality.GroundingLimits
import TruthCore.Results.Causality.FiniteGroundingHasSource.Solution
import TruthCore.Results.Causality.RegressReadingsCoincide.Solution

/-!
Analyst's structural schema (#412). An edge points from an upstream relatum to
its dependent. Sources and terminals are graph-relative, not gods or temporal
endpoints. Finite paths and inductive closure reuse the existing causal
vocabulary solely for its explicitly parameterized mathematical structure.
No source interpretation or actual well-foundedness is asserted.
-/
namespace TruthCore.Logic.Regress
open TruthCore.Causality

/-- Data only. Distinct domain meanings enter through distinct graph adapters. -/
structure Graph (Node : Type) where
  edge : Node → Node → Prop

namespace Graph
variable {A B : Type}

def Source (G : Graph A) (x : A) : Prop := ¬ ∃ y, G.edge y x
def Terminal (G : Graph A) (x : A) : Prop := ¬ ∃ y, G.edge x y

/-- The usual nonempty finite transitive closure, so self-edges count as cycles. -/
def NoCycles (G : Graph A) : Prop := ∀ x, ¬ Relation.TransGen G.edge x x

def Controls (G : Graph A) : Prop :=
  NoCycles G ∧ NoInfiniteDescendingPerSeSeries G.edge ∧
    ∀ x, ∃ s, FiniteCausalPath G.edge x s ∧ G.Source s

/-- Edge preservation suffices for pulling accessibility back; no relation
between the interpretations of the two carriers is built into this structure. -/
structure Map (G : Graph A) (H : Graph B) where
  node : A → B
  preserves : ∀ {y x}, G.edge y x → H.edge (node y) (node x)

theorem Map.accessible {G : Graph A} {H : Graph B} (f : Map G H)
    {x : A} (h : Acc H.edge (f.node x)) : Acc G.edge x := by
  generalize he : f.node x = b at h
  induction h generalizing x with
  | intro b _ ih =>
    exact Acc.intro x (fun y hy => ih (f.node y) (he ▸ f.preserves hy) rfl)

theorem Map.wellFounded {G : Graph A} {H : Graph B} (f : Map G H)
    (h : WellFounded H.edge) : WellFounded G.edge :=
  ⟨fun x => f.accessible (h.apply (f.node x))⟩

/-- Sources add a base case; upstream members transmit membership. -/
def transmission (G : Graph A) (intrinsic : A → Prop) : Set A →o Set A where
  toFun S := {x | intrinsic x ∨ ∃ y, G.edge y x ∧ y ∈ S}
  monotone' := by
    intro S T h x hx
    rcases hx with hx | ⟨y, hy, hs⟩
    · exact Or.inl hx
    · exact Or.inr ⟨y, hy, h hs⟩

theorem grounded_eq_lfp (G : Graph A) (intrinsic : A → Prop) :
    {x | FinitelyGroundedPower G.edge intrinsic x} = (G.transmission intrinsic).lfp := by
  apply le_antisymm
  · intro x hx
    induction hx with
    | intrinsic x hi =>
      rw [← (G.transmission intrinsic).map_lfp]
      exact Or.inl hi
    | borrowed hy _ ih =>
      rw [← (G.transmission intrinsic).map_lfp]
      exact Or.inr ⟨_, hy, ih⟩
  · apply (G.transmission intrinsic).lfp_le
    intro x hx
    rcases hx with hi | ⟨y, hy, hg⟩
    · exact .intrinsic x hi
    · exact .borrowed hy hg

theorem fixedPoints_equal_of_wellFounded (G : Graph A) (intrinsic : A → Prop)
    (h : WellFounded G.edge) :
    (G.transmission intrinsic).lfp = (G.transmission intrinsic).gfp := by
  apply le_antisymm (G.transmission intrinsic).lfp_le_gfp
  intro x hx
  induction h.apply x with
  | intro x _ ih =>
    have step : intrinsic x ∨ ∃ y, G.edge y x ∧ y ∈ (G.transmission intrinsic).gfp := by
      exact (congrArg (fun S : Set A => x ∈ S) (G.transmission intrinsic).map_gfp).mpr hx
    rw [← (G.transmission intrinsic).map_lfp]
    rcases step with hi | ⟨y, hy, hg⟩
    · exact Or.inl hi
    · exact Or.inr ⟨y, hy, ih y hy hg⟩

theorem controls_of_wellFounded (G : Graph A) (h : WellFounded G.edge) : G.Controls := by
  have noSeries := TruthCore.Results.Causality.RegressAccessibilityExcludesSeries.accessibilityReadingExcludesDescendingSeries A G.edge h.apply
  refine ⟨?_, noSeries, ?_⟩
  · intro x hx
    have noReturn : ∀ b, Acc G.edge b → ¬ Relation.TransGen G.edge b b := by
      intro b hb
      induction hb with
      | intro b _ ih =>
        intro hp
        cases hp with
        | single hbb => exact ih b hbb (.single hbb)
        | tail hab hbb => exact ih _ hbb ((Relation.TransGen.single hbb).trans hab)
    exact noReturn x (h.apply x) hx
  · intro x
    have hg : FinitelyGroundedPower G.edge G.Source x := by
      classical
      induction h.apply x with
      | intro x _ ih =>
        by_cases hs : ∃ y, G.edge y x
        · obtain ⟨y, hy⟩ := hs
          exact .borrowed hy (ih y hy)
        · exact .intrinsic x hs
    exact TruthCore.Results.Causality.FiniteGroundingHasSource.finiteGroundingHasSource
      A G.edge G.Source x hg

end Graph

/-- Universal structural controls, transfer along every edge-preserving map,
and Knaster–Tarski content; conditional laws only. -/
def StructuralSchema : Prop :=
  (∀ (A : Type) (G : Graph A), WellFounded G.edge → G.Controls) ∧
  (∀ (A B : Type) (G : Graph A) (H : Graph B) (_f : G.Map H),
    WellFounded H.edge → WellFounded G.edge) ∧
  (∀ (A : Type) (G : Graph A) (intrinsic : A → Prop),
    {x | FinitelyGroundedPower G.edge intrinsic x} = (G.transmission intrinsic).lfp) ∧
  (∀ (A : Type) (G : Graph A) (intrinsic : A → Prop), WellFounded G.edge →
    (G.transmission intrinsic).lfp = (G.transmission intrinsic).gfp)

end TruthCore.Logic.Regress
