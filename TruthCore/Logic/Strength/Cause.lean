import TruthCore.Greek.Plato.Timaeus
import TruthCore.Logic.StrengthComparison

/-! Conditional comparison of the existing broad/distinct readings. No source
claim is revised. Decidable equality is an explicit parameter of the selected
comparison; no global causal irreflexivity or metaphysical applicability follows. -/
namespace TruthCore.Logic.Strength.Cause
open TruthCore.Greek.Plato.Timaeus
open TruthCore.Logic.StrengthComparison
universe u

/-- Every generated thing that causes itself also admits a distinct cause.
This local repair condition is vacuous when no generated being causes itself;
it permits simultaneous self-causation and causation by another being. -/
def SelfCausingGeneratedHaveAlternativeCause {Entity : Type u}
    (G : Entity → Prop) (C : Entity → Entity → Prop) : Prop :=
  ∀ x, G x → C x x → ∃ y, y ≠ x ∧ C y x

/-- Fixed shared vocabulary, with explicit decidability of identity. -/
def spec (Entity : Type u) [DecidableEq Entity]
    (G : Entity → Prop) (C : Entity → Entity → Prop) : ComparisonSpec where
  stronger := DistinctCausePrinciple G C
  weaker := CausePrinciple G C
  delta := SelfCausingGeneratedHaveAlternativeCause G C

/-- Exact additional content, not equivalence of broad and distinct readings. -/
def ExactDelta : Prop := ∀ (Entity : Type u) [DecidableEq Entity]
  (G : Entity → Prop) (C : Entity → Entity → Prop),
  DistinctCausePrinciple G C ↔ CausePrinciple G C ∧ SelfCausingGeneratedHaveAlternativeCause G C

/-- One generated point causes only itself; the second Bool point is ungenerated.
This is a formal interpretation, not an assertion of actual self-causation. -/
def selfOnlySetting : ComparisonSpec :=
  spec Bool (fun x => x = false) (fun c x => c = x)

def SelfOnlySeparates : Prop := Separation selfOnlySetting

/-- A mixed relation has all causal pairs, including both self and nonself pairs. -/
def MixedSelfAndOtherAllowed : Prop :=
  SelfCausingGeneratedHaveAlternativeCause (fun _ : Bool => True) (fun _ _ => True) ∧
  (fun _ _ : Bool => True) false false

/-- With no causes and a generated point, D is true but W and S are false. -/
def NoCauseDeltaControl : Prop :=
  SelfCausingGeneratedHaveAlternativeCause (fun _ : Bool => True) (fun _ _ => False) ∧
  ¬ CausePrinciple (fun _ : Bool => True) (fun _ _ => False)
/-- The local delta is not a disguised W → S: a generated uncaused point
makes W → S vacuous, while a different exclusively self-caused point falsifies D. -/
def DeltaNotConditionalRestatement : Prop :=
  let G := fun _ : Bool => True
  let C := fun c x : Bool => c = false ∧ x = false
  (CausePrinciple G C → DistinctCausePrinciple G C) ∧
  ¬ SelfCausingGeneratedHaveAlternativeCause G C
end TruthCore.Logic.Strength.Cause
