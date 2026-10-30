import TruthCore.Logic.StrengthComparison
import TruthCore.Results.Logic.StrengthCause.Solution

namespace TruthCore.StrengthBindingFixture
open TruthCore.Logic.StrengthComparison

def Forward (P : Bool → Bool → Prop) (a b : Bool) : Prop := P a b
def Reverse (P : Bool → Bool → Prop) (a b : Bool) : Prop := P b a
def Delta (_P : Bool → Bool → Prop) (_a _b : Bool) : Prop := True

def selected (P : Bool → Bool → Prop) (a b : Bool) : ComparisonSpec where
  stronger := Forward P a b
  weaker := Forward P a b
  delta := Delta P a b

theorem correct (P : Bool → Bool → Prop) (a b : Bool) :
    Forward P a b → Forward P a b := fun h => h
theorem swapped (P : Bool → Bool → Prop) (a b : Bool) :
    Forward P b a → Forward P b a := fun h => h

def withBackground (P B : Prop) : ComparisonSpec where
  background := [B]
  stronger := P
  weaker := P
  delta := True

theorem backgroundCorrect (P B : Prop) : B → P → P := fun _ h => h
theorem backgroundWrong (P B : Prop) : (¬ B) → P → P := fun _ h => h

def sufficientOnly (P : Prop) : ComparisonSpec where
  stronger := P
  weaker := True
  delta := False
theorem reconstructionOnly (P : Prop) : True → False → P := fun _ h => False.elim h

def degenerate (P : Prop) : ComparisonSpec where
  stronger := P
  weaker := True
  delta := True → P

def equality (a b : Bool) : ComparisonSpec where
  stronger := a = b
  weaker := True
  delta := a = b

def separator : ComparisonSpec := equality false true
def anotherSpec (a b : Bool) : ComparisonSpec := equality a b
def wrongSeparator : ComparisonSpec := anotherSpec false true
theorem separatorCorrect : Separation separator := by
  exact ⟨trivial, trivial, fun h => Bool.noConfusion h⟩
theorem separatorSwapped : Separation (equality true false) := by
  exact ⟨trivial, trivial, fun h => Bool.noConfusion h⟩

universe u
def Universal {α : Type u} (P : α → Prop) : Prop := ∀ x, P x
def polymorphic {α : Type u} (P : α → Prop) : ComparisonSpec where
  stronger := Universal P
  weaker := Universal P
  delta := True
theorem polymorphicCorrect {α : Type u} (P : α → Prop) : Universal P → Universal P := fun h => h
theorem monomorphicOnly {α : Type} (P : α → Prop) : Universal P → Universal P := fun h => h

-- Proofs remain valid for the bad advertised applications. Only field binding
-- may reject these specifications.
def permuted (P : Bool → Bool → Prop) (a b : Bool) : ComparisonSpec where
  stronger := Forward P b a
  weaker := Forward P b a
  delta := Delta P a b

def Background (P : Bool → Bool → Prop) (a b : Bool) : Prop := P a b
def badBackground (P : Bool → Bool → Prop) (a b : Bool) : ComparisonSpec where
  background := [Background P b a]
  stronger := Forward P a b
  weaker := Forward P a b
  delta := Delta P a b
theorem badBackgroundValid (P : Bool → Bool → Prop) (a b : Bool) :
    Background P b a → Forward P a b → Forward P a b := fun _ h => h

open TruthCore.Greek.Plato.Timaeus TruthCore.Logic.Strength.Cause
-- The unused G is deliberately retained as the advertised generic parameter.
def specialized (Entity : Type u) [DecidableEq Entity]
    (_G : Entity → Prop) (C : Entity → Entity → Prop) : ComparisonSpec where
  stronger := DistinctCausePrinciple (fun _ => True) C
  weaker := CausePrinciple (fun _ => True) C
  delta := SelfCausingGeneratedHaveAlternativeCause (fun _ => True) C
theorem specializedValid (Entity : Type u) [DecidableEq Entity]
    (_G : Entity → Prop) (C : Entity → Entity → Prop) :
    DistinctCausePrinciple (fun _ => True) C ↔
      CausePrinciple (fun _ => True) C ∧
        SelfCausingGeneratedHaveAlternativeCause (fun _ => True) C :=
  TruthCore.Results.Logic.StrengthCause.equivalence Entity (fun _ => True) C

def Padded (P : Bool → Bool → Prop) (a b : Bool) : Prop := Forward P a b ∧ True
-- S ↔ (True ∧ (S ∧ True)) is valid, yet provides no useful explanation of S.
def padded (P : Bool → Bool → Prop) (a b : Bool) : ComparisonSpec where
  stronger := Forward P a b
  weaker := Delta P a b
  delta := Padded P a b
theorem paddedValid (P : Bool → Bool → Prop) (a b : Bool) :
    Forward P a b ↔ Delta P a b ∧ Padded P a b :=
  ⟨fun h => ⟨trivial, h, trivial⟩, fun h => h.2.1⟩

theorem paddedImplication (P : Bool → Bool → Prop) (a b : Bool) :
    Forward P a b → Delta P a b := fun _ => trivial
theorem paddedDeltaForward (P : Bool → Bool → Prop) (a b : Bool) :
    Forward P a b → Padded P a b := fun h => ⟨h, trivial⟩
theorem paddedReconstruction (P : Bool → Bool → Prop) (a b : Bool) :
    Delta P a b → Padded P a b → Forward P a b := fun _ h => h.1
end TruthCore.StrengthBindingFixture
