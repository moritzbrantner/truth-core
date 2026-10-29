import TruthCore.Logic.StrengthComparison

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

end TruthCore.StrengthBindingFixture
