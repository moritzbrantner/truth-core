import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.Nat.Order.Lemmas
import TruthCore.Logic.StrengthComparison

/-! Mathematical order comparisons use the pinned Mathlib order laws, never
primitive metaphysical relations named MoreIn or AtLeastIn. -/
namespace TruthCore.Logic.Strength.Order
open TruthCore.Logic.StrengthComparison
universe u

def Strict {α : Type u} [LinearOrder α] (x y : α) : Prop := y > x
def Weak {α : Type u} [LinearOrder α] (x y : α) : Prop := y ≥ x
def Unequal {α : Type u} (x y : α) : Prop := y ≠ x
def Equal {α : Type u} (x y : α) : Prop := y = x

def spec (α : Type u) [LinearOrder α] (x y : α) : ComparisonSpec where
  stronger := Strict x y
  weaker := Weak x y
  delta := Unequal x y
  remainder := Equal x y

def ExactDelta : Prop := ∀ (α : Type u) [LinearOrder α] (x y : α),
  Strict x y ↔ Weak x y ∧ Unequal x y

def AllowedCasesLaw : Prop := ∀ (α : Type u) [LinearOrder α] (x y : α),
  Weak x y ↔ Strict x y ∨ Equal x y

def RemainderLaw : Prop := ∀ (α : Type u) [LinearOrder α] (x y : α),
  Equal x y ↔ Weak x y ∧ ¬ Strict x y

def zeroSetting : ComparisonSpec := spec Nat 0 0
def ZeroSeparates : Prop := Separation zeroSetting
end TruthCore.Logic.Strength.Order
