import Mathlib.Basic.ExistsUnique
import TruthCore.Logic.StrengthComparison

/-! Generic predicate fixture: uniqueness is the extra requirement; no source
claim or philosophical existence thesis is introduced by this test instance. -/
namespace TruthCore.Logic.Strength.UniqueExistence
open TruthCore.Logic.StrengthComparison
universe u

def Unique {α : Type u} (P : α → Prop) : Prop := ∃! x, P x
def Exists {α : Type u} (P : α → Prop) : Prop := ∃ x, P x
def AtMostOne {α : Type u} (P : α → Prop) : Prop := ∀ x y, P x → P y → x = y

def spec (α : Type u) (P : α → Prop) : ComparisonSpec where
  stronger := Unique P
  weaker := Exists P
  delta := AtMostOne P

def ExactDelta : Prop := ∀ (α : Type u) (P : α → Prop),
  Unique P ↔ Exists P ∧ AtMostOne P

def twoPointSetting : ComparisonSpec := spec Bool (fun _ => True)
def TwoPointsSeparate : Prop := Separation twoPointSetting
end TruthCore.Logic.Strength.UniqueExistence
