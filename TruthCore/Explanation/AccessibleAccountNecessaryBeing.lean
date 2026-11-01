import TruthCore.Explanation.WeakAccountNecessaryBeing

/-! Local accessibility of one selected fact in the SAME account relation.
This does not identify global regress insufficiency with well-foundedness. -/
namespace TruthCore.Explanation.AccessibleAccountNecessaryBeing
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.ExplanatoryAdequacy

/-- Standard accessibility at the selected target, for EXACT existing
ContingentReason. Unrelated account chains are unrestricted by this input. -/
def SelectedAccountAccessible {W B F : Type} (A : Arena W B F) (w : W)
    (S : F → Prop) (x : F) : Prop :=
  Acc (ContingentReason A w S) x

end TruthCore.Explanation.AccessibleAccountNecessaryBeing
