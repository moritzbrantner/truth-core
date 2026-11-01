import TruthCore.Explanation.FixedConstituentNecessaryBeing

/-! Transparent weakening of the existing reason-closed account. The original
nonCopy clause is omitted; no new explanation relation or adequacy claim is added. -/
namespace TruthCore.Explanation.WeakAccountNecessaryBeing
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.ExplanatoryAdequacy

/-- Exactly the first four fields of ReasonClosed. Coverage and foundedness
remain independent OPEN commitments, not established explanatory adequacy. -/
structure WeakReasonClosed {W B F : Type} (A : Arena W B F) (w : W)
    (S : F → Prop) (x : F) : Prop where
  explanandum : S x
  truthful : ∀ f, S f → A.holds w f
  closed : ∀ r f, S f → A.explains w r f → S r
  covered : ∀ f, S f → Contingent A w f → ∃ r, A.explains w r f

end TruthCore.Explanation.WeakAccountNecessaryBeing
