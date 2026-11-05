module

public import TruthCore.Explanation.GroundingBaseline

/-! General semantic factorization companion for #545 A. This adds no language:
the same function receives only access, existence and rigid identity. Quantifiers
may occur inside that function. A property evaluated with differing grounding
arguments does not meet this shared-reduct factorization condition. -/

@[expose] public section
namespace TruthCore.Explanation.GroundingBaseline.Reduct
open TruthCore.Explanation.GroundingBaseline

def GeneralInvariant : Prop :=
  ∀ (W B : Type) (M N : Extension W B), SameModal M N →
    ∀ (query : (W → W → Prop) → (W → B → Prop) → (B → B → Prop) → Prop),
      query M.ontic.frame.access M.ontic.ExistsAt (fun x y => x = y) ↔
      query N.ontic.frame.access N.ontic.ExistsAt (fun x y => x = y)
end TruthCore.Explanation.GroundingBaseline.Reduct
