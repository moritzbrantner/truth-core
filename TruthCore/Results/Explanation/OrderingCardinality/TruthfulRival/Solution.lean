module

public import TruthCore.Explanation.OrderingCardinality

@[expose] public section

namespace TruthCore.Results.Explanation.OrderingCardinality.TruthfulRival
open TruthCore.Explanation.OrderingCardinality

/-- Actual truth is compulsory even when an adequacy judgment accepts a false
candidate. The positive example assumes acceptance, rather than proving adequacy. -/
theorem checks : TruthfulRivalControls := by
  constructor
  · rintro a adequate hfalse ⟨p, hp, ha, _⟩
    exact hfalse p hp ha
  constructor
  · intro a adequate htrue
    let b : Arrangement := a.trans (Equiv.swap (a 0) (a 1))
    refine ⟨fun _ => True, htrue, trivial, b, ?_, trivial⟩
    intro he
    have hz := congrArg (fun e : Arrangement => e 0) he
    have hn : a 1 = a 0 := by
      simpa only [b, Equiv.trans_apply, Equiv.swap_apply_left] using hz
    exact Nat.zero_ne_one (a.injective hn.symm)
  · rintro a adequate ⟨p, hp, _, b, hba, hb⟩ hselect
    exact hba ((hselect p hp).2 b hb)

end TruthCore.Results.Explanation.OrderingCardinality.TruthfulRival
