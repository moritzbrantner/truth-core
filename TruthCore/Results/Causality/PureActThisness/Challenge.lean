import TruthCore.Causality.PureActThisness
namespace TruthCore.Results.Causality.PureActThisness
open TruthCore.Case.Catholicism
open TruthCore.Causality.PureActThisness

/-- Unrestricted perfection and strict pure actuality leave only bare plurality:
any two first movers have exactly the same real determinations. Neither a
different perfection nor a non-pure individuating, receiving or limiting
principle can distinguish them. No first mover is produced. -/
theorem pureActPluralityIsBare {B R D : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hEvery : FirstMoverHasEveryPureDetermination Moved Moves Has Pure)
    (hPure : FirstMoverDeterminationsArePure Moved Moves Has Pure) :
    FirstMoversReallyIndiscernible Moved Moves Has := by
  sorry

/-- If each first mover has a real thisness, strict pure actuality makes that
thisness a pure perfection and unrestricted perfection gives it to every first
mover, so there is at most one. Conditional on three OPEN premises. -/
theorem uniqueFromRealThisness {B R D : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hEvery : FirstMoverHasEveryPureDetermination Moved Moves Has Pure)
    (hPure : FirstMoverDeterminationsArePure Moved Moves Has Pure)
    (hThis : FirstMoverHasRealThisness Moved Moves Has) :
    AtMostOneFirstUnmovedMover Moved Moves := by
  sorry

/-- Bare plurality excluded by identity of real indiscernibles over all beings.
Conditional on three OPEN premises; the third denies bare numerical difference
everywhere, not only among first movers. -/
theorem uniqueFromRealIndividuation {B R D : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hEvery : FirstMoverHasEveryPureDetermination Moved Moves Has Pure)
    (hPure : FirstMoverDeterminationsArePure Moved Moves Has Pure)
    (hIndividuate : RealDeterminationsIndividuate Has) :
    AtMostOneFirstUnmovedMover Moved Moves := by
  sorry

theorem controls : TruthCore.Causality.PureActThisness.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.PureActThisness
