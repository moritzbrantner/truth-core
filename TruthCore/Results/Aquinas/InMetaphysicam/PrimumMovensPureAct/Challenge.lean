import TruthCore.Latin.Aquinas.InMetaphysicam.BookIX
import TruthCore.Causality.TemporalPrimaVia
namespace TruthCore.Results.Aquinas.InMetaphysicam.PrimumMovensPureAct
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct)
open TruthCore.Latin.Aquinas.InMetaphysicam (MoverMovedAtNoTimeIsInActOnlyReading)
open TruthCore.Causality.TemporalPrimaVia (SliceFirstMoverMovedAtNoTimeBridge)
open TruthCore.Case.Catholicism (FirstUnmovedMoverIsPureAct IsFirstUnmovedMover)

/-- *In Metaph.* IX, lect. 8 n. 11 for the case's first mover, at one time: a
mover moved at no time is, whenever it moves, in potency in no respect (the
reading of *primum movens, quod est in actu tantum*); a first mover moved by
none at a time is moved at no time (open bridge, unattributed). Hence, at any
time `t`, every first mover moved by none at `t` is pure act at `t`: the case's
`FirstUnmovedMoverIsPureAct` read at the one time `t`. -/
theorem primumMovensPureAct {B R T : Type} (Moved InPotency : T → B → R → Prop)
    (Moves : T → B → B → R → Prop)
    (hInActOnly : MoverMovedAtNoTimeIsInActOnlyReading Moved Moves InPotency)
    (hBridge : SliceFirstMoverMovedAtNoTimeBridge Moved Moves) (t : T) :
    FirstUnmovedMoverIsPureAct (Moved t) (Moves t) (PureAct (InPotency t)) := by
  sorry

/-- Facts about the route.

1. **The bridge is needed.** In the strictly forward feedback model of
   `FIRST-WAY-SLICE-CONTROLS`, no mover is moved at no time, so the lect. 8
   reading holds, and the pure-act statement fails at t = 1.
2. **The reading is needed.** With one being, one respect and one time, a mover
   that is never moved and in potency satisfies the bridge, and the pure-act
   statement fails.
3. **It is not vacuous.** Both premises hold in a model with a first mover
   moved by none at a time. -/
theorem primumMovensFacts :
    (¬ ∀ (B R T : Type) (Moved InPotency : T → B → R → Prop)
      (Moves : T → B → B → R → Prop),
      MoverMovedAtNoTimeIsInActOnlyReading Moved Moves InPotency →
      ∀ t, FirstUnmovedMoverIsPureAct (Moved t) (Moves t) (PureAct (InPotency t))) ∧
    (¬ ∀ (B R T : Type) (Moved InPotency : T → B → R → Prop)
      (Moves : T → B → B → R → Prop),
      SliceFirstMoverMovedAtNoTimeBridge Moved Moves →
      ∀ t, FirstUnmovedMoverIsPureAct (Moved t) (Moves t) (PureAct (InPotency t))) ∧
    (∃ (B R T : Type) (Moved InPotency : T → B → R → Prop)
      (Moves : T → B → B → R → Prop),
      MoverMovedAtNoTimeIsInActOnlyReading Moved Moves InPotency ∧
      SliceFirstMoverMovedAtNoTimeBridge Moved Moves ∧
      ∃ t f, IsFirstUnmovedMover (Moved t) (Moves t) f) := by
  sorry

end TruthCore.Results.Aquinas.InMetaphysicam.PrimumMovensPureAct
