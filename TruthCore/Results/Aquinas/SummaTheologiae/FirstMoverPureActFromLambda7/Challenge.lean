import TruthCore.Case.Catholicism.StageOne
import TruthCore.Latin.Aquinas.InMetaphysicam.BookXII
import TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyFacts.ActPriorFromIncorruptible.Solution
namespace TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverPureActFromLambda7
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.InMetaphysicam
open TruthCore.Case.Catholicism (FirstUnmovedMoverIsPureAct IsFirstUnmovedMover
  AtMostOneFirstUnmovedMover)

/-- *Met.* Λ.7 for the *prima via*'s mover, without act's simple priority: some
mover moved in no respect and in act in being cannot be otherwise in any respect
(Λ.7, 1072b7-8; *In Metaph.* XII, lect. 7 n. 13); there is at most one first
mover moved by none; whatever can fail to be `r` can be otherwise in `r` (open
bridge, unattributed); and every potency is of the contradictory (Θ.8,
1050b8-15; *In Metaph.* IX, lect. 9 n. 2–4). Hence every first mover moved by
none is pure act. Not used: act's simple priority, non-simultaneity, and the
bridge that the first unmoved mover is the first being. -/
theorem firstMoverPureActFromLambda7 {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
    (esse : Respect)
    (hLambda : SomeUnmovedMoverCannotBeOtherwiseReading MovedIn MovesIn InAct esse
      CanBeOtherwise)
    (hOne : AtMostOneFirstUnmovedMover MovedIn MovesIn)
    (hBridge : CanFailToBeIsCanBeOtherwiseBridge CanFailToBe CanBeOtherwise)
    (hContradiction : PotencyIsOfContradictionReading InPotency CanFailToBe) :
    FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency) := by
  sorry

/-- Facts about the Λ.7 route to pure act.

1. **Each of its four premises is needed.** For each, a model of the other
   three has a first mover moved by none that is in potency in some respect
   (place, in the witnesses). The model without the Λ.7 reading is the case
   *In Metaph.* IX, lect. 9 n. 6 allows: a unique first mover with a dormant
   potency in place, which can therefore fail to be and be otherwise there.
2. **It is not vacuous.** All four hold in a model with a first mover moved by
   none.
3. **The universal sibling reading needs no uniqueness.** If every mover moved
   in no respect and in act in being cannot be otherwise in any respect, then,
   with every mover being in act in the respect in which it moves (ST I q.2
   a.3), actuality only insofar as being (ST I q.4 a.1 ad 3), the bridge and the
   potency of the contradictory, every first mover moved by none is pure act. -/
theorem lambda7RouteFacts :
    (¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (_InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
      (_esse : Respect),
      AtMostOneFirstUnmovedMover MovedIn MovesIn →
      CanFailToBeIsCanBeOtherwiseBridge CanFailToBe CanBeOtherwise →
      PotencyIsOfContradictionReading InPotency CanFailToBe →
      FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency)) ∧
    (¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
      (esse : Respect),
      SomeUnmovedMoverCannotBeOtherwiseReading MovedIn MovesIn InAct esse
        CanBeOtherwise →
      CanFailToBeIsCanBeOtherwiseBridge CanFailToBe CanBeOtherwise →
      PotencyIsOfContradictionReading InPotency CanFailToBe →
      FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency)) ∧
    (¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
      (esse : Respect),
      SomeUnmovedMoverCannotBeOtherwiseReading MovedIn MovesIn InAct esse
        CanBeOtherwise →
      AtMostOneFirstUnmovedMover MovedIn MovesIn →
      PotencyIsOfContradictionReading InPotency CanFailToBe →
      FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency)) ∧
    (¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
      (esse : Respect),
      SomeUnmovedMoverCannotBeOtherwiseReading MovedIn MovesIn InAct esse
        CanBeOtherwise →
      AtMostOneFirstUnmovedMover MovedIn MovesIn →
      CanFailToBeIsCanBeOtherwiseBridge CanFailToBe CanBeOtherwise →
      FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency)) ∧
    (∃ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
      (esse : Respect),
      SomeUnmovedMoverCannotBeOtherwiseReading MovedIn MovesIn InAct esse
        CanBeOtherwise ∧
      AtMostOneFirstUnmovedMover MovedIn MovesIn ∧
      CanFailToBeIsCanBeOtherwiseBridge CanFailToBe CanBeOtherwise ∧
      PotencyIsOfContradictionReading InPotency CanFailToBe ∧
      ∃ f, IsFirstUnmovedMover MovedIn MovesIn f) ∧
    (∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
      (esse : Respect),
      EveryUnmovedMoverCannotBeOtherwiseReading MovedIn MovesIn InAct esse
        CanBeOtherwise →
      MovesOnlyAsInActReading MovesIn InAct →
      ActualityOnlyInsofarAsBeingReading InAct esse →
      CanFailToBeIsCanBeOtherwiseBridge CanFailToBe CanBeOtherwise →
      PotencyIsOfContradictionReading InPotency CanFailToBe →
      FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency)) := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverPureActFromLambda7
