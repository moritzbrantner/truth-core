import TruthCore.Case.Catholicism.StageOne
import TruthCore.Latin.Aquinas.InMetaphysicam.BookXII
import TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyFacts.ActPriorFromIncorruptible.Solution
namespace TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverPureActFromLambda7
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.InMetaphysicam
open TruthCore.Case.Catholicism (FirstUnmovedMoverIsPureAct IsFirstUnmovedMover
  AtMostOneFirstUnmovedMover)

/-- *Met.* Λ.7 for the *prima via*'s mover, without act's simple priority: some
mover moved in no respect of change and in act in being cannot be otherwise in
any respect of change (Λ.7, 1072b4-10; *In Metaph.* XII, lect. 7 n. 12–13); a
mover unchangeable in every respect of change is unmoved and cannot be otherwise
in any respect (open bridge, unattributed; lect. 11 n. 8 supports it for the
respect of understanding only); there is at most one first mover
moved by none; whatever can fail to be `r` can be otherwise in `r` (*In Metaph.*
V, lect. 6 n. 14, read per respect); and every potency is of the contradictory (Θ.8, 1050b8-15;
*In Metaph.* IX, lect. 9 n. 2–4). Hence every first mover moved by none is pure
act. Not used: act's simple priority, non-simultaneity, and the bridge that the
first unmoved mover is the first being. -/
theorem firstMoverPureActFromLambda7 {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
    (esse : Respect) (OfChange : Respect → Prop)
    (hLambda : SomeUnmovedMoverCannotBeOtherwiseReading MovedIn MovesIn InAct esse
      OfChange CanBeOtherwise)
    (hScope : UnchangeableInRespectsOfChangeIsUnchangeableSimplyBridge MovedIn MovesIn
      OfChange CanBeOtherwise)
    (hOne : AtMostOneFirstUnmovedMover MovedIn MovesIn)
    (hBridge : CanFailToBeIsCanBeOtherwiseBridge CanFailToBe CanBeOtherwise)
    (hContradiction : PotencyIsOfContradictionReading InPotency CanFailToBe) :
    FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency) := by
  sorry

/-- Facts about the Λ.7 route to pure act.

1. **Each of its five premises is needed.** For each, a model of the other four
   has a first mover moved by none that is in potency in some respect. Without
   the Λ.7 reading, the unique first mover has a dormant potency in place: the
   analogue, for a first mover, of what *In Metaph.* IX, lect. 9 n. 6 allows in
   moved incorruptible bodies. Without the scope bridge, the mover is fixed in
   every respect of change but in potency in a respect that is not one of change.
2. **It is not vacuous.** All five hold in a model with a first mover moved by
   none.
3. **The universal sibling reading needs no uniqueness.** If every mover moved
   in no respect of change and in act in being cannot be otherwise in any
   respect of change, then, with every mover being in act in the respect in
   which it moves (ST I q.2 a.3), actuality only insofar as being (ST I q.4 a.1
   ad 3), the scope bridge, the bridge from failing to be to being otherwise and
   the potency of the contradictory, every first mover moved by none is pure
   act. -/
theorem lambda7RouteFacts :
    (¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (_InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
      (_esse : Respect) (OfChange : Respect → Prop),
      UnchangeableInRespectsOfChangeIsUnchangeableSimplyBridge MovedIn MovesIn
        OfChange CanBeOtherwise →
      AtMostOneFirstUnmovedMover MovedIn MovesIn →
      CanFailToBeIsCanBeOtherwiseBridge CanFailToBe CanBeOtherwise →
      PotencyIsOfContradictionReading InPotency CanFailToBe →
      FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency)) ∧
    (¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
      (esse : Respect) (OfChange : Respect → Prop),
      SomeUnmovedMoverCannotBeOtherwiseReading MovedIn MovesIn InAct esse
        OfChange CanBeOtherwise →
      AtMostOneFirstUnmovedMover MovedIn MovesIn →
      CanFailToBeIsCanBeOtherwiseBridge CanFailToBe CanBeOtherwise →
      PotencyIsOfContradictionReading InPotency CanFailToBe →
      FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency)) ∧
    (¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
      (esse : Respect) (OfChange : Respect → Prop),
      SomeUnmovedMoverCannotBeOtherwiseReading MovedIn MovesIn InAct esse
        OfChange CanBeOtherwise →
      UnchangeableInRespectsOfChangeIsUnchangeableSimplyBridge MovedIn MovesIn
        OfChange CanBeOtherwise →
      CanFailToBeIsCanBeOtherwiseBridge CanFailToBe CanBeOtherwise →
      PotencyIsOfContradictionReading InPotency CanFailToBe →
      FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency)) ∧
    (¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
      (esse : Respect) (OfChange : Respect → Prop),
      SomeUnmovedMoverCannotBeOtherwiseReading MovedIn MovesIn InAct esse
        OfChange CanBeOtherwise →
      UnchangeableInRespectsOfChangeIsUnchangeableSimplyBridge MovedIn MovesIn
        OfChange CanBeOtherwise →
      AtMostOneFirstUnmovedMover MovedIn MovesIn →
      PotencyIsOfContradictionReading InPotency CanFailToBe →
      FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency)) ∧
    (¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
      (esse : Respect) (OfChange : Respect → Prop),
      SomeUnmovedMoverCannotBeOtherwiseReading MovedIn MovesIn InAct esse
        OfChange CanBeOtherwise →
      UnchangeableInRespectsOfChangeIsUnchangeableSimplyBridge MovedIn MovesIn
        OfChange CanBeOtherwise →
      AtMostOneFirstUnmovedMover MovedIn MovesIn →
      CanFailToBeIsCanBeOtherwiseBridge CanFailToBe CanBeOtherwise →
      FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency)) ∧
    (∃ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
      (esse : Respect) (OfChange : Respect → Prop),
      SomeUnmovedMoverCannotBeOtherwiseReading MovedIn MovesIn InAct esse
        OfChange CanBeOtherwise ∧
      UnchangeableInRespectsOfChangeIsUnchangeableSimplyBridge MovedIn MovesIn
        OfChange CanBeOtherwise ∧
      AtMostOneFirstUnmovedMover MovedIn MovesIn ∧
      CanFailToBeIsCanBeOtherwiseBridge CanFailToBe CanBeOtherwise ∧
      PotencyIsOfContradictionReading InPotency CanFailToBe ∧
      ∃ f, IsFirstUnmovedMover MovedIn MovesIn f) ∧
    (∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InAct InPotency CanFailToBe CanBeOtherwise : Being → Respect → Prop)
      (esse : Respect) (OfChange : Respect → Prop),
      EveryUnmovedMoverCannotBeOtherwiseReading MovedIn MovesIn InAct esse
        OfChange CanBeOtherwise →
      MovesOnlyAsInActReading MovesIn InAct →
      ActualityOnlyInsofarAsBeingReading InAct esse →
      UnchangeableInRespectsOfChangeIsUnchangeableSimplyBridge MovedIn MovesIn
        OfChange CanBeOtherwise →
      CanFailToBeIsCanBeOtherwiseBridge CanFailToBe CanBeOtherwise →
      PotencyIsOfContradictionReading InPotency CanFailToBe →
      FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency)) := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverPureActFromLambda7
