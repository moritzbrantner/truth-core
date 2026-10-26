import TruthCore.Alternatives.ActPotencyRegress
namespace TruthCore.Results.Alternatives.MegarianAbolishesMotion
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Alternatives.ActPotencyRegress

/-- Aristotle's reply to the Megarians (*Metaphysics* IX.3, 1047a10-17): their
thesis abolishes motion and becoming. Something is being moved toward some `r`;
what is being moved toward `r` is able to be `r` and is not yet actually `r`;
so something is able to be `r` without actually being `r`, which the Megarian
thesis denies. -/
theorem megarianThesisFalse {Being Respect : Type}
    (MovedIn InAct CanBe : Being → Respect → Prop)
    (hSense : SomethingIsMovedReading MovedIn)
    (hNotYet : MovedNotYetInActReading MovedIn InAct)
    (hAble : MovedIsAbleToBeReading MovedIn CanBe) :
    MegarianThesisFalse InAct CanBe := by
  sorry

/-- The observation premise is needed: where nothing is moved and nothing is
able to be anything, the Megarian thesis holds. -/
theorem needsSense :
    ¬ ∀ (Being Respect : Type) (MovedIn InAct CanBe : Being → Respect → Prop),
      MovedNotYetInActReading MovedIn InAct → MovedIsAbleToBeReading MovedIn CanBe →
        MegarianThesisFalse InAct CanBe := by
  sorry

/-- The incompleteness premise is needed: a being moved toward a respect it
already actually has, and able to have, satisfies the Megarian thesis. -/
theorem needsNotYet :
    ¬ ∀ (Being Respect : Type) (MovedIn InAct CanBe : Being → Respect → Prop),
      SomethingIsMovedReading MovedIn → MovedIsAbleToBeReading MovedIn CanBe →
        MegarianThesisFalse InAct CanBe := by
  sorry

/-- The ability premise is needed: a being moved toward a respect it is not
able to have satisfies the Megarian thesis vacuously. -/
theorem needsAble :
    ¬ ∀ (Being Respect : Type) (MovedIn InAct CanBe : Being → Respect → Prop),
      SomethingIsMovedReading MovedIn → MovedNotYetInActReading MovedIn InAct →
        MegarianThesisFalse InAct CanBe := by
  sorry

end TruthCore.Results.Alternatives.MegarianAbolishesMotion
