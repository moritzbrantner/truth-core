import TruthCore.Results.Alternatives.MegarianAbolishesMotion.Solution
import TruthCore.Logic.Configuration

namespace TruthCore.Results.Alternatives.MegarianCapacityCore
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Alternatives.ActPotencyRegress
open TruthCore.Results.Alternatives.MegarianAbolishesMotion

/-- Incompatibility clean-up core (#576) in the shared capacity/actuality
vocabulary of *Metaphysics* IX.3 (`Being`, `Respect`, `MovedIn`, `InAct`,
`CanBe`): the Megarian thesis (whatever is able to be `r` is actually `r`,
1046b29-32), present motion (ST I q.2 a.3), motion's incompleteness (what is
being moved toward `r` is not yet actually `r`, *Physics* III.2, 201b31-33)
and the ability of what is moved (what is being moved toward `r` is able to be
`r`, 1047a11-14) are jointly inconsistent. All five parameters are shared by
the four hypotheses; nothing else is assumed. The certificate composes
`MegarianAbolishesMotion.megarianThesisFalse`. Each single removal has a
registered model in `TruthCore.Models.MegarianCapacity`, so the core is
inclusion-minimal. It certifies that the four positions cannot all hold under
this encoding, not which of them is false. -/
theorem incompatible {Being Respect : Type}
    (MovedIn InAct CanBe : Being → Respect → Prop)
    (hMegarian : MegarianAbilityOnlyWhenActingReading InAct CanBe)
    (hSense : SomethingIsMovedReading MovedIn)
    (hNotYet : MovedNotYetInActReading MovedIn InAct)
    (hAble : MovedIsAbleToBeReading MovedIn CanBe) :
    TruthCore.Logic.ConfigurationFalse :=
  -- Compose the derived refutation; its reductio supplies the contradiction.
  megarianThesisFalse MovedIn InAct CanBe hSense hNotYet hAble hMegarian

end TruthCore.Results.Alternatives.MegarianCapacityCore
