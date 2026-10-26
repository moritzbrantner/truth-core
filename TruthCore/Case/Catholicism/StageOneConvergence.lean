import TruthCore.Case.Catholicism.StageOneQuartaVia
import TruthCore.Case.Catholicism.StageOneQuintaVia
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3TertiaVia

/-!
Convergence of the Ways on the *quarta via*'s maximal being (*maxime ens*), the
being that stage 1 identifies with God (#143, handoff 2026-10-24: "make the Ways
converge"). The *prima via*'s first mover is already the maximal being
(`FirstUnmovedMoverIsMaximeEns`). This module adds the *tertia via*'s per se
necessary being and the *quinta via*'s governor.

The *tertia via* is stated in a temporal-modal vocabulary (`Possible`, `IsAt`),
and the *quarta via* in the vocabulary of act and causes of being (`InAct`,
`CausesIn`). The two bridges below connect them over the same `Being` type. Both
are open premises. SCG I.15 [5], which identifies the first being necessary
through itself with God "since He is the first cause", supports them without
stating them.
-/

namespace TruthCore.Case.Catholicism

open TruthCore.Latin.Aquinas.SummaTheologiae

universe u v w x

/-- A necessary being has being: what cannot not-be is in act as to *esse*. Open
bridge between the *tertia via*'s modal vocabulary and the *quarta via*'s. -/
def NecessaryBeingHasBeing {Being : Sort u} {Time : Sort v} {Respect : Sort w}
    (Possible : (Time → Prop) → Prop) (IsAt : Being → Time → Prop)
    (InAct : Being → Respect → Prop) (esse : Respect) : Prop :=
  ∀ x, IsNecessary Possible IsAt x → InAct x esse

/-- Whatever causes the being of a necessary being causes its necessity: the
necessity of a necessary being is the necessity of its being, so a cause of that
being is a cause of its necessity. Open bridge. -/
def CauseOfNecessaryBeingCausesItsNecessity {Being : Sort u} {Time : Sort v}
    {Respect : Sort w}
    (Possible : (Time → Prop) → Prop) (IsAt : Being → Time → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (CausesNecessityOf : Being → Being → Prop) : Prop :=
  ∀ c x, IsNecessary Possible IsAt x → CausesIn c x esse → CausesNecessityOf c x

/-- Every being necessary per se is the maximal being: it is identical with every
being that is maximal in being. Derived in result
`TERTIA-VIA-NECESSARY-PER-SE-IS-MAXIME-ENS`. -/
def NecessaryPerSeIsMaximeEns {Being : Sort u} {Time : Sort v} {Respect : Sort w}
    (Possible : (Time → Prop) → Prop) (IsAt : Being → Time → Prop)
    (CausesNecessityOf : Being → Being → Prop)
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect) : Prop :=
  ∀ n, IsNecessaryPerSe Possible IsAt CausesNecessityOf n →
    ∀ m, IsMaximumIn InAct MoreIn esse m → n = m

/-- Some being maximal in being is the intelligent governor of nature: something maximal in
being is intelligent and directs every natural body to an end. Derived in result
`QUINTA-VIA-GOVERNOR-IS-MAXIME-ENS`. -/
def MaximeEnsGovernsNature {Being : Sort u} {Respect : Sort v} {End : Sort x}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect)
    (NaturalBody Intelligent : Being → Prop)
    (Directs : Being → Being → End → Prop) : Prop :=
  ∃ m, IsMaximumIn InAct MoreIn esse m ∧ Intelligent m ∧
    ∀ y, NaturalBody y → ∃ e, Directs m y e

end TruthCore.Case.Catholicism
