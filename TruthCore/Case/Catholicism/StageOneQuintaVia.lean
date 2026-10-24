import TruthCore.Case.Catholicism.StageOne
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuintaVia

/-!
Stage-1 statement that connects the *quinta via*'s intelligent director (ST I q.2
a.3, fifth way; #148) with the *prima via*'s first mover moved by none (#151).

The *quinta via*'s premises give only "each natural body is directed by some
knower". The step to one director of all is made through the stage-1 uniqueness
statement `AtMostOneFirstUnmovedMover`, using two sourced readings (ad 2's
reduction to an immovable first principle, and directing as moving).
-/

namespace TruthCore.Case.Catholicism

universe u v w

/-- One intelligent first mover moved by none directs every natural body to an
end. Derived in result `AQUINAS-ST-I-Q2-A3-QUINTA-VIA-ONE-GOVERNOR`. It entails
the *quinta via*'s literal conclusion
(`TruthCore.Latin.Aquinas.SummaTheologiae.OneIntelligentDirectsAllNaturalThingsReading`). -/
def OneIntelligentFirstMoverGovernsNature {Being : Sort u} {Respect : Sort v}
    {End : Sort w}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (NaturalBody Intelligent : Being → Prop)
    (Directs : Being → Being → End → Prop) : Prop :=
  ∃ d, IsFirstUnmovedMover MovedIn MovesIn d ∧ Intelligent d ∧
    ∀ x, NaturalBody x → ∃ e, Directs d x e

end TruthCore.Case.Catholicism
