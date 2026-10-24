import TruthCore.Case.Catholicism.StageOne
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuintaVia

/-!
Stage-1 statement that connects the *quinta via*'s intelligent director (ST I q.2
a.3, fifth way; #148) with the *prima via*'s first mover moved by none (#151).

The *quinta via*'s premises give only "each natural body is directed by some
knower". The step to one director of all is made through the stage-1 uniqueness
statement `AtMostOneFirstUnmovedMover` and two bridges,
`NaturalDirectionReducedToIntelligentImmobileDirector` and `DirectingIsMoving`.
No sentence of q.2 a.3 states either of them; ad 2 and the arrow simile only
bear on them (`supports` relations). Each is shown necessary by a countermodel in
result `AQUINAS-ST-I-Q2-A3-QUINTA-VIA-ONE-GOVERNOR`, and each is derived from ST I
q.103 (`AQUINAS-ST-I-Q103-DIRECTING-IS-MOVING`, `AQUINAS-ST-I-Q103-DIRECTOR-REGRESS`).
-/

namespace TruthCore.Case.Catholicism

universe u v w

/-- Whatever directs a natural body to an end, that body is also directed to the
same end by a knowing, intelligent director that is moved in no respect. Derived
in result `AQUINAS-ST-I-Q103-DIRECTOR-REGRESS` (regress of directors, ST I q.103 a.6;
owner decision on #143, 2026-10-24); first introduced as an open bridge. ST I q.2 a.3 ad 2 bears on
it but does not state it: ad 2 reduces what nature does for an end to God as
first cause and to a first immovable principle (claim
`AQUINAS-ST-I-Q2-A3-AD2-REDUCTION-TO-IMMOBILE-FIRST-A`). That a first cause also
directs the body to the same end, and that it is knowing and intelligent, are the
steps still to be argued. It does not say the first director is unique. -/
def NaturalDirectionReducedToIntelligentImmobileDirector {Being : Sort u}
    {Respect : Sort v} {End : Sort w}
    (MovedIn : Being → Respect → Prop)
    (NaturalBody HasCognition Intelligent : Being → Prop)
    (Directs : Being → Being → End → Prop) : Prop :=
  ∀ d x e, NaturalBody x → Directs d x e →
    ∃ f, HasCognition f ∧ Intelligent f ∧ (∀ r, ¬ MovedIn f r) ∧ Directs f x e

/-- To direct a thing to an end is to move it in some respect, in the *prima via*'s
sense of moving. Derived in result `AQUINAS-ST-I-Q103-DIRECTING-IS-MOVING` (ST I q.103 a.3,
a.5 ad 2); first introduced as an open bridge. The
arrow simile (*sicut sagitta a sagittante*) illustrates it for the archer only. -/
def DirectingIsMoving {Being : Sort u} {Respect : Sort v} {End : Sort w}
    (MovesIn : Being → Being → Respect → Prop)
    (Directs : Being → Being → End → Prop) : Prop :=
  ∀ d x e, Directs d x e → ∃ r, MovesIn d x r

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
