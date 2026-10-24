/-!
Source-derived readings from Thomas Aquinas, *Summa theologiae* I q.103 (*de
gubernatione rerum*), a.3, a.5 ad 2 and a.6, used to close the *quinta via*'s
scope bridges (owner decision on #143, 2026-10-24: ST I q.103 plus a regress of
directors).

Basis: the English Dominican translation (2nd rev. ed. 1920), pinned as the web
snapshot `AQUINAS-ST-I-Q103-*-EN` (the SCTA witness has no transcription of
q.103); claims on it carry `basis: translation`.

Vocabulary as in the *quinta via* and the *prima via*: `Directs d x e` (`d`
directs `x` to the end `e`), `MovesIn y x r`, `MovedIn x r`, `HasCognition`,
`Intelligent`; and `Governs d x`, `d` governs `x`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v w

/-- Government is nothing but directing things to their end: whoever directs a
thing to an end governs it ("government is nothing but the directing of the
things governed to the end; which consists in some good"). Only the direction
the argument needs is formalized: directing is governing.

Source: Thomas Aquinas, *Summa theologiae* I q.103 a.3 co. (English Dominican
translation).
-/
def DirectingToAnEndIsGoverningReading {Being : Sort u} {End : Sort w}
    (Directs : Being → Being → End → Prop) (Governs : Being → Being → Prop) : Prop :=
  ∀ d x e, Directs d x e → Governs d x

/-- Government implies a change effected by the governor in what it governs:
"Government implies a certain change effected by the governor in the things
governed. Now every movement is the act of a movable thing, caused by the moving
principle." Read as: a governor moves what it governs in some respect, in the
*prima via*'s sense of moving.

Source: Thomas Aquinas, *Summa theologiae* I q.103 a.5 ad 2 (English Dominican
translation).
-/
def GovernmentEffectsChangeReading {Being : Sort u} {Respect : Sort v}
    (MovesIn : Being → Being → Respect → Prop) (Governs : Being → Being → Prop) : Prop :=
  ∀ d x, Governs d x → ∃ r, MovesIn d x r

/-- In the execution of government God "governs some things by means of others":
he makes some things "causes of others in government". Read as the transitivity
the regress of directors needs: whoever moves a director (other than itself)
directs, through it, what that director directs, to the same end.

This is an interpretive step. a.6 speaks of the first governor using
intermediaries; the reading extends it to every mover of a director, as the
*prima via* does for every mover of a mover.

Source: Thomas Aquinas, *Summa theologiae* I q.103 a.6 co. (English Dominican
translation).
-/
def DirectionThroughIntermediariesReading {Being : Sort u} {Respect : Sort v}
    {End : Sort w}
    (MovesIn : Being → Being → Respect → Prop) (Directs : Being → Being → End → Prop) :
    Prop :=
  ∀ g f x e r, Directs f x e → MovesIn g f r → g ≠ f → Directs g x e

/-- The first director has the design of government, which is providence: "In
government there are two things to be considered; the design of government,
which is providence itself; and the execution of the design. As to the design of
government, God governs all things immediately; whereas in its execution, He
governs some things by means of others." Read as: a director moved by none
directs by its own design, not as executing another's, so it knows and
understands (providence belongs to knowledge and intellect).

Source: Thomas Aquinas, *Summa theologiae* I q.103 a.6 co. (English Dominican
translation).
-/
def UnmovedDirectorHasTheDesignReading {Being : Sort u} {Respect : Sort v}
    {End : Sort w}
    (MovedIn : Being → Respect → Prop)
    (HasCognition Intelligent : Being → Prop)
    (Directs : Being → Being → End → Prop) : Prop :=
  ∀ h x e, Directs h x e → (∀ r, ¬ MovedIn h r) → HasCognition h ∧ Intelligent h

end TruthCore.Latin.Aquinas.SummaTheologiae
