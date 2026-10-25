/-!
Source-derived readings and two open bridges from Thomas Aquinas, *Summa theologiae* I q.103 (*de
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

/-- Direction passes to the movers of a director: whoever moves a director
(other than itself) directs, through it, what that director directs, to the same
end. Open bridge, not a reading (Codex P1 on #196): q.103 a.6 says that God
"governs some things by means of others", making some things "causes of others
in government" (claim `AQUINAS-ST-I-Q103-A6-THROUGH-INTERMEDIARIES`, which
supports it). It does not say that every mover of a director, in any respect,
directs the director's effect; that generalization, and the instrumental
dependence it presupposes, are the open obligation. -/
def DirectionPassesToMoversOfDirectors {Being : Sort u} {Respect : Sort v}
    {End : Sort w}
    (MovesIn : Being → Being → Respect → Prop) (Directs : Being → Being → End → Prop) :
    Prop :=
  ∀ g f x e r, Directs f x e → MovesIn g f r → g ≠ f → Directs g x e

/-- A director moved by none knows and understands. Open bridge, not a reading
(Codex P1 on #196): q.103 a.6 attributes the design of government, which is
providence, to God (claim `AQUINAS-ST-I-Q103-A6-DESIGN-OF-GOVERNMENT`, which
supports it); it does not infer the design from being an unmoved director.
The step from first in the series of directors to knowing and intelligent is
the open obligation. -/
def UnmovedDirectorKnowsAndUnderstands {Being : Sort u} {Respect : Sort v}
    {End : Sort w}
    (MovedIn : Being → Respect → Prop)
    (HasCognition Intelligent : Being → Prop)
    (Directs : Being → Being → End → Prop) : Prop :=
  ∀ h x e, Directs h x e → (∀ r, ¬ MovedIn h r) → HasCognition h ∧ Intelligent h

end TruthCore.Latin.Aquinas.SummaTheologiae
