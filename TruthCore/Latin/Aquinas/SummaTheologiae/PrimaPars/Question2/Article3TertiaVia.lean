/-!
Source-derived readings from Thomas Aquinas, *Summa theologiae* I q.2 a.3 co.,
the *tertia via* (argument from the possible and the necessary).

Vocabulary, all of it parameters:

* `Being` — the things quantified over (*res*, *entia*).
* `Time` with `Before t t'` (`t` is earlier than `t'`) and a present time `now`.
  Nothing makes `Before` a linear, dense or discrete order.
* `IsAt x t` — `x` is (exists) at time `t`.
* `Possible φ` — it is possible that `φ`, for a condition `φ` on times (such as
  "`x` is not"). Possibility is a primitive. It is deliberately **not** defined
  statistically (possible = realized at some time): the link between possibility
  and realization in time is exactly the contested plenitude premise, so it is
  stated as a premise (`PlenitudeOverInfinitePastReading`) and can be dropped.
* `CausesNecessityOf c x` — `c` is a cause of `x`'s necessity
  (*causa suae necessitatis*).

The propositional Kripke layer (`TruthCore.Modal`) is not used: the passage's
modality is temporal (*quod possibile est non esse, quandoque non est*), and its
contested step is the interplay of possibility, time and quantifiers over
beings, which the propositional language cannot express.

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-Q2-A3`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- `x` can not-be (*possibile non esse*): it is possible that `x` is not. -/
def PossibleNotToBe {Being : Sort u} {Time : Sort v}
    (Possible : (Time → Prop) → Prop) (IsAt : Being → Time → Prop) (x : Being) :
    Prop :=
  Possible (fun t => ¬ IsAt x t)

/-- `x` is necessary (*necessarium*): it cannot not-be. -/
def IsNecessary {Being : Sort u} {Time : Sort v}
    (Possible : (Time → Prop) → Prop) (IsAt : Being → Time → Prop) (x : Being) :
    Prop :=
  ¬ PossibleNotToBe Possible IsAt x

/-- `x` has a cause of its necessity from elsewhere (*habet causam suae
necessitatis aliunde*): something other than `x` causes its necessity. -/
def HasCauseOfNecessityAliunde {Being : Sort u}
    (CausesNecessityOf : Being → Being → Prop) (x : Being) : Prop :=
  ∃ c, c ≠ x ∧ CausesNecessityOf c x

/-- `x` is necessary per se (*per se necessarium, non habens causam necessitatis
aliunde*). -/
def IsNecessaryPerSe {Being : Sort u} {Time : Sort v}
    (Possible : (Time → Prop) → Prop) (IsAt : Being → Time → Prop)
    (CausesNecessityOf : Being → Being → Prop) (x : Being) : Prop :=
  IsNecessary Possible IsAt x ∧ ¬ HasCauseOfNecessityAliunde CausesNecessityOf x

/-- A link of the series *in necessariis quae habent causam suae necessitatis*:
`c` is a necessary being other than `y` that causes the necessity of the
necessary being `y`. -/
def NecessityCausedAmongNecessaries {Being : Sort u} {Time : Sort v}
    (Possible : (Time → Prop) → Prop) (IsAt : Being → Time → Prop)
    (CausesNecessityOf : Being → Being → Prop) (c y : Being) : Prop :=
  IsNecessary Possible IsAt c ∧ IsNecessary Possible IsAt y ∧ c ≠ y ∧
    CausesNecessityOf c y

/-- The past is infinite: no time up to now is the first time; before each there
is an earlier one. The hypothesis under which the plenitude reading's step
works. Aquinas does not assert it in q.2 a.3 (ST I q.46 a.2 holds that the
world's beginning is known by faith alone); it is an explicit premise. -/
def PastIsInfinite {Time : Sort v} (Before : Time → Time → Prop) (now : Time) :
    Prop :=
  ∀ t, (t = now ∨ Before t now) → ∃ t', Before t' t

/-- Reading A of *quod possibile est non esse, quandoque non est*, distributive:
each thing that can not-be is, at some time, not.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., tertia via.
-/
def WhatCanNotBeSometimeIsNotReading {Being : Sort u} {Time : Sort v}
    (Possible : (Time → Prop) → Prop) (IsAt : Being → Time → Prop) : Prop :=
  ∀ x, PossibleNotToBe Possible IsAt x → ∃ t, ¬ IsAt x t

/-- Reading B of *quod possibile est non esse, quandoque non est*, as an instance
of a principle of plenitude: given an infinite past, whatever is possible has
been realized at some past time (a possibility never realized in infinite time
is no possibility). Stated for every condition on times, so that it also
applies to "nothing is".

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., tertia via (plenitude
reading; the general principle is Aristotle's, *De caelo* I.12, not pinned).
-/
def PlenitudeOverInfinitePastReading {Time : Sort v}
    (Before : Time → Time → Prop) (now : Time)
    (Possible : (Time → Prop) → Prop) : Prop :=
  PastIsInfinite Before now → ∀ φ, Possible φ → ∃ t, Before t now ∧ φ t

/-- Collective reading of *Si igitur omnia sunt possibilia non esse*: if every
being can not-be, then it is possible that nothing is (all of them at once).
This is the modal counterpart of the quantifier shift: it moves from
"each can not-be" to "possibly none is".

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., tertia via
(collective reading of *omnia*).
-/
def AllCanNotBeThenNothingPossibleReading {Being : Sort u} {Time : Sort v}
    (Possible : (Time → Prop) → Prop) (IsAt : Being → Time → Prop) : Prop :=
  (∀ x, PossibleNotToBe Possible IsAt x) → Possible (fun t => ∀ x, ¬ IsAt x t)

/-- The contested step: if everything can not-be, then at some (past) time
nothing was (*Si igitur omnia sunt possibilia non esse, aliquando nihil fuit in
rebus*).

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., tertia via.
-/
def IfAllCanNotBeThenOnceNothingReading {Being : Sort u} {Time : Sort v}
    (Possible : (Time → Prop) → Prop) (IsAt : Being → Time → Prop)
    (Before : Time → Time → Prop) (now : Time) : Prop :=
  (∀ x, PossibleNotToBe Possible IsAt x) → ∃ t, Before t now ∧ ∀ x, ¬ IsAt x t

/-- What is not begins to be only through something that is (*quod non est, non
incipit esse nisi per aliquid quod est*), in the interval reading the next clause
uses (*si igitur nihil fuit ens, impossibile fuit quod aliquid inciperet esse*):
whatever is not at an earlier time and is at a later one began to be through
something that was at that earlier time, so something was then.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., tertia via.
-/
def NothingBeginsExceptThroughWhatIsReading {Being : Sort u} {Time : Sort v}
    (IsAt : Being → Time → Prop) (Before : Time → Time → Prop) : Prop :=
  ∀ x t0 t, Before t0 t → ¬ IsAt x t0 → IsAt x t → ∃ y, IsAt y t0

/-- Something now is: that now nothing would be *patet esse falsum*.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., tertia via.
-/
def SomethingNowIsReading {Being : Sort u} {Time : Sort v}
    (IsAt : Being → Time → Prop) (now : Time) : Prop :=
  ∃ x, IsAt x now

/-- Something is necessary (*Non ergo omnia entia sunt possibilia: sed oportet
aliquid esse necessarium in rebus*).

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., tertia via.
-/
def SomethingIsNecessaryReading {Being : Sort u} {Time : Sort v}
    (Possible : (Time → Prop) → Prop) (IsAt : Being → Time → Prop) : Prop :=
  ∃ x, IsNecessary Possible IsAt x

/-- Every necessary being either has the cause of its necessity from elsewhere or
not (*Omne autem necessarium vel habet causam suae necessitatis aliunde, vel non
habet*). An instance of excluded middle.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., tertia via.
-/
def NecessaryHasCauseOfNecessityOrNotReading {Being : Sort u} {Time : Sort v}
    (Possible : (Time → Prop) → Prop) (IsAt : Being → Time → Prop)
    (CausesNecessityOf : Being → Being → Prop) : Prop :=
  ∀ x, IsNecessary Possible IsAt x →
    HasCauseOfNecessityAliunde CausesNecessityOf x ∨
      ¬ HasCauseOfNecessityAliunde CausesNecessityOf x

/-- What causes the necessity of a necessary being is itself necessary: the
regress Aquinas excludes runs *in necessariis quae habent causam suae
necessitatis*, a series whose members are all necessary.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., tertia via.
-/
def CauseOfNecessityIsNecessaryReading {Being : Sort u} {Time : Sort v}
    (Possible : (Time → Prop) → Prop) (IsAt : Being → Time → Prop)
    (CausesNecessityOf : Being → Being → Prop) : Prop :=
  ∀ c x, IsNecessary Possible IsAt x → CausesNecessityOf c x →
    IsNecessary Possible IsAt c

/-- There is no infinite regress among necessary beings that have a cause of
their necessity (*Non est autem possibile quod procedatur in infinitum in
necessariis quae habent causam suae necessitatis, sicut nec in causis
efficientibus, ut probatum est*). Formalized as well-foundedness of
`NecessityCausedAmongNecessaries`. The back-reference to the *secunda via* is
recorded in the claim, not formalized.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., tertia via.
-/
def NoInfiniteRegressInCausedNecessariesReading {Being : Sort u} {Time : Sort v}
    (Possible : (Time → Prop) → Prop) (IsAt : Being → Time → Prop)
    (CausesNecessityOf : Being → Being → Prop) : Prop :=
  ∀ x, Acc (NecessityCausedAmongNecessaries Possible IsAt CausesNecessityOf) x

/-- Something is necessary per se, and it is the cause of necessity to others
(*Ergo necesse est ponere aliquid quod sit per se necessarium, non habens causam
necessitatis aliunde, sed quod est causa necessitatis aliis*).

"Cause of necessity to others" is read in the weakest form the argument gives:
every necessary being is either necessary per se or has its necessity, through
a finite chain of necessary causes, from some being necessary per se. It does not
say that one and the same being is the source for all (no uniqueness), and
*quod omnes dicunt Deum* is a separate claim.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., tertia via.
-/
def NecessaryPerSeBeingReading {Being : Sort u} {Time : Sort v}
    (Possible : (Time → Prop) → Prop) (IsAt : Being → Time → Prop)
    (CausesNecessityOf : Being → Being → Prop) : Prop :=
  (∃ n, IsNecessaryPerSe Possible IsAt CausesNecessityOf n) ∧
    ∀ x, IsNecessary Possible IsAt x →
      ∃ n, IsNecessaryPerSe Possible IsAt CausesNecessityOf n ∧
        (n = x ∨ Relation.TransGen
          (NecessityCausedAmongNecessaries Possible IsAt CausesNecessityOf) n x)

/-! ## The eternal-world dilemma (owner decision on #143, 2026-10-24)

The rival to collective possibility, perpetual succession of contingents
(`STMT-PERPETUAL-SUCCESSION-OF-CONTINGENTS`), needs a past without beginning.
SCG I.13 [29]-[30] splits the question accordingly: the proofs are argued on the
supposition that the world is eternal, and if it is not, its beginning needs an
innovating cause. -/

/-- The past is finite: some time up to now has no earlier time. The other horn
of the eternal-world dilemma; it is the classical negation of
`PastIsInfinite`. -/
def PastIsFinite {Time : Sort v} (Before : Time → Time → Prop) (now : Time) : Prop :=
  ∃ t, (t = now ∨ Before t now) ∧ ∀ t', ¬ Before t' t

/-- The rival's succession: beings succeed one another without beginning, so
whenever something is, something was earlier (each generated by a predecessor).
This is the part of perpetual succession that its denial of collective
possibility rests on. It has no source claim: the rival waits for a witness. -/
def BeingsSucceedWithoutBeginning {Being : Sort u} {Time : Sort v}
    (IsAt : Being → Time → Prop) (Before : Time → Time → Prop) : Prop :=
  ∀ x t, IsAt x t → ∃ t', Before t' t ∧ ∃ y, IsAt y t'

end TruthCore.Latin.Aquinas.SummaTheologiae
