import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3

/-!
Source-derived readings from Thomas Aquinas, *Summa theologiae* I q.2 a.3 co.,
the *quarta via* (argument from the grades found in things).

The vocabulary of the *prima via* (`Being`, `Respect`, `InAct`; see
`Question2.Article3`) is reused. A respect is read here as a perfection, as in
ST I q.4 a.1 (*secundum hoc dicitur aliquid esse perfectum, secundum quod est
actu*) and in the reading of q.11 a.3: `InAct x r` says that `x` has the
perfection `r`. New vocabulary, all of it parameters:

* `MoreIn r x y` — `x` is more `r` than `y` (*magis*): more good, more true,
  more noble, more hot. Only the comparative is primitive; nothing makes it a
  total order or a measure.
* `CausesIn c x r` — `c` is a cause of `x`'s being `r` (of the perfection `r` in
  `x`), as fire is a cause of the heat of hot things. It is not identified with
  `MovesIn`: causing a perfection need not be a present reduction from potency
  to act.
* distinguished respects `bonum`, `verum`, `nobile` and `esse`: being good,
  being true, being noble and being (having *esse*, the actuality of all
  things, q.4 a.1 ad 3).

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-Q2-A3`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- `m` has the perfection `r` and nothing is more `r` than it.
This is the weakest maximal reading of *maxime tale*, not greatestness:
no comparison with every other being, uniqueness or totality is asserted. -/
def IsMaximalIn {Being : Sort u} {Respect : Sort v}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (r : Respect) (m : Being) : Prop :=
  InAct m r ∧ ∀ y, ¬ MoreIn r y m

/-- Compatibility name for the existing source reading. The body is exactly
`IsMaximalIn`; existing statement identities and theorem interfaces retain this
name. On a homogeneous preorder this corresponds to Mathlib `IsMax`, not
`IsGreatest`. See `DISAMB-MAXIME-ENS`. -/
def IsMaximumIn {Being : Sort u} {Respect : Sort v}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (r : Respect) (m : Being) : Prop :=
  IsMaximalIn InAct MoreIn r m

/-- `c` is the cause of everything else in the genus `r` (*causa omnium quae sunt
illius generis*): of every other thing that has `r`, `c` causes its being `r`.
`c` itself is excluded: fire is not said to cause its own heat. -/
def CausesAllInGenus {Being : Sort u} {Respect : Sort v}
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (r : Respect) (c : Being) : Prop :=
  ∀ x, x ≠ c → InAct x r → CausesIn c x r

/-- Grades are found in things: something is more and something less good, true
and noble (*Invenitur enim in rebus aliquid magis et minus bonum, et verum, et
nobile*).

Only the three named perfections are asserted; *et sic de aliis huiusmodi* is
not formalized. Like the *prima via*'s *sensu constat*, this is an observation
premise.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., fourth way.
-/
def GradesFoundInThingsReading {Being : Sort u} {Respect : Sort v}
    (MoreIn : Respect → Being → Being → Prop) (bonum verum nobile : Respect) :
    Prop :=
  (∃ x y, MoreIn bonum x y) ∧ (∃ x y, MoreIn verum x y) ∧
    (∃ x y, MoreIn nobile x y)

/-- More and less are said of diverse things according as they approach in
diverse ways something that is maximally (*magis et minus dicuntur de diversis
secundum quod appropinquant diversimode ad aliquid quod maxime est: sicut magis
calidum est, quod magis appropinquat maxime calido*).

Formalized as the step the argument takes from it (*Est igitur aliquid quod est
verissimum, et optimum, et nobilissimum*): wherever there are grades of a
perfection, there is a maximum in it. This is the premise that a gradation
without a highest member (as in an unbounded scale) would falsify; the
countermodel `TruthCore.Results.Aquinas.SummaTheologiae.QuartaVia.quartaViaNeedsMaximum`
shows the argument needs it. The approach relation itself (the more is nearer
the maximum) is not formalized.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., fourth way.
-/
def GradesByApproachToAMaximumReading {Being : Sort u} {Respect : Sort v}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) : Prop :=
  ∀ r, (∃ x y, MoreIn r x y) → ∃ m, IsMaximumIn InAct MoreIn r m

/-- What is maximally true is maximally being (*et per consequens maxime ens: nam
quae sunt maxime vera, sunt maxime entia, ut dicitur II Metaphys.*; Aristotle,
*Metaphysics* II.1, 993b30-31: as each thing stands to being, so to truth).

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., fourth way.
-/
def MostTrueIsMostBeingReading {Being : Sort u} {Respect : Sort v}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (verum esse : Respect) : Prop :=
  ∀ m, IsMaximumIn InAct MoreIn verum m → IsMaximumIn InAct MoreIn esse m

/-- What is called maximally such in a genus is the cause of all that are of that
genus (*Quod autem dicitur maxime tale in aliquo genere, est causa omnium quae
sunt illius generis: sicut ignis, qui est maxime calidus, est causa omnium
calidorum, ut in eodem libro dicitur*).

Stated, as in the text, for every genus (every perfection `r`). The argument
uses only the instance `r = esse`. Aristotle's sentence that Aquinas cites
(*Metaphysics* II.1, 993b24-26) runs the other way, from being the cause to
being most such.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., fourth way.
-/
def MaximumInGenusCausesAllInGenusReading {Being : Sort u} {Respect : Sort v}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ r m, IsMaximumIn InAct MoreIn r m → CausesAllInGenus InAct CausesIn r m

/-- There is something maximally being that is the cause of being to all other
beings (*Ergo est aliquid quod omnibus entibus est causa esse*).

Only the cause of *esse* is formalized. The further clauses *et bonitatis, et
cuiuslibet perfectionis* are not: applying the genus principle to goodness gives
a maximum in goodness that causes goodness, but nothing in the text makes it the
same being as the maximum in being. The closing *et hoc dicimus Deum* is a
separate claim and is not formalized.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., fourth way.
-/
def MaximeEnsCausesBeingOfAllReading {Being : Sort u} {Respect : Sort v}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∃ m, IsMaximumIn InAct MoreIn esse m ∧ CausesAllInGenus InAct CausesIn esse m

end TruthCore.Latin.Aquinas.SummaTheologiae
