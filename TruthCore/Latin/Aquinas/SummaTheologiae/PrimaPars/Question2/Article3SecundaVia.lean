import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1

/-!
Source-derived readings from Thomas Aquinas, *Summa theologiae* I q.2 a.3 co.,
the *secunda via* (argument from the nature of the efficient cause).

The vocabulary of the *prima via* (`Being`, `Respect`; see `Question2.Article3`)
is reused. `PriorSimply` of ST I q.3 a.1 (`Question3.Article1`) is reused for the
priority of a cause over its effect (*sic esset prius seipso*): both are priority
of nature, not of time (the hand and the stick act together), and both say that
what is posterior depends for its being in act on what is prior. New vocabulary,
all of it parameters:

* `EfficientlyCausesIn c x r` — `c` is, here and now, an efficient cause of `x`'s
  being `r`. It is not identified with the *prima via*'s `MovesIn`, nor with the
  *quarta via*'s `CausesIn`, whose kind of causality (efficient or exemplar) the
  fourth way leaves open. Relating them is left to explicit, sourced premises.
* `CausesAsCaused c x` — `c` causes `x` only insofar as `c` is itself caused:
  `c` is a middle cause (*medium*) of a per se ordered series. This is the per se
  link, as `MovesAsMoved` is for movers.

All predicates are read at one and the same time, as in the *prima via*: the
series is a present order of causes, not a history of generations.

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-Q2-A3`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- `f` is a first efficient cause: it efficiently causes something and is
efficiently caused by nothing. -/
def IsFirstEfficientCause {Being : Sort u} {Respect : Sort v}
    (EfficientlyCausesIn : Being → Being → Respect → Prop) (f : Being) : Prop :=
  (∃ x r, EfficientlyCausesIn f x r) ∧ ∀ c r, ¬ EfficientlyCausesIn c f r

/-- In sensible things there is an order of efficient causes (*Invenimus enim in
istis sensibilibus esse ordinem causarum efficientium*).

Only the weakest content is asserted: something efficiently causes something.
That the order is a per se order is the separate premise
`SecondEfficientCausesCauseOnlyAsCausedReading`.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., second way.
-/
def OrderOfEfficientCausesFoundReading {Being : Sort u} {Respect : Sort v}
    (EfficientlyCausesIn : Being → Being → Respect → Prop) : Prop :=
  ∃ c x r, EfficientlyCausesIn c x r

/-- An efficient cause is prior to its effect (*quia sic esset prius seipso*: a
self-cause would be prior to itself).

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., second way.
-/
def EfficientCauseIsPriorToEffectReading {Being : Sort u} {Respect : Sort v}
    (EfficientlyCausesIn : Being → Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop) : Prop :=
  ∀ c x r, EfficientlyCausesIn c x r → PriorSimply c x

/-- Nothing is prior to itself (*prius seipso, quod est impossibile*).

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., second way.
-/
def NothingPriorToItselfReading {Being : Sort u}
    (PriorSimply : Being → Being → Prop) : Prop :=
  ∀ x, ¬ PriorSimply x x

/-- Nothing is the efficient cause of itself (*nec tamen invenitur, nec est
possibile, quod aliquid sit causa efficiens sui ipsius*), in any respect.
Derived in result `AQUINAS-ST-I-Q2-A3-SECUNDA-VIA` from the two priority
premises.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., second way.
-/
def NothingIsEfficientCauseOfItselfReading {Being : Sort u} {Respect : Sort v}
    (EfficientlyCausesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ x r, ¬ EfficientlyCausesIn x x r

/-- In ordered efficient causes the first is the cause of the middle and the
middle of the last; and when the cause is removed, the effect is removed (*in
omnibus causis efficientibus ordinatis, primum est causa medii, et medium est
causa ultimi ... remota autem causa, removetur effectus*).

Read as the per se ordering premise, parallel to the *prima via*'s
`SecondMoversMoveOnlyAsMovedReading` (strong reading A; the weaker sibling is
`SecondEfficientCausesCauseAsCausedInRelevantRespectReading`): an efficient cause other
than its effect that is itself efficiently caused is a middle cause, causing only
as caused (`CausesAsCaused`). Per accidens series (a father who begets, himself
begotten) are not present series and are not covered.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., second way.
-/
def SecondEfficientCausesCauseOnlyAsCausedReading
    {Being : Sort u} {Respect : Sort v}
    (EfficientlyCausesIn : Being → Being → Respect → Prop)
    (CausesAsCaused : Being → Being → Prop) : Prop :=
  ∀ c x r, c ≠ x → EfficientlyCausesIn c x r →
    (∃ d r', EfficientlyCausesIn d c r') → CausesAsCaused c x

/-- Weaker sibling reading of *primum est causa medii, et medium est causa ultimi
... remota autem causa, removetur effectus*: an efficient cause other than its
effect that is itself caused in a respect relevant to its causing that effect is
thereby a middle cause of the series. The premise is one-directional: it does not
say that only such causes are middle causes.

`RelevantTo c x r r'` says that `c`'s being caused in `r'` bears on `c`'s causing
`x` in `r`. A cause caused only in irrelevant respects (a man nourished while he
moves a stick; *generat enim inquantum homo*, ST I q.46 a.2 ad 7, reading B) is
not thereby a per se link. This parallels the *prima via*'s
`SecondMoversMoveAsMovedInRelevantRespectReading`. The result
`AQUINAS-ST-I-Q2-A3-SECUNDA-VIA` uses the strong reading
`SecondEfficientCausesCauseOnlyAsCausedReading`, not this one; on this reading
the argument yields at most a cause uncaused *in the relevant respects*.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., second way (weaker
reading).
-/
def SecondEfficientCausesCauseAsCausedInRelevantRespectReading
    {Being : Sort u} {Respect : Sort v}
    (EfficientlyCausesIn : Being → Being → Respect → Prop)
    (CausesAsCaused : Being → Being → Prop)
    (RelevantTo : Being → Being → Respect → Respect → Prop) : Prop :=
  ∀ c x r r', c ≠ x → EfficientlyCausesIn c x r →
    (∃ d, EfficientlyCausesIn d c r') → RelevantTo c x r r' → CausesAsCaused c x

/-- Among efficient causes one cannot proceed to infinity (*Non autem est possibile
quod in causis efficientibus procedatur in infinitum*), restricted, as ST I q.46
a.2 ad 7 restricts it, to per se ordered causes.

Formalized as well-foundedness of the per se link, exactly as the *prima via*'s
`NoInfinitePerSeMoverSeriesReading` is for `MovesAsMoved`. It is its own
statement: the two are related by result
`AQUINAS-ST-I-Q46-A2-AD7-MOVER-REGRESS-FROM-CAUSE-REGRESS` through a sourced link
premise, not identified.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., second way; I q.46 a.2
ad 7.
-/
def NoInfinitePerSeEfficientCauseSeriesReading {Being : Sort u}
    (CausesAsCaused : Being → Being → Prop) : Prop :=
  ∀ x, Acc CausesAsCaused x

/-- It is necessary to posit some first efficient cause (*Ergo est necesse ponere
aliquam causam efficientem primam*).

Stated, like the *prima via*'s conclusion, as the impossibility of there being
none, which keeps the result axiom-free. It does not identify the first efficient
cause with God; *quam omnes Deum nominant* is a separate claim.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., second way.
-/
def FirstEfficientCauseCannotBeLackingReading {Being : Sort u} {Respect : Sort v}
    (EfficientlyCausesIn : Being → Being → Respect → Prop) : Prop :=
  ¬ ¬ ∃ f, IsFirstEfficientCause EfficientlyCausesIn f

/-- A per se link of a series of moved movers is a per se link of a series of
efficient causes: whatever moves only as moved causes only as caused. ST I q.46
a.2 ad 7 gives the *prima via*'s own series (stone, stick, hand) as its example of
efficient causes *quae per se requiruntur ad aliquem effectum*.

Source: Thomas Aquinas, *Summa theologiae* I q.46 a.2 ad 7.
-/
def PerSeMoverLinkIsPerSeCauseLinkReading {Being : Sort u}
    (MovesAsMoved CausesAsCaused : Being → Being → Prop) : Prop :=
  ∀ y x, MovesAsMoved y x → CausesAsCaused y x

end TruthCore.Latin.Aquinas.SummaTheologiae
