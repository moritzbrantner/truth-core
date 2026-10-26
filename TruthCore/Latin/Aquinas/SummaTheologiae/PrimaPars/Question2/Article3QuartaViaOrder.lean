import Mathlib.Order.Bounds.Basic
import TruthCore.Case.Catholicism.StageOneQuartaVia
import TruthCore.Greek.Aristotle.Metaphysics
import TruthCore.Logic.ExcludedMiddle

/-!
Order models of *more and less in being* (issue #340, item 3).

The *quarta via* speaks of things that are more and less beings (`MoreIn esse`).
`DISAMB-BEING-UNIVOCITY` records two senses of *being*. This file gives each
sense an order model in Mathlib's order theory, so that the frontier premises
can be tested on each (`DISAMB-ORDER-OF-BEING`):

* `HomogeneousScaleReading` — the **univocal** reading (`DEF-HOMOGENEOUS-SCALE`):
  more being is the strict part of one preorder on one domain, and every member
  of the domain has the perfection. The maximum, if any, is one grade among the
  others (Mathlib `IsMax`), as a proportioned measure is homogeneous with what it
  measures (ST I q.3 a.5 ad 2; q.13 a.5 arg. 3). It is a contrast reading: Aquinas
  denies that being is said univocally of God and creatures (q.13 a.5 co.).
* `ApproachToPrimaryReading` — the reading by **attribution** (`DEF-ORDER-BY-APPROACH-TO-A-PRIMARY`):
  one thing is more a being than another exactly when it approaches a primary
  `p` more nearly (q.3 a.5 ad 2: *unumquodque tantum habet de esse, quantum ei
  appropinquat*).
* `StrictPrimacyReading` — **strict primacy** (`DEF-STRICT-PRIMACY`): every
  other thing falls short of `p`. An open premise, not attributed to q.3 a.5
  ad 2; the results that need it take it as a separate hypothesis.
* `OrderedToPrimaryAsCauseReading` — Aquinas' account of what the order *to* the
  primary is for God and creatures (q.13 a.5 co.: *ordo creaturae ad Deum, ut ad
  principium et causam*): the primary causes the perfection in every creature
  that has it.
* `OthersAreCreaturesReading` — everything other than the primary is a
  creature (`DEF-CREATURE`). An open premise, not attributed to q.13 a.5.

Order shape alone does not tell the two readings apart. If every represented
being has the perfection (`∀ x, InAct x r`), an order by approach to a primary
is a homogeneous scale for the preorder pulled back along `near`
(`ApproachToPrimaryReading.homogeneousLift`). The attribution reading itself
requires only the primary to have the perfection, so the universal possession
condition is additional. Strict primacy and the causal clause of q.13 a.5 are
further separate conditions used by the results below.

The degrees of approach live in their own preorder `Degree`, with `near x` the
degree to which `x` approaches the primary. Nothing makes `Degree` total,
antisymmetric or bounded. `p` need not be God in the definitions; the claims say
which source fixes it.

Source witnesses: SCTA diplomatic TEI of the Leonine edition, passages
`AQUINAS-ST-I-Q3-A5` and `AQUINAS-ST-I-Q13-A5`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism (SimplyPriorIsCauseOfBeing MaximumInBeingIsFirstBeing)

universe u v w

/-- The univocal reading as an order (`DEF-HOMOGENEOUS-SCALE`): every being has
the perfection `r`, and `x` is more `r` than `y` exactly when `y < x` in one
preorder on the beings. Ties are allowed (a preorder, not a partial order), and
nothing distinguishes a maximum from the other grades except its place on the
scale.

Stipulative contrast reading, not attributed to Aquinas (`DEF-BEING-UNIVOCAL`). -/
def HomogeneousScaleReading {Being : Type u} {Respect : Sort v} [Preorder Being]
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (r : Respect) : Prop :=
  (∀ x, InAct x r) ∧ ∀ x y, MoreIn r x y ↔ y < x

/-- The reading by attribution as an order (`DEF-ORDER-BY-APPROACH-TO-A-PRIMARY`):
the primary `p` has `r`, and `x` is more `r` than `y` exactly when `x`
approaches `p` more nearly than `y` (`near y < near x`).

Source: ST I q.3 a.5 ad 2, *Deus autem non est mensura proportionata alicui.
Dicitur tamen mensura omnium, ex eo quod unumquodque tantum habet de esse,
quantum ei appropinquat*. The biconditional reads *tantum ... quantum*. Nothing
here says that nothing else reaches the primary (that is
`StrictPrimacyReading`, an open premise), nor that the primary causes
anything. -/
def ApproachToPrimaryReading {Being : Sort u} {Respect : Sort v}
    {Degree : Type w} [Preorder Degree]
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (r : Respect)
    (near : Being → Degree) (p : Being) : Prop :=
  InAct p r ∧ ∀ x y, MoreIn r x y ↔ near y < near x

/-- Strict primacy (`DEF-STRICT-PRIMACY`): every thing other than the primary
approaches it less nearly than the primary itself stands (`near x < near p`), so
nothing ties with the primary.

Open premise, not attributed to any source. ST I q.3 a.5 ad 2 says that each
thing has as much being as it approaches God and that God is not a proportioned
measure; it does not say that nothing other than God reaches God's degree. The
results that need this clause (`QUARTA-VIA-ATTRIBUTION-GENUS-PRINCIPLE-AT-BEING`,
`QUARTA-VIA-ATTRIBUTION-UNIQUE-MAXIMUM`) take it as a separate hypothesis, and
their omission countermodels show it is load-bearing. Candidate
`AQUINAS-STRICT-PRIMACY-IN-BEING` records where a source might be found. -/
def StrictPrimacyReading {Being : Sort u} {Degree : Type w} [Preorder Degree]
    (near : Being → Degree) (p : Being) : Prop :=
  ∀ x, x ≠ p → near x < near p

/-- Every creature that has `r` has it by its order to the primary as to its
principle and cause: the primary causes `r` in it.

Source: ST I q.13 a.5 co., *quidquid dicitur de Deo et creaturis, dicitur
secundum quod est aliquis ordo creaturae ad Deum, ut ad principium et causam, in
qua praeexistunt excellenter omnes rerum perfectiones*. Read for one perfection
`r` said of the primary and of creatures; the order *ad causam* is the
primary's being a cause of that perfection in the creature
(`DEF-CAUSE-OF-PERFECTION`, `DISAMB-CAUSE`), as in the article's own example
the medicine is *causa sanitatis quae est in animali*. `Creature` is a
predicate (`DEF-CREATURE`): the sentence speaks of creatures, not of everything
other than God, so it is not `CausesAllInGenus` at `p` until
`OthersAreCreaturesReading` (an open premise) is added
(`OrderedToPrimaryAsCauseReading.causesAllInGenus`). Aristotle's *pros hen*
(*Metaphysics* IV.2, 1003a33-b10) does not give it: there the relation to the
primary may be being an affection of it, a way to it, a privation of it, and so
on, not only being caused by it. -/
def OrderedToPrimaryAsCauseReading {Being : Sort u} {Respect : Sort v}
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (Creature : Being → Prop)
    (r : Respect) (p : Being) : Prop :=
  ∀ x, Creature x → InAct x r → CausesIn p x r

/-- Everything other than the primary is a creature (`DEF-CREATURE`).

Open premise, not attributed to ST I q.13 a.5, which speaks only of creatures.
ST I q.44 a.1 (*omne ens quod quocumque modo est, a Deo esse*) is where a
source might be found; no claim is made on it here. -/
def OthersAreCreaturesReading {Being : Sort u} (Creature : Being → Prop)
    (p : Being) : Prop :=
  ∀ x, x ≠ p → Creature x

/-- The genus principle at being only: whatever is maximal in being causes the
being of every other being. It is the instance `r = esse` of
`MaximumInGenusCausesAllInGenusReading`, the only instance the *quarta via* uses. -/
def MaximumInBeingCausesAllBeingsReading {Being : Sort u} {Respect : Sort v}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∀ m, IsMaximumIn InAct MoreIn esse m → CausesAllInGenus InAct CausesIn esse m

/-- Aristotle's cause-is-more-such principle restricted to the primary: the
primary is more `r` than any other thing in which it causes `r`. -/
def PrimaryCauseIsMoreSuchReading {Being : Sort u} {Respect : Sort v}
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (r : Respect) (p : Being) : Prop :=
  ∀ x, x ≠ p → CausesIn p x r → MoreIn r p x

/-- Formal fact: on the reading by attribution, Aristotle's principle (*Metaphysics*
II.1, a cause of a quality in another is more such) holds for the primary, but
not in general.

1. Any order by approach to a primary with strict primacy makes the primary
   more `r` than whatever else it causes `r` in.
2. An order by approach to a primary with strict primacy, the causal order of
   creatures to it, everything else being a creature, and the broad genus
   principle do not yield the unrestricted principle: a secondary
   cause may cause being in something that approaches the primary more nearly. -/
def AttributionOrderRestrictsCauseMoreSuch : Prop :=
  (∀ (Being Respect Degree : Type) [Preorder Degree]
      (InAct : Being → Respect → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop)
      (r : Respect) (near : Being → Degree) (p : Being),
      ApproachToPrimaryReading InAct MoreIn r near p →
      StrictPrimacyReading near p →
      PrimaryCauseIsMoreSuchReading MoreIn CausesIn r p) ∧
  ¬ ∀ (Being Respect Degree : Type) [Preorder Degree]
      (InAct : Being → Respect → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop) (Creature : Being → Prop)
      (esse : Respect) (near : Being → Degree) (p : Being),
      ApproachToPrimaryReading InAct MoreIn esse near p →
      StrictPrimacyReading near p →
      OrderedToPrimaryAsCauseReading InAct CausesIn Creature esse p →
      OthersAreCreaturesReading Creature p →
      MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn →
      CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn

/-- Formal fact: neither order reading yields that the maximum in being is the
first being. A homogeneous scale and an order by approach to a primary with
strict primacy on the same beings, the causal order of creatures to the primary,
everything else being a creature, the broad genus principle and the open premise that what is simply prior to a thing causes its
being (`SimplyPriorIsCauseOfBeing`) all hold, yet something other than the
maximum is simply prior to it. -/
def OrderReadingsDoNotYieldFirstBeing : Prop :=
  ¬ ∀ (Being : Type) [Preorder Being] (Respect Degree : Type) [Preorder Degree]
      (InAct : Being → Respect → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop) (Creature : Being → Prop)
      (PriorSimply : Being → Being → Prop)
      (esse : Respect) (near : Being → Degree) (p : Being),
      HomogeneousScaleReading InAct MoreIn esse →
      ApproachToPrimaryReading InAct MoreIn esse near p →
      StrictPrimacyReading near p →
      OrderedToPrimaryAsCauseReading InAct CausesIn Creature esse p →
      OthersAreCreaturesReading Creature p →
      MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn →
      SimplyPriorIsCauseOfBeing PriorSimply CausesIn esse →
      MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply

/-- Formal fact: a homogeneous scale gives no cause of being, but leaves room for
one.

1. A homogeneous scale of being with a greatest element (Mathlib `IsGreatest`)
   does not yield that the maximum causes the being of the others.
2. A homogeneous scale, the broad genus principle and Aristotle's
   cause-is-more-such principle hold together, with a maximum in being. -/
def HomogeneousScaleGivesNoCauseOfBeing : Prop :=
  (¬ ∀ (Being : Type) [Preorder Being] (Respect : Type)
      (InAct : Being → Respect → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop) (esse : Respect),
      HomogeneousScaleReading InAct MoreIn esse →
      (∃ m : Being, IsGreatest Set.univ m) →
      MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse) ∧
  ∃ (Being : Type) (_ : Preorder Being) (Respect : Type)
      (InAct : Being → Respect → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop) (esse : Respect),
      HomogeneousScaleReading InAct MoreIn esse ∧
      MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn ∧
      CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn ∧
      ∃ m, IsMaximumIn InAct MoreIn esse m

/-! ## Order lemmas

Stated with Mathlib's `IsMax`, `IsGreatest` and `Preorder.lift`, for reuse by the
order-theoretic consolidation of the *quarta via* (#341). -/

/-- On a homogeneous scale, being maximal in `r` is being a maximal element
(Mathlib `IsMax`) of the scale. -/
theorem HomogeneousScaleReading.isMaximumIn_iff_isMax {Being : Type u}
    {Respect : Sort v} [Preorder Being]
    {InAct : Being → Respect → Prop} {MoreIn : Respect → Being → Being → Prop}
    {r : Respect} (h : HomogeneousScaleReading InAct MoreIn r) (m : Being) :
    IsMaximumIn InAct MoreIn r m ↔ IsMax m := by
  rw [isMax_iff_forall_not_lt]
  constructor
  · intro hm y hy
    exact hm.2 y ((h.2 y m).2 hy)
  · intro hm
    exact ⟨h.1 m, fun y hy => hm y ((h.2 y m).1 hy)⟩

/-- With strict primacy, the primary's degree is the greatest degree reached
(Mathlib `IsGreatest` on the range of `near`). Classical (Mathlib's
`by_cases`); not used by the results. -/
theorem StrictPrimacyReading.isGreatest {Being : Sort u}
    {Degree : Type w} [Preorder Degree] {near : Being → Degree} {p : Being}
    (hStrict : StrictPrimacyReading near p) :
    IsGreatest (Set.range near) (near p) := by
  refine ⟨⟨p, rfl⟩, ?_⟩
  rintro _ ⟨x, rfl⟩
  by_cases hx : x = p
  · rw [hx]
  · exact (hStrict x hx).le

/-- On an order by approach to a primary with strict primacy, the primary is
maximal in `r`. No excluded middle is used: `y = p` and `y ≠ p` each refute `y`
being more `r`. -/
theorem ApproachToPrimaryReading.isMaximumIn_primary {Being : Sort u}
    {Respect : Sort v} {Degree : Type w} [Preorder Degree]
    {InAct : Being → Respect → Prop} {MoreIn : Respect → Being → Being → Prop}
    {r : Respect} {near : Being → Degree} {p : Being}
    (h : ApproachToPrimaryReading InAct MoreIn r near p)
    (hStrict : StrictPrimacyReading near p) :
    IsMaximumIn InAct MoreIn r p := by
  refine ⟨h.1, fun y hy => ?_⟩
  have hlt : near p < near y := (h.2 y p).1 hy
  have hSame : y ≠ p := fun hyp => lt_irrefl (near p) (hyp ▸ hlt)
  exact lt_asymm (hStrict y hSame) hlt

/-- On an order by approach to a primary with strict primacy, whatever is
maximal in `r` is the primary: anything else falls short of it. Excluded middle
(on `m = p`) is an explicit hypothesis, as elsewhere in the corpus. -/
theorem ApproachToPrimaryReading.eq_of_isMaximumIn {Being : Sort u}
    {Respect : Sort v} {Degree : Type w} [Preorder Degree]
    {InAct : Being → Respect → Prop} {MoreIn : Respect → Being → Being → Prop}
    {r : Respect} {near : Being → Degree} {p : Being}
    (h : ApproachToPrimaryReading InAct MoreIn r near p)
    (hStrict : StrictPrimacyReading near p)
    (hEM : TruthCore.Logic.ExcludedMiddle) {m : Being}
    (hm : IsMaximumIn InAct MoreIn r m) : m = p := by
  cases hEM (m = p) with
  | inl hSame => exact hSame
  | inr hne => exact absurd ((h.2 p m).2 (hStrict m hne)) (hm.2 p)

/-- The causal order of creatures to the primary, with everything other than
the primary a creature, is the primary's causing `r` in everything else that
has it (`CausesAllInGenus` at `p`). -/
theorem OrderedToPrimaryAsCauseReading.causesAllInGenus {Being : Sort u}
    {Respect : Sort v} {InAct : Being → Respect → Prop}
    {CausesIn : Being → Being → Respect → Prop} {Creature : Being → Prop}
    {r : Respect} {p : Being}
    (h : OrderedToPrimaryAsCauseReading InAct CausesIn Creature r p)
    (hCreatures : OthersAreCreaturesReading Creature p) :
    CausesAllInGenus InAct CausesIn r p :=
  fun x hx hr => h x (hCreatures x hx) hr

/-- Order theory does not tell the readings apart: an order by approach to a
primary on beings that all have `r` is a homogeneous scale for the preorder
pulled back along `near` (`Preorder.lift`). -/
theorem ApproachToPrimaryReading.homogeneousLift {Being : Type u}
    {Respect : Sort v} {Degree : Type w} [Preorder Degree]
    {InAct : Being → Respect → Prop} {MoreIn : Respect → Being → Being → Prop}
    {r : Respect} {near : Being → Degree} {p : Being}
    (h : ApproachToPrimaryReading InAct MoreIn r near p) (hAll : ∀ x, InAct x r) :
    @HomogeneousScaleReading Being Respect (Preorder.lift near) InAct MoreIn r :=
  ⟨hAll, h.2⟩

end TruthCore.Latin.Aquinas.SummaTheologiae
