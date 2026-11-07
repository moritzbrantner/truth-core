module

public import TruthCore.Greek.Aristotle.Metaphysics
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaAscent
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article2
public import TruthCore.Logic.ExcludedMiddle

/-! Causal maps, batch 1: the cause of a quality is more such, the efficient
cause is prior, and nothing moves except as in act

Analyst formulations, attribution deferred. Three exploration maps
(`explorations/cause-of-quality-more-such.toml`,
`explorations/efficient-cause-prior.toml`,
`explorations/nothing-moves-except-in-act.toml`) propose derivations of three
stated but underived root-path premises. Every new proposition below is an OPEN
premise: an analyst bridge, or a reading recorded as `supported` by an existing
claim with its gap. None is attributed as stated.

Vocabulary reused exactly: `CausesIn` and `MoreIn` of the Metaphysics II.1
reading (DEF-CAUSE-OF-PERFECTION, DEF-MORE-IN), `InAct` (DEF-ACT), `MovesIn` of
the prima via, `EfficientlyCausesIn` (DEF-EFFICIENT-CAUSING) and `PriorSimply`
(DEF-SIMPLE-PRIORITY) of the secunda via. New primitives, all parameters:

* `ReceivedIn y r z` (DEF-PERFECTION-RECEIVED-IN): `y`'s having the perfection
  `r` is received in `z`, which stands to it as receiving potency. It generalizes
  `EsseReceivedIn` (DEF-ESSE-RECEIVED-IN) from esse to any perfection; it is not
  the giving of a perfection by an agent (DISAMB-ESSE-RECEPTION).
* `LimitedBy y r z` (DEF-PERFECTION-LIMITED-BY): `y` has `r` only to the measure
  of `z`'s capacity, as heat in wood is bounded by what the wood can take. It
  generalizes `EsseLimited` (DEF-ESSE-LIMITED) and is relative to a limiter.
* `DependsForBeing x y` (DEF-DEPENDS-FOR-BEING): `x` would not be if `y` were
  not, in the q.44 a.1 ad 2 sense of an effect's dependence on its agent; not
  temporal succession and not material implication.
* `PartOf p x` (DEF-MOVER-PART): `p` is an integral part of the whole `x`, as
  the soul-moved limb or the heart of an animal (Physics VIII.4-5).

The new propositions do not identify `MovesIn`, `CausesIn` and
`EfficientlyCausesIn` (DISAMB-CAUSE); the one bridge that relates moving to
causing a perfection, `MoverCausesWhatItMovesTo`, is an explicit open premise. -/

@[expose] public section

namespace TruthCore.Causality.CausalMapsBatch1

universe u v

/-! ## Map 1: the cause of a quality in another is more such -/

/-- Nothing gives what it does not have: whatever causes a perfection `r` in a
thing has `r` (formally or eminently, the abstract `InAct`). Supported by ST I
q.4 a.2 co., which says it of the effective cause of a thing's being. -/
def CauseHasWhatItGives {B : Sort u} {R : Sort v}
    (CausesIn : B → B → R → Prop) (InAct : B → R → Prop) : Prop :=
  ∀ c x r, CausesIn c x r → InAct c r

/-- A caused perfection is had by its effect: if `c` causes `x`'s being `r`, then
`x` is `r` in act. -/
def CausedPerfectionIsHad {B : Sort u} {R : Sort v}
    (CausesIn : B → B → R → Prop) (InAct : B → R → Prop) : Prop :=
  ∀ c x r, CausesIn c x r → InAct x r

/-- The weak, q.4 a.2-scoped version: a cause of a thing's being has every
perfection it causes in that thing. -/
def CauseOfBeingHasWhatItGives {B : Sort u} {R : Sort v}
    (CausesIn : B → B → R → Prop) (InAct : B → R → Prop) (esse : R) : Prop :=
  ∀ c x r, CausesIn c x esse → CausesIn c x r → InAct c r

/-- A perfection caused in another is received in that other: if `c ≠ x` causes
`x`'s being `r`, then `x`'s having `r` is received in `x`. -/
def CausedPerfectionIsReceivedInEffect {B : Sort u} {R : Sort v}
    (CausesIn : B → B → R → Prop) (ReceivedIn : B → R → B → Prop) : Prop :=
  ∀ c x r, c ≠ x → CausesIn c x r → ReceivedIn x r x

/-- A received perfection is limited by its recipient (generalizing ST I q.7 a.2
co. from esse to every perfection). -/
def ReceivedPerfectionIsLimitedByRecipient {B : Sort u} {R : Sort v}
    (ReceivedIn LimitedBy : B → R → B → Prop) : Prop :=
  ∀ y r z, ReceivedIn y r z → LimitedBy y r z

/-- A perfection is limited by something only through being received in it
(generalizing ST I q.7 a.1 co. from esse to every perfection). -/
def PerfectionLimitedOnlyThroughReception {B : Sort u} {R : Sort v}
    (ReceivedIn LimitedBy : B → R → B → Prop) : Prop :=
  ∀ y r z, LimitedBy y r z → ReceivedIn y r z

/-- A distinct cause does not have the perfection it causes as received in its
effect. -/
def CauseHasPerfectionNotAsReceivedInEffect {B : Sort u} {R : Sort v}
    (CausesIn : B → B → R → Prop) (ReceivedIn : B → R → B → Prop) : Prop :=
  ∀ c x r, c ≠ x → CausesIn c x r → ¬ ReceivedIn c r x

/-- Whoever has `r` without the limit that `x`'s capacity imposes on `x`'s own
having of `r` is more `r` than `x`. -/
def UnlimitedPossessionExceedsLimited {B : Sort u} {R : Sort v}
    (InAct : B → R → Prop) (LimitedBy : B → R → B → Prop)
    (MoreIn : R → B → B → Prop) : Prop :=
  ∀ c x r, InAct c r → LimitedBy x r x → ¬ LimitedBy c r x → MoreIn r c x

/-! ## Map 2: the efficient cause is prior to its effect -/

/-- ST I q.44 a.1 ad 2, read as dependence: whatever is efficiently caused
depends for its being on its efficient cause. -/
def EffectDependsOnEfficientCause {B : Sort u} {R : Sort v}
    (EfficientlyCausesIn : B → B → R → Prop) (DependsForBeing : B → B → Prop) : Prop :=
  ∀ c x r, EfficientlyCausesIn c x r → DependsForBeing x c

/-- An efficient cause does not depend for its being on what it efficiently
causes. -/
def EfficientCauseNotDependentOnEffect {B : Sort u} {R : Sort v}
    (EfficientlyCausesIn : B → B → R → Prop) (DependsForBeing : B → B → Prop) : Prop :=
  ∀ c x r, EfficientlyCausesIn c x r → ¬ DependsForBeing c x

/-- Nonmutual dependence suffices for simple priority: if `x` depends for its
being on `y` and `y` does not so depend on `x`, then `y` is simply prior to `x`. -/
def NonmutualDependenceSufficesForPriority {B : Sort u}
    (PriorSimply DependsForBeing : B → B → Prop) : Prop :=
  ∀ y x, DependsForBeing x y → ¬ DependsForBeing y x → PriorSimply y x

/-- Simple priority requires nonmutual dependence: if `y` is simply prior to
`x`, then `x` depends for its being on `y` and `y` does not so depend on `x`. -/
def PriorityRequiresNonmutualDependence {B : Sort u}
    (PriorSimply DependsForBeing : B → B → Prop) : Prop :=
  ∀ y x, PriorSimply y x → DependsForBeing x y ∧ ¬ DependsForBeing y x

/-- No two things efficiently cause each other, in any respects. -/
def NoMutualEfficientCausation {B : Sort u} {R : Sort v}
    (EfficientlyCausesIn : B → B → R → Prop) : Prop :=
  ∀ c x r s, EfficientlyCausesIn c x r → ¬ EfficientlyCausesIn x c s

/-! ## Map 3: nothing moves except as in act -/

/-- Whatever moves another in a respect causes that other's being so in that
respect (`CausesIn`, the perfection-causing relation of DEF-CAUSE-OF-PERFECTION;
moving is reduction to act, DEF-MOTION-AS-REDUCTION). -/
def MoverCausesWhatItMovesTo {B : Sort u} {R : Sort v}
    (MovesIn CausesIn : B → B → R → Prop) : Prop :=
  ∀ y x r, MovesIn y x r → CausesIn y x r

/-- Whatever moves itself in a respect does so by a part distinct from the whole
that moves the whole in that respect (Physics VIII.4-5). -/
def SelfMoverMovesByADistinctPart {B : Sort u} {R : Sort v}
    (MovesIn : B → B → R → Prop) (PartOf : B → B → Prop) : Prop :=
  ∀ x r, MovesIn x x r → ∃ p, PartOf p x ∧ p ≠ x ∧ MovesIn p x r

/-- A whole is in act in a respect in which one of its parts is in act. -/
def WholeInActThroughItsPart {B : Sort u} {R : Sort v}
    (PartOf : B → B → Prop) (InAct : B → R → Prop) : Prop :=
  ∀ p x r, PartOf p x → InAct p r → InAct x r

/-! ## Controls

Omission models generated by `scripts/countermodel.py --all` and checked by
`decide`, with the generated `Fin 2`/`Fin 1` carriers renamed to `Bool`/`Unit`
so that `decide` uses no axiom; the joint witness is written by hand because the generated one is
empty. Satisfiability and omission only; no model is claimed to describe
reality. -/

namespace Control

/-- One-element carriers are `Unit`; these instances decide its quantifiers
without axioms (the `Fin` instances use `propext`). -/
instance unitForallDecidable (P : Unit → Prop) [h : Decidable (P ())] : Decidable (∀ x, P x) :=
  match h with
  | isTrue hp => isTrue (fun _ => hp)
  | isFalse hn => isFalse (fun hall => hn (hall ()))

instance unitExistsDecidable (P : Unit → Prop) [h : Decidable (P ())] : Decidable (∃ x, P x) :=
  match h with
  | isTrue hp => isTrue ⟨(), hp⟩
  | isFalse hn => isFalse (fun ⟨_, hx⟩ => hn hx)

namespace causeOfQualityMoreSuch.omit_hHas
/-- Omission model for `hHas` of `causeOfQualityMoreSuch`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = true ∧ x2 = ())
abbrev InAct : B → R → Prop := fun _ _ => False
abbrev ReceivedIn : B → R → B → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = () ∧ x2 = true)
abbrev LimitedBy : B → R → B → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = () ∧ x2 = true)
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives CausesIn InAct) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    ¬ (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
end causeOfQualityMoreSuch.omit_hHas

namespace causeOfQualityMoreSuch.omit_hRecv
/-- Omission model for `hRecv` of `causeOfQualityMoreSuch`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev InAct : B → R → Prop := fun x0 x1 => (x0 = true ∧ x1 = ())
abbrev ReceivedIn : B → R → B → Prop := fun _ _ _ => False
abbrev LimitedBy : B → R → B → Prop := fun _ _ _ => False
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives CausesIn InAct) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    ¬ (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
end causeOfQualityMoreSuch.omit_hRecv

namespace causeOfQualityMoreSuch.omit_hLim
/-- Omission model for `hLim` of `causeOfQualityMoreSuch`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev InAct : B → R → Prop := fun x0 x1 => (x0 = true ∧ x1 = ())
abbrev ReceivedIn : B → R → B → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = () ∧ x2 = false)
abbrev LimitedBy : B → R → B → Prop := fun _ _ _ => False
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives CausesIn InAct) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    ¬ (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
end causeOfQualityMoreSuch.omit_hLim

namespace causeOfQualityMoreSuch.omit_hOnly
/-- Omission model for `hOnly` of `causeOfQualityMoreSuch`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev InAct : B → R → Prop := fun x0 x1 => (x0 = true ∧ x1 = ())
abbrev ReceivedIn : B → R → B → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = () ∧ x2 = false)
abbrev LimitedBy : B → R → B → Prop := fun x0 x1 x2 =>
  (x0 = false ∧ x1 = () ∧ x2 = false) ∨
  (x0 = true ∧ x1 = () ∧ x2 = false)
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives CausesIn InAct) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    ¬ (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
end causeOfQualityMoreSuch.omit_hOnly

namespace causeOfQualityMoreSuch.omit_hNot
/-- Omission model for `hNot` of `causeOfQualityMoreSuch`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev InAct : B → R → Prop := fun x0 x1 => (x0 = true ∧ x1 = ())
abbrev ReceivedIn : B → R → B → Prop := fun x0 x1 x2 =>
  (x0 = false ∧ x1 = () ∧ x2 = false) ∨
  (x0 = true ∧ x1 = () ∧ x2 = false)
abbrev LimitedBy : B → R → B → Prop := fun x0 x1 x2 =>
  (x0 = false ∧ x1 = () ∧ x2 = false) ∨
  (x0 = true ∧ x1 = () ∧ x2 = false)
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives CausesIn InAct) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    ¬ (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
end causeOfQualityMoreSuch.omit_hNot

namespace causeOfQualityMoreSuch.omit_hExceed
/-- Omission model for `hExceed` of `causeOfQualityMoreSuch`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev InAct : B → R → Prop := fun x0 x1 => (x0 = true ∧ x1 = ())
abbrev ReceivedIn : B → R → B → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = () ∧ x2 = false)
abbrev LimitedBy : B → R → B → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = () ∧ x2 = false)
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives CausesIn InAct) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    ¬ (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
end causeOfQualityMoreSuch.omit_hExceed

namespace causeOfBeingHasWhatItGives.omit_hPre
/-- Omission model for `hPre` of `causeOfBeingHasWhatItGives`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev esse : R := ()
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = true ∧ x2 = ())
abbrev InAct : B → R → Prop := fun x0 x1 => (x0 = true ∧ x1 = ())
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsHad CausesIn InAct) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.CauseOfBeingHasWhatItGives CausesIn InAct esse)
end causeOfBeingHasWhatItGives.omit_hPre

namespace causeOfBeingHasWhatItGives.omit_hHad
/-- Omission model for `hHad` of `causeOfBeingHasWhatItGives`: the other premises hold and the conclusion fails. -/
abbrev B := Unit
abbrev R := Unit
abbrev esse : R := ()
abbrev CausesIn : B → B → R → Prop := fun _ _ _ => True
abbrev InAct : B → R → Prop := fun _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Latin.Aquinas.SummaTheologiae.PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsHad CausesIn InAct) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.CauseOfBeingHasWhatItGives CausesIn InAct esse)
end causeOfBeingHasWhatItGives.omit_hHad

namespace efficientCausePrior.omit_hDep
/-- Omission model for `hDep` of `efficientCausePrior`: the other premises hold and the conclusion fails. -/
abbrev B := Unit
abbrev R := Unit
abbrev EfficientlyCausesIn : B → B → R → Prop := fun _ _ _ => True
abbrev PriorSimply : B → B → Prop := fun _ _ => False
abbrev DependsForBeing : B → B → Prop := fun _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause EfficientlyCausesIn DependsForBeing) ∧
    (TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing) ∧
    (TruthCore.Causality.CausalMapsBatch1.NonmutualDependenceSufficesForPriority PriorSimply DependsForBeing) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply)
end efficientCausePrior.omit_hDep

namespace efficientCausePrior.omit_hIndep
/-- Omission model for `hIndep` of `efficientCausePrior`: the other premises hold and the conclusion fails. -/
abbrev B := Unit
abbrev R := Unit
abbrev EfficientlyCausesIn : B → B → R → Prop := fun _ _ _ => True
abbrev PriorSimply : B → B → Prop := fun _ _ => False
abbrev DependsForBeing : B → B → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause EfficientlyCausesIn DependsForBeing) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing) ∧
    (TruthCore.Causality.CausalMapsBatch1.NonmutualDependenceSufficesForPriority PriorSimply DependsForBeing) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply)
end efficientCausePrior.omit_hIndep

namespace efficientCausePrior.omit_hSuff
/-- Omission model for `hSuff` of `efficientCausePrior`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev EfficientlyCausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev PriorSimply : B → B → Prop := fun _ _ => False
abbrev DependsForBeing : B → B → Prop := fun x0 x1 => (x0 = false ∧ x1 = true)
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause EfficientlyCausesIn DependsForBeing) ∧
    (TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.NonmutualDependenceSufficesForPriority PriorSimply DependsForBeing) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply)
end efficientCausePrior.omit_hSuff

namespace nothingPriorToItself.omit_hReq
/-- Omission model for `hReq` of `nothingPriorToItself`: the other premises hold and the conclusion fails. -/
abbrev B := Unit
abbrev PriorSimply : B → B → Prop := fun _ _ => True
abbrev DependsForBeing : B → B → Prop := fun _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (TruthCore.Causality.CausalMapsBatch1.PriorityRequiresNonmutualDependence PriorSimply DependsForBeing) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.NothingPriorToItselfReading PriorSimply)
end nothingPriorToItself.omit_hReq

namespace nothingEfficientCauseOfItself.omit_hDep
/-- Omission model for `hDep` of `nothingEfficientCauseOfItself`: the other premises hold and the conclusion fails. -/
abbrev B := Unit
abbrev R := Unit
abbrev EfficientlyCausesIn : B → B → R → Prop := fun _ _ _ => True
abbrev DependsForBeing : B → B → Prop := fun _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause EfficientlyCausesIn DependsForBeing) ∧
    (TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn)
end nothingEfficientCauseOfItself.omit_hDep

namespace nothingEfficientCauseOfItself.omit_hIndep
/-- Omission model for `hIndep` of `nothingEfficientCauseOfItself`: the other premises hold and the conclusion fails. -/
abbrev B := Unit
abbrev R := Unit
abbrev EfficientlyCausesIn : B → B → R → Prop := fun _ _ _ => True
abbrev DependsForBeing : B → B → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause EfficientlyCausesIn DependsForBeing) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn)
end nothingEfficientCauseOfItself.omit_hIndep

namespace noMutualEfficientCausation.omit_hDep
/-- Omission model for `hDep` of `noMutualEfficientCausation`: the other premises hold and the conclusion fails. -/
abbrev B := Unit
abbrev R := Unit
abbrev EfficientlyCausesIn : B → B → R → Prop := fun _ _ _ => True
abbrev DependsForBeing : B → B → Prop := fun _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause EfficientlyCausesIn DependsForBeing) ∧
    (TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.NoMutualEfficientCausation EfficientlyCausesIn)
end noMutualEfficientCausation.omit_hDep

namespace noMutualEfficientCausation.omit_hIndep
/-- Omission model for `hIndep` of `noMutualEfficientCausation`: the other premises hold and the conclusion fails. -/
abbrev B := Unit
abbrev R := Unit
abbrev EfficientlyCausesIn : B → B → R → Prop := fun _ _ _ => True
abbrev DependsForBeing : B → B → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause EfficientlyCausesIn DependsForBeing) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.NoMutualEfficientCausation EfficientlyCausesIn)
end noMutualEfficientCausation.omit_hIndep

namespace nothingMovesExceptInAct.omit_hCause
/-- Omission model for `hCause` of `nothingMovesExceptInAct`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev MovesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = true ∧ x2 = ())
abbrev CausesIn : B → B → R → Prop := fun _ _ _ => False
abbrev InAct : B → R → Prop := fun _ _ => False
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
abbrev PartOf : B → B → Prop := fun _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (TruthCore.Causality.CausalMapsBatch1.MoverCausesWhatItMovesTo MovesIn CausesIn) ∧
    (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading InAct MoreIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.SelfMoverMovesByADistinctPart MovesIn PartOf) ∧
    (TruthCore.Causality.CausalMapsBatch1.WholeInActThroughItsPart PartOf InAct) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading MovesIn InAct)
end nothingMovesExceptInAct.omit_hCause

namespace nothingMovesExceptInAct.omit_hMore
/-- Omission model for `hMore` of `nothingMovesExceptInAct`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev MovesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev InAct : B → R → Prop := fun _ _ => False
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
abbrev PartOf : B → B → Prop := fun _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.CausalMapsBatch1.MoverCausesWhatItMovesTo MovesIn CausesIn) ∧
    ¬ (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading InAct MoreIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.SelfMoverMovesByADistinctPart MovesIn PartOf) ∧
    (TruthCore.Causality.CausalMapsBatch1.WholeInActThroughItsPart PartOf InAct) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading MovesIn InAct)
end nothingMovesExceptInAct.omit_hMore

namespace nothingMovesExceptInAct.omit_hHas
/-- Omission model for `hHas` of `nothingMovesExceptInAct`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev MovesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev InAct : B → R → Prop := fun _ _ => False
abbrev MoreIn : R → B → B → Prop := fun x0 x1 x2 => (x0 = () ∧ x1 = true ∧ x2 = false)
abbrev PartOf : B → B → Prop := fun _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.CausalMapsBatch1.MoverCausesWhatItMovesTo MovesIn CausesIn) ∧
    (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading InAct MoreIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.SelfMoverMovesByADistinctPart MovesIn PartOf) ∧
    (TruthCore.Causality.CausalMapsBatch1.WholeInActThroughItsPart PartOf InAct) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading MovesIn InAct)
end nothingMovesExceptInAct.omit_hHas

namespace nothingMovesExceptInAct.omit_hSelf
/-- Omission model for `hSelf` of `nothingMovesExceptInAct`: the other premises hold and the conclusion fails. -/
abbrev B := Unit
abbrev R := Unit
abbrev MovesIn : B → B → R → Prop := fun _ _ _ => True
abbrev CausesIn : B → B → R → Prop := fun _ _ _ => True
abbrev InAct : B → R → Prop := fun _ _ => False
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
abbrev PartOf : B → B → Prop := fun _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.CausalMapsBatch1.MoverCausesWhatItMovesTo MovesIn CausesIn) ∧
    (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading InAct MoreIn) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.SelfMoverMovesByADistinctPart MovesIn PartOf) ∧
    (TruthCore.Causality.CausalMapsBatch1.WholeInActThroughItsPart PartOf InAct) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading MovesIn InAct)
end nothingMovesExceptInAct.omit_hSelf

namespace nothingMovesExceptInAct.omit_hWhole
/-- Omission model for `hWhole` of `nothingMovesExceptInAct`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev MovesIn : B → B → R → Prop := fun x0 x1 x2 =>
  (x0 = false ∧ x1 = true ∧ x2 = ()) ∨
  (x0 = true ∧ x1 = true ∧ x2 = ())
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 =>
  (x0 = false ∧ x1 = true ∧ x2 = ()) ∨
  (x0 = true ∧ x1 = true ∧ x2 = ())
abbrev InAct : B → R → Prop := fun x0 x1 => (x0 = false ∧ x1 = ())
abbrev MoreIn : R → B → B → Prop := fun x0 x1 x2 => (x0 = () ∧ x1 = false ∧ x2 = true)
abbrev PartOf : B → B → Prop := fun x0 x1 => (x0 = false ∧ x1 = true)
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.CausalMapsBatch1.MoverCausesWhatItMovesTo MovesIn CausesIn) ∧
    (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading InAct MoreIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.SelfMoverMovesByADistinctPart MovesIn PartOf) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.WholeInActThroughItsPart PartOf InAct) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading MovesIn InAct)
end nothingMovesExceptInAct.omit_hWhole

namespace witness
/-! Joint nonvacuity witness for the whole batch. Being `false` causes, moves and
efficiently causes being `true`, and is its part; `true` also moves itself (by its part `false`).
Every relation the derivations use is nonempty, and every premise and every
conclusion of the batch holds (excluded middle is a logical premise, not a model
condition, and is left out so the certificate stays axiom-free). -/
abbrev B := Bool
abbrev R := Unit
abbrev esse : R := ()
abbrev CausesIn : B → B → R → Prop := fun _ x _ => x = true
abbrev MovesIn : B → B → R → Prop := fun _ x _ => x = true
abbrev InAct : B → R → Prop := fun _ _ => True
abbrev ReceivedIn : B → R → B → Prop := fun y _ z => y = true ∧ z = true
abbrev LimitedBy : B → R → B → Prop := fun y _ z => y = true ∧ z = true
abbrev MoreIn : R → B → B → Prop := fun _ c x => c = false ∧ x = true
abbrev PartOf : B → B → Prop := fun p x => p = false ∧ x = true
abbrev EfficientlyCausesIn : B → B → R → Prop := fun c x _ => c = false ∧ x = true
abbrev DependsForBeing : B → B → Prop := fun x y => x = true ∧ y = false
abbrev PriorSimply : B → B → Prop := fun y x => y = false ∧ x = true
/-- Every premise and conclusion of the batch holds, with nonempty relations. -/
def Holds : Prop :=
    (∃ c x r, c ≠ x ∧ CausesIn c x r) ∧ (∃ x r, MovesIn x x r) ∧
    (∃ c x r, EfficientlyCausesIn c x r) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives CausesIn InAct) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsHad CausesIn InAct) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseOfBeingHasWhatItGives CausesIn InAct esse) ∧
    (TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause EfficientlyCausesIn DependsForBeing) ∧
    (TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing) ∧
    (TruthCore.Causality.CausalMapsBatch1.NonmutualDependenceSufficesForPriority PriorSimply DependsForBeing) ∧
    (TruthCore.Causality.CausalMapsBatch1.PriorityRequiresNonmutualDependence PriorSimply DependsForBeing) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.NothingPriorToItselfReading PriorSimply) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.NoMutualEfficientCausation EfficientlyCausesIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.MoverCausesWhatItMovesTo MovesIn CausesIn) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading InAct MoreIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.SelfMoverMovesByADistinctPart MovesIn PartOf) ∧
    (TruthCore.Causality.CausalMapsBatch1.WholeInActThroughItsPart PartOf InAct) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading MovesIn InAct)
end witness

/-- The batch controls: one omission model per premise of each derivation (excluded
middle excepted: it is logical, and no omission model of it exists within the
bounds) and one joint nonvacuity witness. -/
def Certificate : Prop :=
  causeOfQualityMoreSuch.omit_hHas.Holds ∧
  causeOfQualityMoreSuch.omit_hRecv.Holds ∧
  causeOfQualityMoreSuch.omit_hLim.Holds ∧
  causeOfQualityMoreSuch.omit_hOnly.Holds ∧
  causeOfQualityMoreSuch.omit_hNot.Holds ∧
  causeOfQualityMoreSuch.omit_hExceed.Holds ∧
  causeOfBeingHasWhatItGives.omit_hPre.Holds ∧
  causeOfBeingHasWhatItGives.omit_hHad.Holds ∧
  efficientCausePrior.omit_hDep.Holds ∧
  efficientCausePrior.omit_hIndep.Holds ∧
  efficientCausePrior.omit_hSuff.Holds ∧
  nothingPriorToItself.omit_hReq.Holds ∧
  nothingEfficientCauseOfItself.omit_hDep.Holds ∧
  nothingEfficientCauseOfItself.omit_hIndep.Holds ∧
  noMutualEfficientCausation.omit_hDep.Holds ∧
  noMutualEfficientCausation.omit_hIndep.Holds ∧
  nothingMovesExceptInAct.omit_hCause.Holds ∧
  nothingMovesExceptInAct.omit_hMore.Holds ∧
  nothingMovesExceptInAct.omit_hHas.Holds ∧
  nothingMovesExceptInAct.omit_hSelf.Holds ∧
  nothingMovesExceptInAct.omit_hWhole.Holds ∧
  witness.Holds

end Control

end TruthCore.Causality.CausalMapsBatch1
