module

public import Mathlib.Order.Bounds.Basic
public import TruthCore.Causality.CausalMapsBatch1
public import TruthCore.Causality.ComponentFirstness
public import TruthCore.Causality.ReceptionLimitation
public import TruthCore.Case.Catholicism.CausalPerfectionTransfer
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaOrder

/-! Round 2 on perfection and primacy: deeper premises for eight bare root-path
bridges

Analyst formulations, attribution deferred. Eight exploration maps
(`explorations/round2-*.toml`) propose derivations of eight bare premises that
lie on root paths: four bridges of causal maps batch 1 (unlimited possession
exceeds limited; caused perfection is received in the effect; the cause's
perfection is not received in the effect; the efficient cause does not depend on
its effect), the sufficiency of nonmutual dependence for priority, and three
primacy premises (others than the primary are creatures; nothing else reaches the
primary; a universal cause of being transfers perfections). Every new
proposition below is an OPEN premise, either an analyst bridge or a reading
recorded as `supported` by an existing claim with its gap. None is attributed
as stated.

Vocabulary reused exactly: `CausesIn`, `InAct`, `MoreIn`, `ReceivedIn`,
`LimitedBy`, `EfficientlyCausesIn`, `DependsForBeing` and `PriorSimply` of
causal maps batch 1; `Participated` of `ComponentFirstness`
(DEF-PARTICIPATED-ESSE); `EsseReceivedIn`/`EsseLimited` of the q.7 readings
(DEF-ESSE-RECEIVED-IN, DEF-ESSE-LIMITED); `Creature` (DEF-CREATURE), `near`
(DEF-ORDER-BY-APPROACH-TO-A-PRIMARY) and `CausesAllInGenus`
(DEF-UNIVERSAL-ESSE-CAUSE-SCOPE). New primitives, all parameters:

* `deg y r` and `cap z r` (DEF-DEGREE-AND-CAPACITY): the degree in which `y`
  has the perfection `r`, and the measure of `r` that `z` can take, in one
  preorder of degrees. A measure reading of "to the measure of z's capacity" in
  DEF-PERFECTION-LIMITED-BY; nothing makes degrees of different respects
  comparable.
* `ParticipatesIn x r` (DEF-PARTICIPATED-PERFECTION): `x` has `r` by
  participation, not through what it is; it generalizes `Participated`
  (esse by participation) to any perfection.
* `CanBeWithout y x` (DEF-CAN-BE-WITHOUT): `y` can be while `x` is not, the
  criterion of natural priority in Aquinas, *In V Metaph.* lect. 13 n. 15 and
  n. 18 (pinned passage AQUINAS-IN-METAPH-V-L13, no claim made here).
* `TotalCauseOfBeing c x` and `ModeOfBeing x r` (DEF-TOTAL-CAUSE-OF-BEING,
  DEF-MODE-OF-BEING): `c` causes the whole being of `x`, not only its coming to
  be in a presupposed subject; and `r` is one of the ways in which `x` has
  being (ST I q.4 a.2: perfections pertain to the perfection of being).
-/

@[expose] public section

namespace TruthCore.Causality.Round2PerfectionPrimacy

section Vocabulary

variable {B R P D : Type}

/-! ## Target 1: unlimited possession exceeds limited -/

/-- Measure reading of limitation, one direction: whatever has `r` limited by
`z` has it in a degree within `z`'s capacity for `r`. -/
def LimitedHavingIsWithinCapacity [Preorder D] (LimitedBy : B → R → B → Prop)
    (deg cap : B → R → D) : Prop :=
  ∀ y r z, LimitedBy y r z → deg y r ≤ cap z r

/-- Measure reading of limitation, other direction: whatever has `r` and does
not have it limited by `z` has it in a degree beyond `z`'s capacity. It
presupposes that the degree of a haver of `r` and the capacity of `z` for `r`
are comparable. -/
def UnlimitedHavingExceedsCapacity [Preorder D] (InAct : B → R → Prop)
    (LimitedBy : B → R → B → Prop) (deg cap : B → R → D) : Prop :=
  ∀ y r z, InAct y r → ¬ LimitedBy y r z → cap z r < deg y r

/-- Degree reading of "more": what has `r` in a strictly greater degree is
more `r`. -/
def GreaterDegreeIsMore [Preorder D] (MoreIn : R → B → B → Prop) (deg : B → R → D) : Prop :=
  ∀ r c x, deg x r < deg c r → MoreIn r c x

/-! ## Target 2: a perfection caused in another is received in it -/

/-- What a thing has from a distinct cause it has by participation, not through
what it is (converse direction of ST I q.44 a.1 ad 1, which goes from
participation to being caused). -/
def CausedByAnotherIsParticipated (CausesIn : B → B → R → Prop)
    (ParticipatesIn : B → R → Prop) : Prop :=
  ∀ c x r, c ≠ x → CausesIn c x r → ParticipatesIn x r

/-- A perfection had by participation is received in its participant
(*participare est quasi partem capere*). -/
def ParticipatedIsReceivedInParticipant (ParticipatesIn : B → R → Prop)
    (ReceivedIn : B → R → B → Prop) : Prop :=
  ∀ x r, ParticipatesIn x r → ReceivedIn x r x

/-! ## Target 3: the cause's perfection is not received in its effect -/

/-- What has `r` as received in `z` depends for its being on `z`: the receiving
principle is intrinsic to the haver, as matter to the composite. -/
def HaverDependsOnRecipient (ReceivedIn : B → R → B → Prop)
    (DependsForBeing : B → B → Prop) : Prop :=
  ∀ y r z, ReceivedIn y r z → DependsForBeing y z

/-- Causing a perfection in another is efficient causing in that respect. It
relates two relations DISAMB-CAUSE keeps apart and does not identify them. -/
def PerfectionCausingInAnotherIsEfficient (CausesIn EfficientlyCausesIn : B → B → R → Prop) :
    Prop :=
  ∀ c x r, c ≠ x → CausesIn c x r → EfficientlyCausesIn c x r

/-! ## Target 4: an efficient cause does not depend on its effect -/

/-- No two distinct things depend for their being on each other (*In V
Metaph.* lect. 13 n. 18: *priora non dependent a posterioribus, sicut e
converso*). Restricted to distinct things because DependsForBeing, read
counterfactually, holds trivially of a thing and itself. -/
def DistinctBeingsNotMutuallyDependent (DependsForBeing : B → B → Prop) : Prop :=
  ∀ x y, x ≠ y → DependsForBeing x y → ¬ DependsForBeing y x

/-! ## Target 5: nonmutual dependence suffices for priority -/

/-- What depends for its being on `y` cannot be without `y`. -/
def DependenceExcludesBeingWithout (DependsForBeing CanBeWithout : B → B → Prop) : Prop :=
  ∀ x y, DependsForBeing x y → ¬ CanBeWithout x y

/-- What does not depend for its being on `x` can be without `x`. -/
def IndependenceAllowsBeingWithout (DependsForBeing CanBeWithout : B → B → Prop) : Prop :=
  ∀ y x, ¬ DependsForBeing y x → CanBeWithout y x

/-- Natural priority by the dependence criterion (*In V Metaph.* lect. 13
n. 15: *priora dicuntur, quae possunt esse sine aliis et illa non possunt esse
sine eis*), read for simple priority. -/
def PriorityByBeingWithout (PriorSimply CanBeWithout : B → B → Prop) : Prop :=
  ∀ y x, CanBeWithout y x → ¬ CanBeWithout x y → PriorSimply y x

/-! ## Target 6: everything other than the primary is a creature -/

/-- Everything other than the primary has its being by participation (ST I q.44
a.1 co., read for the primary `p`). -/
def OthersThanPrimaryParticipateEsse (Participated : B → Prop) (p : B) : Prop :=
  ∀ x, x ≠ p → Participated x

/-- Whatever has its being caused by another is a creature (DEF-CREATURE read
as: ordered to a cause of its being). -/
def CausedInBeingByAnotherIsCreature (CausesIn : B → B → R → Prop) (Creature : B → Prop)
    (esse : R) : Prop :=
  ∀ c x, c ≠ x → CausesIn c x esse → Creature x

/-! ## Target 7: nothing else reaches the primary -/

/-- A creature's esse is received in some principle (ST I q.7 a.2 co., said of
a subsistent created form, generalized to every creature). -/
def CreatureEsseIsReceived (Creature : B → Prop) (EsseReceivedIn : B → P → Prop) : Prop :=
  ∀ x, Creature x → ∃ z, EsseReceivedIn x z

/-- The primary's esse is received in nothing (ST I q.7 a.1 co., *esse divinum
non sit esse receptum in aliquo*, applied to the primary `p` of the approach
order). -/
def PrimaryEsseUnreceived (EsseReceivedIn : B → P → Prop) (p : B) : Prop :=
  ∀ z, ¬ EsseReceivedIn p z

/-- Whatever has limited esse approaches less nearly than whatever has
unlimited esse. -/
def LimitedEsseApproachesLess [Preorder D] (EsseLimited : B → Prop) (near : B → D) : Prop :=
  ∀ x y, EsseLimited x → ¬ EsseLimited y → near x < near y

/-! ## Target 8: a universal cause of being transfers perfections -/

/-- A cause of the being of every other being is the total cause of the being
of each other thing whose being it causes. -/
def UniversalCauseOfBeingIsTotal (InAct : B → R → Prop) (CausesIn : B → B → R → Prop)
    (esse : R) (TotalCauseOfBeing : B → B → Prop) : Prop :=
  ∀ c, TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus InAct CausesIn esse c →
    ∀ x, x ≠ c → CausesIn c x esse → TotalCauseOfBeing c x

/-- A total cause of a thing's being causes each of its modes of being. -/
def TotalCauseCausesModesOfBeing (TotalCauseOfBeing : B → B → Prop)
    (ModeOfBeing : B → R → Prop) (CausesIn : B → B → R → Prop) : Prop :=
  ∀ c x r, TotalCauseOfBeing c x → ModeOfBeing x r → CausesIn c x r

/-- Every perfection a thing has is a mode of its being (ST I q.4 a.2 co.,
*omnium perfectiones pertinent ad perfectionem essendi*). -/
def PerfectionsAreModesOfBeing (InAct : B → R → Prop) (ModeOfBeing : B → R → Prop) : Prop :=
  ∀ x r, InAct x r → ModeOfBeing x r

end Vocabulary

/-! ## Controls

Omission models generated by `scripts/countermodel.py --all` and checked by
`decide`, with the generated `Fin 2`/`Fin 1` carriers renamed to `Bool`/`Unit`
so that `decide` uses no axiom; the models of the two derivations with a degree
preorder and the joint witness are written by hand. Satisfiability and omission
only; no model is claimed to describe reality. -/

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

namespace causePerfectionNotReceivedInEffect.omit_hHaver
/-- Omission model for `hHaver` of `causePerfectionNotReceivedInEffect`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev EfficientlyCausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev ReceivedIn : B → R → B → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = () ∧ x2 = false)
abbrev DependsForBeing : B → B → Prop := fun _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.HaverDependsOnRecipient ReceivedIn DependsForBeing) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.PerfectionCausingInAnotherIsEfficient CausesIn EfficientlyCausesIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn)
end causePerfectionNotReceivedInEffect.omit_hHaver

namespace causePerfectionNotReceivedInEffect.omit_hEff
/-- Omission model for `hEff` of `causePerfectionNotReceivedInEffect`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev EfficientlyCausesIn : B → B → R → Prop := fun _ _ _ => False
abbrev ReceivedIn : B → R → B → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = () ∧ x2 = false)
abbrev DependsForBeing : B → B → Prop := fun x0 x1 => (x0 = true ∧ x1 = false)
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.Round2PerfectionPrimacy.HaverDependsOnRecipient ReceivedIn DependsForBeing) ∧
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.PerfectionCausingInAnotherIsEfficient CausesIn EfficientlyCausesIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn)
end causePerfectionNotReceivedInEffect.omit_hEff

namespace causePerfectionNotReceivedInEffect.omit_hIndep
/-- Omission model for `hIndep` of `causePerfectionNotReceivedInEffect`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev EfficientlyCausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev ReceivedIn : B → R → B → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = () ∧ x2 = false)
abbrev DependsForBeing : B → B → Prop := fun x0 x1 => (x0 = true ∧ x1 = false)
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.Round2PerfectionPrimacy.HaverDependsOnRecipient ReceivedIn DependsForBeing) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.PerfectionCausingInAnotherIsEfficient CausesIn EfficientlyCausesIn) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn)
end causePerfectionNotReceivedInEffect.omit_hIndep

namespace causedPerfectionReceivedInEffect.omit_hPart
/-- Omission model for `hPart` of `causedPerfectionReceivedInEffect`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev ParticipatesIn : B → R → Prop := fun _ _ => False
abbrev ReceivedIn : B → R → B → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.CausedByAnotherIsParticipated CausesIn ParticipatesIn) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.ParticipatedIsReceivedInParticipant ParticipatesIn ReceivedIn) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn)
end causedPerfectionReceivedInEffect.omit_hPart

namespace causedPerfectionReceivedInEffect.omit_hRecv
/-- Omission model for `hRecv` of `causedPerfectionReceivedInEffect`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = true ∧ x2 = ())
abbrev ParticipatesIn : B → R → Prop := fun x0 x1 => (x0 = true ∧ x1 = ())
abbrev ReceivedIn : B → R → B → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.Round2PerfectionPrimacy.CausedByAnotherIsParticipated CausesIn ParticipatesIn) ∧
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.ParticipatedIsReceivedInParticipant ParticipatesIn ReceivedIn) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn)
end causedPerfectionReceivedInEffect.omit_hRecv

namespace efficientCauseNotDependent.omit_hDep
/-- Omission model for `hDep` of `efficientCauseNotDependent`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev EfficientlyCausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev DependsForBeing : B → B → Prop := fun x0 x1 => (x0 = true ∧ x1 = false)
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause EfficientlyCausesIn DependsForBeing) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.DistinctBeingsNotMutuallyDependent DependsForBeing) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing)
end efficientCauseNotDependent.omit_hDep

namespace efficientCauseNotDependent.omit_hNoSelf
/-- Omission model for `hNoSelf` of `efficientCauseNotDependent`: the other premises hold and the conclusion fails. -/
abbrev B := Unit
abbrev R := Unit
abbrev EfficientlyCausesIn : B → B → R → Prop := fun _ _ _ => True
abbrev DependsForBeing : B → B → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause EfficientlyCausesIn DependsForBeing) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.DistinctBeingsNotMutuallyDependent DependsForBeing) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing)
end efficientCauseNotDependent.omit_hNoSelf

namespace efficientCauseNotDependent.omit_hAsym
/-- Omission model for `hAsym` of `efficientCauseNotDependent`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev EfficientlyCausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev DependsForBeing : B → B → Prop := fun x0 x1 =>
  (x0 = false ∧ x1 = true) ∨
  (x0 = true ∧ x1 = false)
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause EfficientlyCausesIn DependsForBeing) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn) ∧
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.DistinctBeingsNotMutuallyDependent DependsForBeing) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing)
end efficientCauseNotDependent.omit_hAsym

namespace nonmutualDependenceSuffices.omit_hExcl
/-- Omission model for `hExcl` of `nonmutualDependenceSuffices`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev PriorSimply : B → B → Prop := fun _ _ => False
abbrev DependsForBeing : B → B → Prop := fun x0 x1 => (x0 = true ∧ x1 = false)
abbrev CanBeWithout : B → B → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.DependenceExcludesBeingWithout DependsForBeing CanBeWithout) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.IndependenceAllowsBeingWithout DependsForBeing CanBeWithout) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.PriorityByBeingWithout PriorSimply CanBeWithout) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.NonmutualDependenceSufficesForPriority PriorSimply DependsForBeing)
end nonmutualDependenceSuffices.omit_hExcl

namespace nonmutualDependenceSuffices.omit_hAllow
/-- Omission model for `hAllow` of `nonmutualDependenceSuffices`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev PriorSimply : B → B → Prop := fun _ _ => False
abbrev DependsForBeing : B → B → Prop := fun x0 x1 => (x0 = true ∧ x1 = false)
abbrev CanBeWithout : B → B → Prop := fun _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.Round2PerfectionPrimacy.DependenceExcludesBeingWithout DependsForBeing CanBeWithout) ∧
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.IndependenceAllowsBeingWithout DependsForBeing CanBeWithout) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.PriorityByBeingWithout PriorSimply CanBeWithout) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.NonmutualDependenceSufficesForPriority PriorSimply DependsForBeing)
end nonmutualDependenceSuffices.omit_hAllow

namespace nonmutualDependenceSuffices.omit_hCrit
/-- Omission model for `hCrit` of `nonmutualDependenceSuffices`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev PriorSimply : B → B → Prop := fun _ _ => False
abbrev DependsForBeing : B → B → Prop := fun x0 x1 => (x0 = true ∧ x1 = false)
abbrev CanBeWithout : B → B → Prop := fun x0 x1 =>
  (x0 = false ∧ x1 = false) ∨
  (x0 = false ∧ x1 = true) ∨
  (x0 = true ∧ x1 = true)
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.Round2PerfectionPrimacy.DependenceExcludesBeingWithout DependsForBeing CanBeWithout) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.IndependenceAllowsBeingWithout DependsForBeing CanBeWithout) ∧
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.PriorityByBeingWithout PriorSimply CanBeWithout) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.NonmutualDependenceSufficesForPriority PriorSimply DependsForBeing)
end nonmutualDependenceSuffices.omit_hCrit

namespace othersAreCreatures.omit_hOthers
/-- Omission model for `hOthers` of `othersAreCreatures`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev esse : R := ()
abbrev p : B := false
abbrev Participated : B → Prop := fun _ => False
abbrev Creature : B → Prop := fun _ => False
abbrev CausesIn : B → B → R → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.OthersThanPrimaryParticipateEsse Participated p) ∧
    (TruthCore.Causality.ComponentFirstness.ParticipatedHasOtherCause Participated CausesIn esse) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.CausedInBeingByAnotherIsCreature CausesIn Creature esse) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading Creature p)
end othersAreCreatures.omit_hOthers

namespace othersAreCreatures.omit_hCaused
/-- Omission model for `hCaused` of `othersAreCreatures`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev esse : R := ()
abbrev p : B := false
abbrev Participated : B → Prop := fun x0 => (x0 = true)
abbrev Creature : B → Prop := fun _ => False
abbrev CausesIn : B → B → R → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.Round2PerfectionPrimacy.OthersThanPrimaryParticipateEsse Participated p) ∧
    ¬ (TruthCore.Causality.ComponentFirstness.ParticipatedHasOtherCause Participated CausesIn esse) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.CausedInBeingByAnotherIsCreature CausesIn Creature esse) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading Creature p)
end othersAreCreatures.omit_hCaused

namespace othersAreCreatures.omit_hCreature
/-- Omission model for `hCreature` of `othersAreCreatures`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev esse : R := ()
abbrev p : B := false
abbrev Participated : B → Prop := fun x0 => (x0 = true)
abbrev Creature : B → Prop := fun _ => False
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = true ∧ x2 = ())
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.Round2PerfectionPrimacy.OthersThanPrimaryParticipateEsse Participated p) ∧
    (TruthCore.Causality.ComponentFirstness.ParticipatedHasOtherCause Participated CausesIn esse) ∧
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.CausedInBeingByAnotherIsCreature CausesIn Creature esse) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading Creature p)
end othersAreCreatures.omit_hCreature

namespace universalCauseTransfers.omit_hTotal
/-- Omission model for `hTotal` of `universalCauseTransfers`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Bool
abbrev esse : R := false
abbrev InAct : B → R → Prop := fun x0 x1 => (x0 = true ∧ x1 = true)
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = true ∧ x2 = false)
abbrev TotalCauseOfBeing : B → B → Prop := fun _ _ => False
abbrev ModeOfBeing : B → R → Prop := fun x0 x1 => (x0 = true ∧ x1 = true)
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.UniversalCauseOfBeingIsTotal InAct CausesIn esse TotalCauseOfBeing) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.TotalCauseCausesModesOfBeing TotalCauseOfBeing ModeOfBeing CausesIn) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.PerfectionsAreModesOfBeing InAct ModeOfBeing) ∧
    ¬ (TruthCore.Case.Catholicism.UniversalCauseTransfersPerfections InAct CausesIn esse)
end universalCauseTransfers.omit_hTotal

namespace universalCauseTransfers.omit_hModes
/-- Omission model for `hModes` of `universalCauseTransfers`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Bool
abbrev esse : R := false
abbrev InAct : B → R → Prop := fun x0 x1 => (x0 = false ∧ x1 = true)
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = false)
abbrev TotalCauseOfBeing : B → B → Prop := fun x0 x1 => (x0 = true ∧ x1 = false)
abbrev ModeOfBeing : B → R → Prop := fun x0 x1 => (x0 = false ∧ x1 = true)
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.Round2PerfectionPrimacy.UniversalCauseOfBeingIsTotal InAct CausesIn esse TotalCauseOfBeing) ∧
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.TotalCauseCausesModesOfBeing TotalCauseOfBeing ModeOfBeing CausesIn) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.PerfectionsAreModesOfBeing InAct ModeOfBeing) ∧
    ¬ (TruthCore.Case.Catholicism.UniversalCauseTransfersPerfections InAct CausesIn esse)
end universalCauseTransfers.omit_hModes

namespace universalCauseTransfers.omit_hPerf
/-- Omission model for `hPerf` of `universalCauseTransfers`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Bool
abbrev esse : R := false
abbrev InAct : B → R → Prop := fun x0 x1 => (x0 = false ∧ x1 = true)
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = false)
abbrev TotalCauseOfBeing : B → B → Prop := fun x0 x1 => (x0 = true ∧ x1 = false)
abbrev ModeOfBeing : B → R → Prop := fun _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.Round2PerfectionPrimacy.UniversalCauseOfBeingIsTotal InAct CausesIn esse TotalCauseOfBeing) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.TotalCauseCausesModesOfBeing TotalCauseOfBeing ModeOfBeing CausesIn) ∧
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.PerfectionsAreModesOfBeing InAct ModeOfBeing) ∧
    ¬ (TruthCore.Case.Catholicism.UniversalCauseTransfersPerfections InAct CausesIn esse)
end universalCauseTransfers.omit_hPerf

/-! Hand-written omission models for the two derivations with a degree
preorder (`scripts/countermodel.py` does not support instance parameters).
Degrees are natural numbers with their Mathlib order. -/

namespace unlimitedPossessionExceedsLimited.omit_hWithin
/-- Omission model for `hWithin`: every degree is 1 and every capacity 0, so the
limited `false` exceeds its own capacity. -/
abbrev B := Bool
abbrev R := Unit
abbrev InAct : B → R → Prop := fun _ _ => True
abbrev LimitedBy : B → R → B → Prop := fun y _ _ => y = false
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
abbrev deg : B → R → Nat := fun _ _ => 1
abbrev cap : B → R → Nat := fun _ _ => 0
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.LimitedHavingIsWithinCapacity LimitedBy deg cap) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.UnlimitedHavingExceedsCapacity InAct LimitedBy deg cap) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.GreaterDegreeIsMore MoreIn deg) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn)
end unlimitedPossessionExceedsLimited.omit_hWithin

namespace unlimitedPossessionExceedsLimited.omit_hBeyond
/-- Omission model for `hBeyond`: all degrees and capacities are 0, so the
unlimited `true` does not exceed `false`'s capacity. -/
abbrev B := Bool
abbrev R := Unit
abbrev InAct : B → R → Prop := fun _ _ => True
abbrev LimitedBy : B → R → B → Prop := fun y _ _ => y = false
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
abbrev deg : B → R → Nat := fun _ _ => 0
abbrev cap : B → R → Nat := fun _ _ => 0
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.Round2PerfectionPrimacy.LimitedHavingIsWithinCapacity LimitedBy deg cap) ∧
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.UnlimitedHavingExceedsCapacity InAct LimitedBy deg cap) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.GreaterDegreeIsMore MoreIn deg) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn)
end unlimitedPossessionExceedsLimited.omit_hBeyond

namespace unlimitedPossessionExceedsLimited.omit_hMore
/-- Omission model for `hMore`: `true` has the greater degree, but nothing is
more anything. -/
abbrev B := Bool
abbrev R := Unit
abbrev InAct : B → R → Prop := fun _ _ => True
abbrev LimitedBy : B → R → B → Prop := fun y _ _ => y = false
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
abbrev deg : B → R → Nat := fun y _ => if y then 2 else 1
abbrev cap : B → R → Nat := fun _ _ => 1
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.Round2PerfectionPrimacy.LimitedHavingIsWithinCapacity LimitedBy deg cap) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.UnlimitedHavingExceedsCapacity InAct LimitedBy deg cap) ∧
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.GreaterDegreeIsMore MoreIn deg) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn)
end unlimitedPossessionExceedsLimited.omit_hMore

namespace nothingElseReachesPrimary.omit_hOthers
/-- Omission model for `hOthers` of `nothingElseReachesPrimary`: nothing is a creature, all degrees tie. -/
abbrev B := Bool
abbrev P := Unit
abbrev p : B := true
abbrev Creature : B → Prop := fun _ => False
abbrev EsseReceivedIn : B → P → Prop := fun _ _ => False
abbrev EsseLimited : B → Prop := fun _ => False
abbrev near : B → Nat := fun _ => 1
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading Creature p) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.CreatureEsseIsReceived Creature EsseReceivedIn) ∧
    (TruthCore.Causality.ReceptionLimitation.ReceivedEsseIsLimited EsseLimited EsseReceivedIn) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.EsseLimitedOnlyThroughReceptionReading EsseLimited EsseReceivedIn) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.PrimaryEsseUnreceived EsseReceivedIn p) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.LimitedEsseApproachesLess EsseLimited near) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.StrictPrimacyReading near p)
end nothingElseReachesPrimary.omit_hOthers

namespace nothingElseReachesPrimary.omit_hRecv
/-- Omission model for `hRecv` of `nothingElseReachesPrimary`: `false` is a creature with unreceived esse. -/
abbrev B := Bool
abbrev P := Unit
abbrev p : B := true
abbrev Creature : B → Prop := fun x => x = false
abbrev EsseReceivedIn : B → P → Prop := fun _ _ => False
abbrev EsseLimited : B → Prop := fun _ => False
abbrev near : B → Nat := fun _ => 1
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading Creature p) ∧
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.CreatureEsseIsReceived Creature EsseReceivedIn) ∧
    (TruthCore.Causality.ReceptionLimitation.ReceivedEsseIsLimited EsseLimited EsseReceivedIn) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.EsseLimitedOnlyThroughReceptionReading EsseLimited EsseReceivedIn) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.PrimaryEsseUnreceived EsseReceivedIn p) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.LimitedEsseApproachesLess EsseLimited near) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.StrictPrimacyReading near p)
end nothingElseReachesPrimary.omit_hRecv

namespace nothingElseReachesPrimary.omit_hLim
/-- Omission model for `hLim` of `nothingElseReachesPrimary`: `false`'s esse is received but not limited. -/
abbrev B := Bool
abbrev P := Unit
abbrev p : B := true
abbrev Creature : B → Prop := fun x => x = false
abbrev EsseReceivedIn : B → P → Prop := fun x _ => x = false
abbrev EsseLimited : B → Prop := fun _ => False
abbrev near : B → Nat := fun _ => 1
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading Creature p) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.CreatureEsseIsReceived Creature EsseReceivedIn) ∧
    ¬ (TruthCore.Causality.ReceptionLimitation.ReceivedEsseIsLimited EsseLimited EsseReceivedIn) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.EsseLimitedOnlyThroughReceptionReading EsseLimited EsseReceivedIn) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.PrimaryEsseUnreceived EsseReceivedIn p) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.LimitedEsseApproachesLess EsseLimited near) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.StrictPrimacyReading near p)
end nothingElseReachesPrimary.omit_hLim

namespace nothingElseReachesPrimary.omit_hOnly
/-- Omission model for `hOnly` of `nothingElseReachesPrimary`: every esse is limited, the primary's without reception. -/
abbrev B := Bool
abbrev P := Unit
abbrev p : B := true
abbrev Creature : B → Prop := fun x => x = false
abbrev EsseReceivedIn : B → P → Prop := fun x _ => x = false
abbrev EsseLimited : B → Prop := fun _ => True
abbrev near : B → Nat := fun _ => 1
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading Creature p) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.CreatureEsseIsReceived Creature EsseReceivedIn) ∧
    (TruthCore.Causality.ReceptionLimitation.ReceivedEsseIsLimited EsseLimited EsseReceivedIn) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.EsseLimitedOnlyThroughReceptionReading EsseLimited EsseReceivedIn) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.PrimaryEsseUnreceived EsseReceivedIn p) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.LimitedEsseApproachesLess EsseLimited near) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.StrictPrimacyReading near p)
end nothingElseReachesPrimary.omit_hOnly

namespace nothingElseReachesPrimary.omit_hUnrec
/-- Omission model for `hUnrec` of `nothingElseReachesPrimary`: every esse, the primary's too, is received and limited. -/
abbrev B := Bool
abbrev P := Unit
abbrev p : B := true
abbrev Creature : B → Prop := fun x => x = false
abbrev EsseReceivedIn : B → P → Prop := fun _ _ => True
abbrev EsseLimited : B → Prop := fun _ => True
abbrev near : B → Nat := fun _ => 1
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading Creature p) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.CreatureEsseIsReceived Creature EsseReceivedIn) ∧
    (TruthCore.Causality.ReceptionLimitation.ReceivedEsseIsLimited EsseLimited EsseReceivedIn) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.EsseLimitedOnlyThroughReceptionReading EsseLimited EsseReceivedIn) ∧
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.PrimaryEsseUnreceived EsseReceivedIn p) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.LimitedEsseApproachesLess EsseLimited near) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.StrictPrimacyReading near p)
end nothingElseReachesPrimary.omit_hUnrec

namespace nothingElseReachesPrimary.omit_hLess
/-- Omission model for `hLess` of `nothingElseReachesPrimary`: limitation as intended, but `false` ties with the primary. -/
abbrev B := Bool
abbrev P := Unit
abbrev p : B := true
abbrev Creature : B → Prop := fun x => x = false
abbrev EsseReceivedIn : B → P → Prop := fun x _ => x = false
abbrev EsseLimited : B → Prop := fun x => x = false
abbrev near : B → Nat := fun _ => 1
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading Creature p) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.CreatureEsseIsReceived Creature EsseReceivedIn) ∧
    (TruthCore.Causality.ReceptionLimitation.ReceivedEsseIsLimited EsseLimited EsseReceivedIn) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.EsseLimitedOnlyThroughReceptionReading EsseLimited EsseReceivedIn) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.PrimaryEsseUnreceived EsseReceivedIn p) ∧
    ¬ (TruthCore.Causality.Round2PerfectionPrimacy.LimitedEsseApproachesLess EsseLimited near) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.StrictPrimacyReading near p)
end nothingElseReachesPrimary.omit_hLess

namespace witness
/-! Joint nonvacuity witness for the whole batch. `true` is the primary: it
causes, efficiently causes, totally causes the being of, and is prior to
`false`; `false` participates, receives and is limited, depends on `true`, and
approaches less nearly. Every relation the derivations use is nonempty, and every
premise and every conclusion of the batch holds. -/
abbrev B := Bool
abbrev R := Unit
abbrev P := Unit
abbrev esse : R := ()
abbrev p : B := true
abbrev CausesIn : B → B → R → Prop := fun c x _ => c = true ∧ x = false
abbrev EfficientlyCausesIn : B → B → R → Prop := fun c x _ => c = true ∧ x = false
abbrev InAct : B → R → Prop := fun _ _ => True
abbrev ParticipatesIn : B → R → Prop := fun x _ => x = false
abbrev ReceivedIn : B → R → B → Prop := fun y _ z => y = false ∧ z = false
abbrev LimitedBy : B → R → B → Prop := fun y _ _ => y = false
abbrev deg : B → R → Nat := fun y _ => if y then 2 else 1
abbrev cap : B → R → Nat := fun _ _ => 1
abbrev MoreIn : R → B → B → Prop := fun _ c x => c = true ∧ x = false
abbrev DependsForBeing : B → B → Prop := fun x _ => x = false
abbrev CanBeWithout : B → B → Prop := fun y _ => y = true
abbrev PriorSimply : B → B → Prop := fun y x => y = true ∧ x = false
abbrev Participated : B → Prop := fun x => x = false
abbrev Creature : B → Prop := fun x => x = false
abbrev EsseReceivedIn : B → P → Prop := fun x _ => x = false
abbrev EsseLimited : B → Prop := fun x => x = false
abbrev near : B → Nat := fun x => if x then 2 else 1
abbrev TotalCauseOfBeing : B → B → Prop := fun c x => c = true ∧ x = false
abbrev ModeOfBeing : B → R → Prop := fun _ _ => True
/-- Every premise and conclusion of the batch holds, with nonempty relations. -/
def Holds : Prop :=
    (∃ c x r, c ≠ x ∧ CausesIn c x r) ∧ (∃ c x r, EfficientlyCausesIn c x r) ∧
    (∃ y r z, ReceivedIn y r z) ∧ (∃ x y, DependsForBeing x y) ∧
    (∃ y r z, LimitedBy y r z) ∧ (∃ x, Creature x) ∧ (∃ x z, EsseReceivedIn x z) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.LimitedHavingIsWithinCapacity LimitedBy deg cap) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.UnlimitedHavingExceedsCapacity InAct LimitedBy deg cap) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.GreaterDegreeIsMore MoreIn deg) ∧
    (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.CausedByAnotherIsParticipated CausesIn ParticipatesIn) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.ParticipatedIsReceivedInParticipant ParticipatesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.HaverDependsOnRecipient ReceivedIn DependsForBeing) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.PerfectionCausingInAnotherIsEfficient CausesIn EfficientlyCausesIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause EfficientlyCausesIn DependsForBeing) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.DistinctBeingsNotMutuallyDependent DependsForBeing) ∧
    (TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.DependenceExcludesBeingWithout DependsForBeing CanBeWithout) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.IndependenceAllowsBeingWithout DependsForBeing CanBeWithout) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.PriorityByBeingWithout PriorSimply CanBeWithout) ∧
    (TruthCore.Causality.CausalMapsBatch1.NonmutualDependenceSufficesForPriority PriorSimply DependsForBeing) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.OthersThanPrimaryParticipateEsse Participated p) ∧
    (TruthCore.Causality.ComponentFirstness.ParticipatedHasOtherCause Participated CausesIn esse) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.CausedInBeingByAnotherIsCreature CausesIn Creature esse) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading Creature p) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.CreatureEsseIsReceived Creature EsseReceivedIn) ∧
    (TruthCore.Causality.ReceptionLimitation.ReceivedEsseIsLimited EsseLimited EsseReceivedIn) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.EsseLimitedOnlyThroughReceptionReading EsseLimited EsseReceivedIn) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.PrimaryEsseUnreceived EsseReceivedIn p) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.LimitedEsseApproachesLess EsseLimited near) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.StrictPrimacyReading near p) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.UniversalCauseOfBeingIsTotal InAct CausesIn esse TotalCauseOfBeing) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.TotalCauseCausesModesOfBeing TotalCauseOfBeing ModeOfBeing CausesIn) ∧
    (TruthCore.Causality.Round2PerfectionPrimacy.PerfectionsAreModesOfBeing InAct ModeOfBeing) ∧
    (TruthCore.Case.Catholicism.UniversalCauseTransfersPerfections InAct CausesIn esse)
end witness


/-- The batch controls: one omission model per premise of each derivation and one
joint nonvacuity witness. -/
def Certificate : Prop :=
  causePerfectionNotReceivedInEffect.omit_hHaver.Holds ∧
  causePerfectionNotReceivedInEffect.omit_hEff.Holds ∧
  causePerfectionNotReceivedInEffect.omit_hIndep.Holds ∧
  causedPerfectionReceivedInEffect.omit_hPart.Holds ∧
  causedPerfectionReceivedInEffect.omit_hRecv.Holds ∧
  efficientCauseNotDependent.omit_hDep.Holds ∧
  efficientCauseNotDependent.omit_hNoSelf.Holds ∧
  efficientCauseNotDependent.omit_hAsym.Holds ∧
  nonmutualDependenceSuffices.omit_hExcl.Holds ∧
  nonmutualDependenceSuffices.omit_hAllow.Holds ∧
  nonmutualDependenceSuffices.omit_hCrit.Holds ∧
  othersAreCreatures.omit_hOthers.Holds ∧
  othersAreCreatures.omit_hCaused.Holds ∧
  othersAreCreatures.omit_hCreature.Holds ∧
  universalCauseTransfers.omit_hTotal.Holds ∧
  universalCauseTransfers.omit_hModes.Holds ∧
  universalCauseTransfers.omit_hPerf.Holds ∧
  unlimitedPossessionExceedsLimited.omit_hWithin.Holds ∧
  unlimitedPossessionExceedsLimited.omit_hBeyond.Holds ∧
  unlimitedPossessionExceedsLimited.omit_hMore.Holds ∧
  nothingElseReachesPrimary.omit_hOthers.Holds ∧
  nothingElseReachesPrimary.omit_hRecv.Holds ∧
  nothingElseReachesPrimary.omit_hLim.Holds ∧
  nothingElseReachesPrimary.omit_hOnly.Holds ∧
  nothingElseReachesPrimary.omit_hUnrec.Holds ∧
  nothingElseReachesPrimary.omit_hLess.Holds ∧
  witness.Holds

end Control

end TruthCore.Causality.Round2PerfectionPrimacy
