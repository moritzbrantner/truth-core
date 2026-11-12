module

public import TruthCore.Case.Catholicism.CauseOfBeingHasBeing
public import TruthCore.Case.Catholicism.StageOneQuartaVia
public import TruthCore.Case.Catholicism.Root
public import TruthCore.Causality.CausalMapsBatch1
public import TruthCore.Causality.GodMaximalCausal
public import TruthCore.Greek.Aristotle.Metaphysics
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaAscent
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article8
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article2
public import TruthCore.Logic.ExcludedMiddle

/-!
# Where "nothing gives what it does not have" is load-bearing

Analyst formulations for the modal spine, stage two (`docs/notes/modal-spine.md`,
"Where `376d6a5a` is load-bearing"). Attribution deferred: no claim states any
premise below.

Under strict expansion (least fixpoint over verified arguments, statements
without a verified derivation as leaves), removing the unrestricted principle
`CausalMapsBatch1.CauseHasWhatItGives` ("nothing gives what it does not have")
left one of ten verified routes to `STMT-GOD-EXISTS`. The computed bottleneck
is not q.4 a.2 preexistence alone. Eight routes consume the Metaphysics α "more
such" premise (`CauseOfQualityInAnotherIsMoreSuchReading`), directly or through
the grades-to-a-maximum and moves-only-as-in-act steps; the composition routes
consume preexistence and "God is maximal in being". This module separates what
each needs.

* **More in being, without transfer.** `CauseOfBeingIsMoreInBeing` is the esse
  instance of "more such": whatever, distinct from `x`, causes `x`'s being is
  more in being than `x`. It follows from "a cause of being has being"
  (`CauseOfBeingHasBeing.CauseOfBeingInActAsToBeing`, itself derived from agency
  in act and q.4 a.1 ad 3) and the existing reception bundle at esse, with no
  transfer principle. Two consumers that use "more such" only at esse are
  re-derived from it: "God is maximal in being" and stage one from the quarta
  via's conclusion.
* **Preexistence and the cause-of-being restriction are interderivable.** With
  the transfer premise (`CauseOfBeingCausesEveryPerfection`), the restriction
  `CauseOfBeingHasWhatItGives` gives preexistence; the existing result
  `CausalMapsBatch1.causeOfBeingHasWhatItGives` gives the converse from
  preexistence and "a caused perfection is had". Neither has a derivation that
  avoids the other or the unrestricted principle, so this closes a cycle, not a
  route.
* **"More such" carries distinct-cause transfer.** `DistinctCauseHasWhatItGives`
  (whatever causes a perfection in another has it) follows from "more such" and
  "what is more such has the perfection", and "more such" follows from it and
  the reception bundle. The routes that need "more such" at an arbitrary
  perfection therefore need distinct-cause transfer, not a cause-of-being
  restriction.

`InAct` is the shared abstract parameter, read inclusively (formally or
eminently, DISAMB-IN-ACT). `CausesIn c x esse` is CAUSE_2 at esse, read for
extrinsic (efficient) causes of being.
-/

@[expose] public section

namespace TruthCore.Case.Catholicism.PreexistenceWithoutTransfer

section Vocabulary

variable {B R : Type}

/-- OPEN as a premise, derived here: whatever, distinct from `x`, causes `x`'s
being is more in being than `x`. The esse instance of the Metaphysics α "more
such" premise (`CauseOfQualityInAnotherIsMoreSuchReading` at `r = esse`). -/
def CauseOfBeingIsMoreInBeing (CausesIn : B → B → R → Prop)
    (MoreIn : R → B → B → Prop) (esse : R) : Prop :=
  ∀ c x, c ≠ x → CausesIn c x esse → MoreIn esse c x

/-- Distinct-cause transfer: whatever causes a perfection `r` in another thing
has `r` (formally or eminently, the inclusive `InAct`). The unrestricted
`CausalMapsBatch1.CauseHasWhatItGives` without its self-causation case. -/
def DistinctCauseHasWhatItGives (CausesIn : B → B → R → Prop) (InAct : B → R → Prop) :
    Prop :=
  ∀ c x r, c ≠ x → CausesIn c x r → InAct c r

end Vocabulary

/-! ## Finite controls -/

namespace Control

/-- Respect `false` is esse, `true` another perfection. -/
abbrev esse : Bool := false

/-- `false` causes the being of `true` and nothing else. -/
def causesBeing (c x : Bool) (r : Bool) : Prop := c = false ∧ x = true ∧ r = esse

/-- `false` causes both perfections of `true`. -/
def causesAll (c x : Bool) (_ : Bool) : Prop := c = false ∧ x = true

/-- `false` causes only the other perfection of `true`, not its being. -/
def causesOther (c x : Bool) (r : Bool) : Prop := c = false ∧ x = true ∧ r = true

/-- `false` is more `r` than `true`, in every respect. -/
def moreFalse (_ : Bool) (x y : Bool) : Prop := x = false ∧ y = true

/-- Reception: `true` receives in itself whatever is caused in it. -/
def recvTrue (y : Bool) (_ : Bool) (z : Bool) : Prop := y = true ∧ z = true

/-- Strictness of the esse instance: `false` causes the being and the other
perfection of `true`; it is more in being than `true` but not more in the other
perfection. -/
def moreEsseOnly (r : Bool) (x y : Bool) : Prop := r = esse ∧ x = false ∧ y = true

/-- Strictness and nonvacuity controls. -/
def Strictness : Prop :=
  -- (1) strictness: the esse instance of "more such" holds where "more such" fails
  (CauseOfBeingIsMoreInBeing causesAll moreEsseOnly esse ∧
    ¬ TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
      causesAll moreEsseOnly) ∧
  -- (2) the cause-of-being restriction says nothing of a cause of another perfection
  -- of something whose being it does not cause; distinct-cause transfer does
  (TruthCore.Causality.CausalMapsBatch1.CauseOfBeingHasWhatItGives causesOther
      (fun _ _ => False) esse ∧
    ¬ DistinctCauseHasWhatItGives causesOther (fun (_ : Bool) (_ : Bool) => False)) ∧
  -- (3) distinct-cause transfer says nothing of self-causation; the unrestricted
  -- principle does
  (DistinctCauseHasWhatItGives (fun c x _ => c = true ∧ x = true)
      (fun (_ : Bool) (_ : Bool) => False) ∧
    ¬ TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives
      (fun c x _ => c = true ∧ x = true) (fun (_ : Bool) (_ : Bool) => False)) ∧
  -- (4) nonvacuity: `false` causes the being and the other perfection of `true`,
  -- has both, is more in both, and every premise of the batch holds
  (TruthCore.Case.Catholicism.CauseOfBeingHasBeing.CauseOfBeingInActAsToBeing
      (fun _ _ => True) causesAll esse ∧
    TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect causesAll recvTrue ∧
    TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient recvTrue recvTrue ∧
    TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception recvTrue recvTrue ∧
    TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect causesAll recvTrue ∧
    TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited (fun _ _ => True)
      recvTrue moreFalse ∧
    CauseOfBeingIsMoreInBeing causesAll moreFalse esse ∧
    TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection (fun _ _ => True) causesAll esse ∧
    TruthCore.Causality.CausalMapsBatch1.CauseOfBeingHasWhatItGives causesAll
      (fun _ _ => True) esse ∧
    TruthCore.Latin.Aquinas.SummaTheologiae.PerfectionsOfEffectPreexistInCauseReading
      (fun _ _ => True) causesAll esse ∧
    TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
      causesAll moreFalse ∧
    DistinctCauseHasWhatItGives causesAll (fun _ _ => True) ∧
    causesAll false true esse ∧ causesAll false true true) ∧
  -- (5) nonvacuity of "God is maximal in being" from causing being: `true` is God,
  -- causes the being of `false` and is more in being than it
  (TruthCore.Causality.GodMaximalCausal.GodCausesBeingOfAllOthers
      TruthCore.Causality.GodMaximalCausal.Control.isGod
      TruthCore.Causality.GodMaximalCausal.Control.causes () ∧
    CauseOfBeingIsMoreInBeing TruthCore.Causality.GodMaximalCausal.Control.causes
      TruthCore.Causality.GodMaximalCausal.Control.more () ∧
    TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading
      TruthCore.Causality.GodMaximalCausal.Control.inAct
      TruthCore.Causality.GodMaximalCausal.Control.more ∧
    TruthCore.Causality.GodMaximalCausal.MoreInIsAsymmetric
      TruthCore.Causality.GodMaximalCausal.Control.more ∧
    TruthCore.Causality.GodMaximalCausal.SomethingOtherThanGodExists
      TruthCore.Causality.GodMaximalCausal.Control.isGod ∧
    TruthCore.Case.Catholicism.GodIsMaximalInBeing
      TruthCore.Causality.GodMaximalCausal.Control.isGod
      TruthCore.Causality.GodMaximalCausal.Control.inAct
      TruthCore.Causality.GodMaximalCausal.Control.more () ∧
    TruthCore.Causality.GodMaximalCausal.Control.isGod true)

/-! ### Omission models and joint witnesses (found by `scripts/countermodel.py`, carriers
recast as `Bool` and `Unit` so `decide` needs no axioms) -/

namespace causeOfBeingMoreInBeing.omit_hHas
/-- Omission model for `hHas` of `causeOfBeingMoreInBeing`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev esse : R := ()
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = true ∧ x2 = ())
abbrev InAct : B → R → Prop := fun _ _ => False
abbrev ReceivedIn : B → R → B → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = () ∧ x2 = true)
abbrev LimitedBy : B → R → B → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = () ∧ x2 = true)
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (TruthCore.Case.Catholicism.CauseOfBeingHasBeing.CauseOfBeingInActAsToBeing InAct CausesIn esse) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    ¬ (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing CausesIn MoreIn esse)
end causeOfBeingMoreInBeing.omit_hHas

namespace causeOfBeingMoreInBeing.omit_hRecv
/-- Omission model for `hRecv` of `causeOfBeingMoreInBeing`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev esse : R := ()
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev InAct : B → R → Prop := fun x0 x1 => (x0 = true ∧ x1 = ())
abbrev ReceivedIn : B → R → B → Prop := fun _ _ _ => False
abbrev LimitedBy : B → R → B → Prop := fun _ _ _ => False
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Case.Catholicism.CauseOfBeingHasBeing.CauseOfBeingInActAsToBeing InAct CausesIn esse) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    ¬ (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing CausesIn MoreIn esse)
end causeOfBeingMoreInBeing.omit_hRecv

namespace causeOfBeingMoreInBeing.omit_hLim
/-- Omission model for `hLim` of `causeOfBeingMoreInBeing`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev esse : R := ()
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev InAct : B → R → Prop := fun x0 x1 => (x0 = true ∧ x1 = ())
abbrev ReceivedIn : B → R → B → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = () ∧ x2 = false)
abbrev LimitedBy : B → R → B → Prop := fun _ _ _ => False
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Case.Catholicism.CauseOfBeingHasBeing.CauseOfBeingInActAsToBeing InAct CausesIn esse) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    ¬ (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing CausesIn MoreIn esse)
end causeOfBeingMoreInBeing.omit_hLim

namespace causeOfBeingMoreInBeing.omit_hOnly
/-- Omission model for `hOnly` of `causeOfBeingMoreInBeing`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev esse : R := ()
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev InAct : B → R → Prop := fun x0 x1 => (x0 = true ∧ x1 = ())
abbrev ReceivedIn : B → R → B → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = () ∧ x2 = false)
abbrev LimitedBy : B → R → B → Prop := fun x0 x1 x2 =>
  (x0 = false ∧ x1 = () ∧ x2 = false) ∨
  (x0 = true ∧ x1 = () ∧ x2 = false)
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Case.Catholicism.CauseOfBeingHasBeing.CauseOfBeingInActAsToBeing InAct CausesIn esse) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    ¬ (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing CausesIn MoreIn esse)
end causeOfBeingMoreInBeing.omit_hOnly

namespace causeOfBeingMoreInBeing.omit_hNot
/-- Omission model for `hNot` of `causeOfBeingMoreInBeing`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev esse : R := ()
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
    (TruthCore.Case.Catholicism.CauseOfBeingHasBeing.CauseOfBeingInActAsToBeing InAct CausesIn esse) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    ¬ (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing CausesIn MoreIn esse)
end causeOfBeingMoreInBeing.omit_hNot

namespace causeOfBeingMoreInBeing.omit_hExceed
/-- Omission model for `hExceed` of `causeOfBeingMoreInBeing`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev esse : R := ()
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev InAct : B → R → Prop := fun x0 x1 => (x0 = true ∧ x1 = ())
abbrev ReceivedIn : B → R → B → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = () ∧ x2 = false)
abbrev LimitedBy : B → R → B → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = () ∧ x2 = false)
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Case.Catholicism.CauseOfBeingHasBeing.CauseOfBeingInActAsToBeing InAct CausesIn esse) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    ¬ (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing CausesIn MoreIn esse)
end causeOfBeingMoreInBeing.omit_hExceed

namespace causeOfBeingMoreInBeing.witness
/-- Joint witness of `causeOfBeingMoreInBeing`: every premise and the conclusion hold. -/
abbrev B := Unit
abbrev R := Unit
abbrev esse : R := ()
abbrev CausesIn : B → B → R → Prop := fun _ _ _ => False
abbrev InAct : B → R → Prop := fun _ _ => False
abbrev ReceivedIn : B → R → B → Prop := fun _ _ _ => False
abbrev LimitedBy : B → R → B → Prop := fun _ _ _ => False
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
/-- The witness condition. -/
def Holds : Prop :=
    (TruthCore.Case.Catholicism.CauseOfBeingHasBeing.CauseOfBeingInActAsToBeing InAct CausesIn esse) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing CausesIn MoreIn esse)
end causeOfBeingMoreInBeing.witness
namespace distinctCauseGivesOfMoreSuch.omit_hMore
/-- Omission model for `hMore` of `distinctCauseGivesOfMoreSuch`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev InAct : B → R → Prop := fun _ _ => False
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading InAct MoreIn) ∧
    ¬ (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives CausesIn InAct)
end distinctCauseGivesOfMoreSuch.omit_hMore

namespace distinctCauseGivesOfMoreSuch.omit_hHas
/-- Omission model for `hHas` of `distinctCauseGivesOfMoreSuch`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev InAct : B → R → Prop := fun _ _ => False
abbrev MoreIn : R → B → B → Prop := fun x0 x1 x2 => (x0 = () ∧ x1 = true ∧ x2 = false)
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading InAct MoreIn) ∧
    ¬ (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives CausesIn InAct)
end distinctCauseGivesOfMoreSuch.omit_hHas

namespace distinctCauseGivesOfMoreSuch.witness
/-- Joint witness of `distinctCauseGivesOfMoreSuch`: every premise and the conclusion hold. -/
abbrev B := Unit
abbrev R := Unit
abbrev CausesIn : B → B → R → Prop := fun _ _ _ => False
abbrev InAct : B → R → Prop := fun _ _ => False
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
/-- The witness condition. -/
def Holds : Prop :=
    (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading InAct MoreIn) ∧
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives CausesIn InAct)
end distinctCauseGivesOfMoreSuch.witness
namespace godExistsFromMaximeEnsCausingAllByBeing.omit_hMaxime
/-- Omission model for `hMaxime` of `godExistsFromMaximeEnsCausingAllByBeing`: the other premises hold and the conclusion fails (excluded middle, which holds classically, is not listed). -/
abbrev Being := Unit
abbrev Respect := Unit
abbrev esse : Respect := ()
abbrev InAct : Being → Respect → Prop := fun _ _ => False
abbrev MoreIn : Respect → Being → Being → Prop := fun _ _ _ => False
abbrev CausesIn : Being → Being → Respect → Prop := fun _ _ _ => False
abbrev ComponentOf : Being → Being → Prop := fun _ _ => False
abbrev PriorSimply : Being → Being → Prop := fun _ _ => False
abbrev IsGod : Being → Prop := fun _ => False
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading InAct esse) ∧
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing CausesIn MoreIn esse) ∧
    (TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection InAct CausesIn esse) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.NoComponentIsFirstBeingReading ComponentOf PriorSimply) ∧
    (TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply) ∧
    (TruthCore.Case.Catholicism.GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) ∧
    ¬ (TruthCore.Case.Catholicism.GodExists IsGod)
end godExistsFromMaximeEnsCausingAllByBeing.omit_hMaxime

namespace godExistsFromMaximeEnsCausingAllByBeing.omit_hBeing
/-- Omission model for `hBeing` of `godExistsFromMaximeEnsCausingAllByBeing`: the other premises hold and the conclusion fails (excluded middle, which holds classically, is not listed). -/
abbrev Being := Bool
abbrev Respect := Bool
abbrev esse : Respect := false
abbrev InAct : Being → Respect → Prop := fun x0 x1 =>
  (x0 = false ∧ x1 = true) ∨
  (x0 = true ∧ x1 = false)
abbrev MoreIn : Respect → Being → Being → Prop := fun _ _ _ => False
abbrev CausesIn : Being → Being → Respect → Prop := fun _ _ _ => False
abbrev ComponentOf : Being → Being → Prop := fun _ _ => False
abbrev PriorSimply : Being → Being → Prop := fun _ _ => False
abbrev IsGod : Being → Prop := fun _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Latin.Aquinas.SummaTheologiae.MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading InAct esse) ∧
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing CausesIn MoreIn esse) ∧
    (TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection InAct CausesIn esse) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.NoComponentIsFirstBeingReading ComponentOf PriorSimply) ∧
    (TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply) ∧
    (TruthCore.Case.Catholicism.GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) ∧
    ¬ (TruthCore.Case.Catholicism.GodExists IsGod)
end godExistsFromMaximeEnsCausingAllByBeing.omit_hBeing

namespace godExistsFromMaximeEnsCausingAllByBeing.omit_hCauseMore
/-- Omission model for `hCauseMore` of `godExistsFromMaximeEnsCausingAllByBeing`: the other premises hold and the conclusion fails (excluded middle, which holds classically, is not listed). -/
abbrev Being := Bool
abbrev Respect := Unit
abbrev esse : Respect := ()
abbrev InAct : Being → Respect → Prop := fun _ _ => True
abbrev MoreIn : Respect → Being → Being → Prop := fun _ _ _ => False
abbrev CausesIn : Being → Being → Respect → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev ComponentOf : Being → Being → Prop := fun _ _ => False
abbrev PriorSimply : Being → Being → Prop := fun _ _ => False
abbrev IsGod : Being → Prop := fun _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Latin.Aquinas.SummaTheologiae.MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading InAct esse) ∧
    ¬ (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing CausesIn MoreIn esse) ∧
    (TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection InAct CausesIn esse) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.NoComponentIsFirstBeingReading ComponentOf PriorSimply) ∧
    (TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply) ∧
    (TruthCore.Case.Catholicism.GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) ∧
    ¬ (TruthCore.Case.Catholicism.GodExists IsGod)
end godExistsFromMaximeEnsCausingAllByBeing.omit_hCauseMore

namespace godExistsFromMaximeEnsCausingAllByBeing.omit_hPerfections
/-- Omission model for `hPerfections` of `godExistsFromMaximeEnsCausingAllByBeing`: the other premises hold and the conclusion fails (excluded middle, which holds classically, is not listed). -/
abbrev Being := Bool
abbrev Respect := Bool
abbrev esse : Respect := false
abbrev InAct : Being → Respect → Prop := fun x0 x1 =>
  (x0 = false ∧ x1 = false) ∨
  (x0 = true ∧ x1 = false) ∨
  (x0 = true ∧ x1 = true)
abbrev MoreIn : Respect → Being → Being → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = false ∧ x2 = true)
abbrev CausesIn : Being → Being → Respect → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = true ∧ x2 = false)
abbrev ComponentOf : Being → Being → Prop := fun _ _ => False
abbrev PriorSimply : Being → Being → Prop := fun _ _ => False
abbrev IsGod : Being → Prop := fun _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Latin.Aquinas.SummaTheologiae.MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading InAct esse) ∧
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing CausesIn MoreIn esse) ∧
    ¬ (TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection InAct CausesIn esse) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.NoComponentIsFirstBeingReading ComponentOf PriorSimply) ∧
    (TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply) ∧
    (TruthCore.Case.Catholicism.GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) ∧
    ¬ (TruthCore.Case.Catholicism.GodExists IsGod)
end godExistsFromMaximeEnsCausingAllByBeing.omit_hPerfections

namespace godExistsFromMaximeEnsCausingAllByBeing.omit_hNoComponent
/-- Omission model for `hNoComponent` of `godExistsFromMaximeEnsCausingAllByBeing`: the other premises hold and the conclusion fails (excluded middle, which holds classically, is not listed). -/
abbrev Being := Unit
abbrev Respect := Unit
abbrev esse : Respect := ()
abbrev InAct : Being → Respect → Prop := fun _ _ => True
abbrev MoreIn : Respect → Being → Being → Prop := fun _ _ _ => False
abbrev CausesIn : Being → Being → Respect → Prop := fun _ _ _ => False
abbrev ComponentOf : Being → Being → Prop := fun _ _ => True
abbrev PriorSimply : Being → Being → Prop := fun _ _ => False
abbrev IsGod : Being → Prop := fun _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Latin.Aquinas.SummaTheologiae.MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading InAct esse) ∧
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing CausesIn MoreIn esse) ∧
    (TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection InAct CausesIn esse) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.NoComponentIsFirstBeingReading ComponentOf PriorSimply) ∧
    (TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply) ∧
    (TruthCore.Case.Catholicism.GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) ∧
    ¬ (TruthCore.Case.Catholicism.GodExists IsGod)
end godExistsFromMaximeEnsCausingAllByBeing.omit_hNoComponent

namespace godExistsFromMaximeEnsCausingAllByBeing.omit_hFirstBeing
/-- Omission model for `hFirstBeing` of `godExistsFromMaximeEnsCausingAllByBeing`: the other premises hold and the conclusion fails (excluded middle, which holds classically, is not listed). -/
abbrev Being := Bool
abbrev Respect := Unit
abbrev esse : Respect := ()
abbrev InAct : Being → Respect → Prop := fun x0 x1 => (x0 = true ∧ x1 = ())
abbrev MoreIn : Respect → Being → Being → Prop := fun _ _ _ => False
abbrev CausesIn : Being → Being → Respect → Prop := fun _ _ _ => False
abbrev ComponentOf : Being → Being → Prop := fun x0 x1 => (x0 = true ∧ x1 = true)
abbrev PriorSimply : Being → Being → Prop := fun x0 x1 => (x0 = false ∧ x1 = true)
abbrev IsGod : Being → Prop := fun _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Latin.Aquinas.SummaTheologiae.MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading InAct esse) ∧
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing CausesIn MoreIn esse) ∧
    (TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection InAct CausesIn esse) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.NoComponentIsFirstBeingReading ComponentOf PriorSimply) ∧
    ¬ (TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply) ∧
    (TruthCore.Case.Catholicism.GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) ∧
    ¬ (TruthCore.Case.Catholicism.GodExists IsGod)
end godExistsFromMaximeEnsCausingAllByBeing.omit_hFirstBeing

namespace godExistsFromMaximeEnsCausingAllByBeing.omit_hFull
/-- Omission model for `hFull` of `godExistsFromMaximeEnsCausingAllByBeing`: the other premises hold and the conclusion fails (excluded middle, which holds classically, is not listed). -/
abbrev Being := Unit
abbrev Respect := Unit
abbrev esse : Respect := ()
abbrev InAct : Being → Respect → Prop := fun _ _ => True
abbrev MoreIn : Respect → Being → Being → Prop := fun _ _ _ => False
abbrev CausesIn : Being → Being → Respect → Prop := fun _ _ _ => False
abbrev ComponentOf : Being → Being → Prop := fun _ _ => False
abbrev PriorSimply : Being → Being → Prop := fun _ _ => False
abbrev IsGod : Being → Prop := fun _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Latin.Aquinas.SummaTheologiae.MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading InAct esse) ∧
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing CausesIn MoreIn esse) ∧
    (TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection InAct CausesIn esse) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.NoComponentIsFirstBeingReading ComponentOf PriorSimply) ∧
    (TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply) ∧
    ¬ (TruthCore.Case.Catholicism.GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) ∧
    ¬ (TruthCore.Case.Catholicism.GodExists IsGod)
end godExistsFromMaximeEnsCausingAllByBeing.omit_hFull

namespace godExistsFromMaximeEnsCausingAllByBeing.witness
/-- Joint witness of `godExistsFromMaximeEnsCausingAllByBeing`: every premise and the conclusion hold (excluded middle, which holds classically, is not listed). -/
abbrev Being := Unit
abbrev Respect := Unit
abbrev esse : Respect := ()
abbrev InAct : Being → Respect → Prop := fun _ _ => True
abbrev MoreIn : Respect → Being → Being → Prop := fun _ _ _ => False
abbrev CausesIn : Being → Being → Respect → Prop := fun _ _ _ => False
abbrev ComponentOf : Being → Being → Prop := fun _ _ => False
abbrev PriorSimply : Being → Being → Prop := fun _ _ => False
abbrev IsGod : Being → Prop := fun _ => True
/-- The witness condition. -/
def Holds : Prop :=
    (TruthCore.Latin.Aquinas.SummaTheologiae.MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading InAct esse) ∧
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing CausesIn MoreIn esse) ∧
    (TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection InAct CausesIn esse) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.NoComponentIsFirstBeingReading ComponentOf PriorSimply) ∧
    (TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply) ∧
    (TruthCore.Case.Catholicism.GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) ∧
    (TruthCore.Case.Catholicism.GodExists IsGod)
end godExistsFromMaximeEnsCausingAllByBeing.witness
namespace godMaximalFromCausingBeing.omit_hCauses
/-- Omission model for `hCauses` of `godMaximalFromCausingBeing`: the other premises hold and the conclusion fails (excluded middle, which holds classically, is not listed). -/
abbrev B := Bool
abbrev R := Unit
abbrev esse : R := ()
abbrev IsGod : B → Prop := fun x0 => (x0 = true)
abbrev InAct : B → R → Prop := fun _ _ => False
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
abbrev CausesIn : B → B → R → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (TruthCore.Causality.GodMaximalCausal.GodCausesBeingOfAllOthers IsGod CausesIn esse) ∧
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing CausesIn MoreIn esse) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading InAct MoreIn) ∧
    (TruthCore.Causality.GodMaximalCausal.MoreInIsAsymmetric MoreIn) ∧
    (TruthCore.Causality.GodMaximalCausal.SomethingOtherThanGodExists IsGod) ∧
    ¬ (TruthCore.Case.Catholicism.GodIsMaximalInBeing IsGod InAct MoreIn esse)
end godMaximalFromCausingBeing.omit_hCauses

namespace godMaximalFromCausingBeing.omit_hMore
/-- Omission model for `hMore` of `godMaximalFromCausingBeing`: the other premises hold and the conclusion fails (excluded middle, which holds classically, is not listed). -/
abbrev B := Bool
abbrev R := Unit
abbrev esse : R := ()
abbrev IsGod : B → Prop := fun x0 => (x0 = true)
abbrev InAct : B → R → Prop := fun _ _ => False
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.GodMaximalCausal.GodCausesBeingOfAllOthers IsGod CausesIn esse) ∧
    ¬ (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing CausesIn MoreIn esse) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading InAct MoreIn) ∧
    (TruthCore.Causality.GodMaximalCausal.MoreInIsAsymmetric MoreIn) ∧
    (TruthCore.Causality.GodMaximalCausal.SomethingOtherThanGodExists IsGod) ∧
    ¬ (TruthCore.Case.Catholicism.GodIsMaximalInBeing IsGod InAct MoreIn esse)
end godMaximalFromCausingBeing.omit_hMore

namespace godMaximalFromCausingBeing.omit_hHas
/-- Omission model for `hHas` of `godMaximalFromCausingBeing`: the other premises hold and the conclusion fails (excluded middle, which holds classically, is not listed). -/
abbrev B := Bool
abbrev R := Unit
abbrev esse : R := ()
abbrev IsGod : B → Prop := fun x0 => (x0 = true)
abbrev InAct : B → R → Prop := fun _ _ => False
abbrev MoreIn : R → B → B → Prop := fun x0 x1 x2 => (x0 = () ∧ x1 = true ∧ x2 = false)
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.GodMaximalCausal.GodCausesBeingOfAllOthers IsGod CausesIn esse) ∧
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing CausesIn MoreIn esse) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading InAct MoreIn) ∧
    (TruthCore.Causality.GodMaximalCausal.MoreInIsAsymmetric MoreIn) ∧
    (TruthCore.Causality.GodMaximalCausal.SomethingOtherThanGodExists IsGod) ∧
    ¬ (TruthCore.Case.Catholicism.GodIsMaximalInBeing IsGod InAct MoreIn esse)
end godMaximalFromCausingBeing.omit_hHas

namespace godMaximalFromCausingBeing.omit_hAsym
/-- Omission model for `hAsym` of `godMaximalFromCausingBeing`: the other premises hold and the conclusion fails (excluded middle, which holds classically, is not listed). -/
abbrev B := Bool
abbrev R := Unit
abbrev esse : R := ()
abbrev IsGod : B → Prop := fun x0 => (x0 = true)
abbrev InAct : B → R → Prop := fun x0 x1 => (x0 = true ∧ x1 = ())
abbrev MoreIn : R → B → B → Prop := fun x0 x1 x2 =>
  (x0 = () ∧ x1 = true ∧ x2 = false) ∨
  (x0 = () ∧ x1 = true ∧ x2 = true)
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.GodMaximalCausal.GodCausesBeingOfAllOthers IsGod CausesIn esse) ∧
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing CausesIn MoreIn esse) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading InAct MoreIn) ∧
    ¬ (TruthCore.Causality.GodMaximalCausal.MoreInIsAsymmetric MoreIn) ∧
    (TruthCore.Causality.GodMaximalCausal.SomethingOtherThanGodExists IsGod) ∧
    ¬ (TruthCore.Case.Catholicism.GodIsMaximalInBeing IsGod InAct MoreIn esse)
end godMaximalFromCausingBeing.omit_hAsym

namespace godMaximalFromCausingBeing.omit_hOther
/-- Omission model for `hOther` of `godMaximalFromCausingBeing`: the other premises hold and the conclusion fails (excluded middle, which holds classically, is not listed). -/
abbrev B := Unit
abbrev R := Unit
abbrev esse : R := ()
abbrev IsGod : B → Prop := fun _ => True
abbrev InAct : B → R → Prop := fun _ _ => False
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
abbrev CausesIn : B → B → R → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Causality.GodMaximalCausal.GodCausesBeingOfAllOthers IsGod CausesIn esse) ∧
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing CausesIn MoreIn esse) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading InAct MoreIn) ∧
    (TruthCore.Causality.GodMaximalCausal.MoreInIsAsymmetric MoreIn) ∧
    ¬ (TruthCore.Causality.GodMaximalCausal.SomethingOtherThanGodExists IsGod) ∧
    ¬ (TruthCore.Case.Catholicism.GodIsMaximalInBeing IsGod InAct MoreIn esse)
end godMaximalFromCausingBeing.omit_hOther

namespace godMaximalFromCausingBeing.witness
/-- Joint witness of `godMaximalFromCausingBeing`: every premise and the conclusion hold (excluded middle, which holds classically, is not listed). -/
abbrev B := Unit
abbrev R := Unit
abbrev esse : R := ()
abbrev IsGod : B → Prop := fun _ => False
abbrev InAct : B → R → Prop := fun _ _ => False
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
abbrev CausesIn : B → B → R → Prop := fun _ _ _ => False
/-- The witness condition. -/
def Holds : Prop :=
    (TruthCore.Causality.GodMaximalCausal.GodCausesBeingOfAllOthers IsGod CausesIn esse) ∧
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing CausesIn MoreIn esse) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading InAct MoreIn) ∧
    (TruthCore.Causality.GodMaximalCausal.MoreInIsAsymmetric MoreIn) ∧
    (TruthCore.Causality.GodMaximalCausal.SomethingOtherThanGodExists IsGod) ∧
    (TruthCore.Case.Catholicism.GodIsMaximalInBeing IsGod InAct MoreIn esse)
end godMaximalFromCausingBeing.witness
namespace moreSuchOfDistinctCauseGives.omit_hHas
/-- Omission model for `hHas` of `moreSuchOfDistinctCauseGives`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = true ∧ x2 = ())
abbrev InAct : B → R → Prop := fun _ _ => False
abbrev ReceivedIn : B → R → B → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = () ∧ x2 = true)
abbrev LimitedBy : B → R → B → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = () ∧ x2 = true)
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives CausesIn InAct) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    ¬ (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
end moreSuchOfDistinctCauseGives.omit_hHas

namespace moreSuchOfDistinctCauseGives.omit_hRecv
/-- Omission model for `hRecv` of `moreSuchOfDistinctCauseGives`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev InAct : B → R → Prop := fun x0 x1 => (x0 = true ∧ x1 = ())
abbrev ReceivedIn : B → R → B → Prop := fun _ _ _ => False
abbrev LimitedBy : B → R → B → Prop := fun _ _ _ => False
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives CausesIn InAct) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    ¬ (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
end moreSuchOfDistinctCauseGives.omit_hRecv

namespace moreSuchOfDistinctCauseGives.omit_hLim
/-- Omission model for `hLim` of `moreSuchOfDistinctCauseGives`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev InAct : B → R → Prop := fun x0 x1 => (x0 = true ∧ x1 = ())
abbrev ReceivedIn : B → R → B → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = () ∧ x2 = false)
abbrev LimitedBy : B → R → B → Prop := fun _ _ _ => False
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives CausesIn InAct) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    ¬ (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
end moreSuchOfDistinctCauseGives.omit_hLim

namespace moreSuchOfDistinctCauseGives.omit_hOnly
/-- Omission model for `hOnly` of `moreSuchOfDistinctCauseGives`: the other premises hold and the conclusion fails. -/
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
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives CausesIn InAct) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    ¬ (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
end moreSuchOfDistinctCauseGives.omit_hOnly

namespace moreSuchOfDistinctCauseGives.omit_hNot
/-- Omission model for `hNot` of `moreSuchOfDistinctCauseGives`: the other premises hold and the conclusion fails. -/
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
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives CausesIn InAct) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    ¬ (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
end moreSuchOfDistinctCauseGives.omit_hNot

namespace moreSuchOfDistinctCauseGives.omit_hExceed
/-- Omission model for `hExceed` of `moreSuchOfDistinctCauseGives`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = ())
abbrev InAct : B → R → Prop := fun x0 x1 => (x0 = true ∧ x1 = ())
abbrev ReceivedIn : B → R → B → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = () ∧ x2 = false)
abbrev LimitedBy : B → R → B → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = () ∧ x2 = false)
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives CausesIn InAct) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    ¬ (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
end moreSuchOfDistinctCauseGives.omit_hExceed

namespace moreSuchOfDistinctCauseGives.witness
/-- Joint witness of `moreSuchOfDistinctCauseGives`: every premise and the conclusion hold. -/
abbrev B := Unit
abbrev R := Unit
abbrev CausesIn : B → B → R → Prop := fun _ _ _ => False
abbrev InAct : B → R → Prop := fun _ _ => False
abbrev ReceivedIn : B → R → B → Prop := fun _ _ _ => False
abbrev LimitedBy : B → R → B → Prop := fun _ _ _ => False
abbrev MoreIn : R → B → B → Prop := fun _ _ _ => False
/-- The witness condition. -/
def Holds : Prop :=
    (TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives CausesIn InAct) ∧
    (TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn) ∧
    (TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) ∧
    (TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
end moreSuchOfDistinctCauseGives.witness
namespace preexistOfTransferAndRestriction.omit_hTransfer
/-- Omission model for `hTransfer` of `preexistOfTransferAndRestriction`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Bool
abbrev esse : R := false
abbrev InAct : B → R → Prop := fun x0 x1 =>
  (x0 = false ∧ x1 = true) ∨
  (x0 = true ∧ x1 = false)
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = true ∧ x1 = false ∧ x2 = false)
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection InAct CausesIn esse) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseOfBeingHasWhatItGives CausesIn InAct esse) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse)
end preexistOfTransferAndRestriction.omit_hTransfer

namespace preexistOfTransferAndRestriction.omit_hGives
/-- Omission model for `hGives` of `preexistOfTransferAndRestriction`: the other premises hold and the conclusion fails. -/
abbrev B := Bool
abbrev R := Unit
abbrev esse : R := ()
abbrev InAct : B → R → Prop := fun x0 x1 => (x0 = true ∧ x1 = ())
abbrev CausesIn : B → B → R → Prop := fun x0 x1 x2 => (x0 = false ∧ x1 = true ∧ x2 = ())
/-- The omission condition. -/
def Holds : Prop :=
    (TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection InAct CausesIn esse) ∧
    ¬ (TruthCore.Causality.CausalMapsBatch1.CauseOfBeingHasWhatItGives CausesIn InAct esse) ∧
    ¬ (TruthCore.Latin.Aquinas.SummaTheologiae.PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse)
end preexistOfTransferAndRestriction.omit_hGives

namespace preexistOfTransferAndRestriction.witness
/-- Joint witness of `preexistOfTransferAndRestriction`: every premise and the conclusion hold. -/
abbrev B := Unit
abbrev R := Unit
abbrev esse : R := ()
abbrev InAct : B → R → Prop := fun _ _ => False
abbrev CausesIn : B → B → R → Prop := fun _ _ _ => False
/-- The witness condition. -/
def Holds : Prop :=
    (TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection InAct CausesIn esse) ∧
    (TruthCore.Causality.CausalMapsBatch1.CauseOfBeingHasWhatItGives CausesIn InAct esse) ∧
    (TruthCore.Latin.Aquinas.SummaTheologiae.PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse)
end preexistOfTransferAndRestriction.witness

/-- Every control of the batch: strictness of the esse instance and of the
transfer ladder, nonvacuity, an omission model for each premise of each
registered derivation (except excluded middle, which holds classically) and a
joint witness for each. -/
def Controls : Prop :=
  Strictness ∧
  causeOfBeingMoreInBeing.omit_hHas.Holds ∧
  causeOfBeingMoreInBeing.omit_hRecv.Holds ∧
  causeOfBeingMoreInBeing.omit_hLim.Holds ∧
  causeOfBeingMoreInBeing.omit_hOnly.Holds ∧
  causeOfBeingMoreInBeing.omit_hNot.Holds ∧
  causeOfBeingMoreInBeing.omit_hExceed.Holds ∧
  causeOfBeingMoreInBeing.witness.Holds ∧
  distinctCauseGivesOfMoreSuch.omit_hMore.Holds ∧
  distinctCauseGivesOfMoreSuch.omit_hHas.Holds ∧
  distinctCauseGivesOfMoreSuch.witness.Holds ∧
  godExistsFromMaximeEnsCausingAllByBeing.omit_hMaxime.Holds ∧
  godExistsFromMaximeEnsCausingAllByBeing.omit_hBeing.Holds ∧
  godExistsFromMaximeEnsCausingAllByBeing.omit_hCauseMore.Holds ∧
  godExistsFromMaximeEnsCausingAllByBeing.omit_hPerfections.Holds ∧
  godExistsFromMaximeEnsCausingAllByBeing.omit_hNoComponent.Holds ∧
  godExistsFromMaximeEnsCausingAllByBeing.omit_hFirstBeing.Holds ∧
  godExistsFromMaximeEnsCausingAllByBeing.omit_hFull.Holds ∧
  godExistsFromMaximeEnsCausingAllByBeing.witness.Holds ∧
  godMaximalFromCausingBeing.omit_hCauses.Holds ∧
  godMaximalFromCausingBeing.omit_hMore.Holds ∧
  godMaximalFromCausingBeing.omit_hHas.Holds ∧
  godMaximalFromCausingBeing.omit_hAsym.Holds ∧
  godMaximalFromCausingBeing.omit_hOther.Holds ∧
  godMaximalFromCausingBeing.witness.Holds ∧
  moreSuchOfDistinctCauseGives.omit_hHas.Holds ∧
  moreSuchOfDistinctCauseGives.omit_hRecv.Holds ∧
  moreSuchOfDistinctCauseGives.omit_hLim.Holds ∧
  moreSuchOfDistinctCauseGives.omit_hOnly.Holds ∧
  moreSuchOfDistinctCauseGives.omit_hNot.Holds ∧
  moreSuchOfDistinctCauseGives.omit_hExceed.Holds ∧
  moreSuchOfDistinctCauseGives.witness.Holds ∧
  preexistOfTransferAndRestriction.omit_hTransfer.Holds ∧
  preexistOfTransferAndRestriction.omit_hGives.Holds ∧
  preexistOfTransferAndRestriction.witness.Holds

end Control

end TruthCore.Case.Catholicism.PreexistenceWithoutTransfer
