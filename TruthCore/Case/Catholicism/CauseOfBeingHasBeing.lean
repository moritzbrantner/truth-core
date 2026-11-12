module

public import TruthCore.Causality.Round2Grounding
public import TruthCore.Causality.Round2ExistenceAct
public import TruthCore.Causality.SpineRivalsRootEsse
public import TruthCore.Logic.CogitoEsse

/-!
# The giver of being has being: decomposing the esse-cause bridge

Analyst formulations for the modal spine, stage two (`docs/notes/modal-spine.md`,
"Stage two: the root and the act of being"). Attribution deferred: no claim
states any premise below.

The esse-cause bridge `EsseCauseIsActualConcreteGround` (an actual concretum's
distinct cause of being is its actual concrete ground) feeds eight of the ten
attribute and naming steps of the registered composition from the join's
underived individual (result `57213a13`): it carries root uniqueness, the
maximum's identity with the root and simplicity. Its only derivation
(`Round2Grounding.esseCauseGroundViaDependence`) took two analyst leaves for its
first two clauses: causes of esse are concrete (`EsseCausesAreConcrete`) and
causes of the esse of an actual concretum exist at the selected world
(`EsseCausesExistAt`). This module derives both clauses from more basic,
separately intelligible premises.

* **Concreteness.** `EsseInReIsConcrete` states one direction of the adopted
  sense of "concrete" (CONCRETE_6, having esse in re, owner decision on #1103)
  for the profile's free `concrete` predicate. With the existing selected-world
  contract `ExistingInActAt` it gives `CogitoEsse.EveryExistentConcreteAt`:
  nothing non-concrete exists at the selected world. No causal premise is used.
* **Existence of the cause.** `CauseOfABeingHasBeing` is the classical maxim at
  being: whatever causes the being of something that is in act as to being is
  itself in act as to being (nothing gives being that it does not have). With
  `ExistingInActAt` and the existing converse `ActOfEsseSufficesForExistenceAt`
  it gives `EsseCausesExistAt`. The maxim is the esse instance of q.4 a.2
  preexistence and is entailed by `CauseOfBeingInActAsToBeing`, which in turn follows
  from agency in act (`CauseOfBeingIsInAct`, after q.75 a.2 *non enim est
  operari nisi entis in actu*) and the sourced q.4 a.1 ad 3 premise.

**The ladder of "nothing gives what it does not have".** The strength orders
registered with this batch run from the unrestricted principle
`CausalMapsBatch1.CauseHasWhatItGives` (every cause of any perfection has it)
through its cause-of-being restriction `CauseOfBeingHasWhatItGives` and
`CauseOfBeingInActAsToBeing` down to `CauseOfABeingHasBeing`, and from q.4 a.2
preexistence down to the same bottom rung. The esse-cause bridge uses only the
bottom rung, which also follows from agency in act without any transfer
principle. Scope objections to the unrestricted principle (instrumental causes
and causes of becoming; equivocal causes read formally) bear on the upper
rungs, as recorded in the modal-spine note.

`InAct` is the shared abstract parameter (DISAMB-IN-ACT): every premise is read
in the one sense the other act premises take. `CausesIn c x esse` is CAUSE_2,
causal responsibility for the effect's being, not for its coming to be.
-/

@[expose] public section

namespace TruthCore.Case.Catholicism.CauseOfBeingHasBeing

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.Round2Grounding
open TruthCore.Causality.Round2ExistenceAct (ActOfEsseSufficesForExistenceAt)
open TruthCore.Causality.SpineRivalsRootEsse (SomeEsseCauseNonConcrete)
open TruthCore.Logic.CogitoEsse (EveryExistentConcreteAt)
open TruthCore.Ontology.ConcreteAbstract (HasEsseInRe)

variable {W B R : Type}

/-- OPEN, agency in act restricted to causes of being: whatever causes the being
of something is in act in some respect. After q.75 a.2 co. (*non enim est
operari nisi entis in actu*), which the corpus states for operation edges
(`OperationOnlyOfBeingInActReading`, over `Ontic.Causes`); this is the sibling
for the tenseless `CausesIn` at esse, unattributed. -/
def CauseOfBeingIsInAct (InAct : B → R → Prop) (CausesIn : B → B → R → Prop)
    (esse : R) : Prop :=
  ∀ c x, CausesIn c x esse → ∃ r, InAct c r

/-- OPEN: whatever causes the being of anything is itself in act as to being.
The esse instance of `CausalMapsBatch1.CauseOfBeingHasWhatItGives`. -/
def CauseOfBeingInActAsToBeing (InAct : B → R → Prop) (CausesIn : B → B → R → Prop)
    (esse : R) : Prop :=
  ∀ c x, CausesIn c x esse → InAct c esse

/-- OPEN, nothing gives being that it does not have: whatever causes the being
of something that is in act as to being is itself in act as to being. The esse
instance of q.4 a.2 preexistence (`PerfectionsOfEffectPreexistInCauseReading`
at `r = esse`), and weaker than `CauseOfBeingInActAsToBeing`: it constrains only
causes of the being of things in act as to being. -/
def CauseOfABeingHasBeing (InAct : B → R → Prop) (CausesIn : B → B → R → Prop)
    (esse : R) : Prop :=
  ∀ c x, CausesIn c x esse → InAct x esse → InAct c esse

/-- OPEN interpretation premise, one direction of the CONCRETE_6 calibration of
the profile's free `concrete` predicate: whatever has esse in re
(`HasEsseInRe InAct esse`) is concrete. The converse is not stated. It is the
`concreteIsEsse` field of `CausalPowerConcreteness.EsseIntendedProfile`, one
direction, for the Profile and InAct of the stage-two composition. -/
def EsseInReIsConcrete (m : Profile W B) (InAct : B → R → Prop) (esse : R) : Prop :=
  ∀ x, HasEsseInRe InAct esse x → m.concrete x

/-! ## Companion facts (lake-checked, not registered) -/

/-- The calibration and the existence-to-act contract exclude the recorded
non-concrete esse-cause rival outright: its cause exists at `w`, so it is in act
as to being, so it is concrete. No causal premise is used. -/
theorem notSomeEsseCauseNonConcrete (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hConcrete : EsseInReIsConcrete m InAct esse) :
    ¬ SomeEsseCauseNonConcrete m w CausesIn esse := by
  rintro ⟨c, _, _, _, _, hc, hnc⟩
  exact hnc (hConcrete c (hExisting c hc))

/-- `CauseOfBeingInActAsToBeing` entails agency in act. Not registered: registering it
would close a support cycle with `causeOfBeingHasBeingOfAgency`. -/
theorem inActOfHasBeing (InAct : B → R → Prop) (CausesIn : B → B → R → Prop)
    (esse : R) (h : CauseOfBeingInActAsToBeing InAct CausesIn esse) :
    CauseOfBeingIsInAct InAct CausesIn esse :=
  fun c x hc => ⟨esse, h c x hc⟩

/-! ## Finite controls -/

namespace Control

/-- Respect `false` is esse, `true` another perfection. -/
abbrev esse : Bool := false

/-- A one-world Profile on `Bool` with the given existence, concreteness and
grounding. -/
def prof (ex : Bool → Prop) (conc : Bool → Prop) (gr : Bool → Bool → Prop) :
    Profile Unit Bool where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ b => ex b,
             Causes := fun _ _ _ => False }
  concrete := conc
  grounds := fun _ => gr

/-- `false` causes the being of `true` and nothing else. -/
def causesBeing (c x : Bool) (r : Bool) : Prop := c = false ∧ x = true ∧ r = esse

/-- `false` causes the being of `true` and its other perfection. -/
def causesAll (c x : Bool) (_ : Bool) : Prop := c = false ∧ x = true

/-- Omission controls for `everyExistentConcreteOfCalibration`, `esseCausesExistOfCauseHasBeing`,
`esseCauseGroundOfExistentConcreteness` and `causeOfBeingHasBeingOfAgency`, strictness of the
three strength orders, and nonvacuity. -/
def Controls : Prop :=
  -- (1) without the existence-to-act contract: `false` exists, nothing is in act
  (EsseInReIsConcrete (prof (fun _ => True) (fun b => b = true) (fun _ _ => False))
      (fun _ _ => False) esse ∧
    ¬ ExistingInActAt (prof (fun _ => True) (fun b => b = true) (fun _ _ => False)).ontic
      (fun _ _ => False) esse () ∧
    ¬ EveryExistentConcreteAt (prof (fun _ => True) (fun b => b = true) (fun _ _ => False)).ontic
      (prof (fun _ => True) (fun b => b = true) (fun _ _ => False)).concrete ()) ∧
  -- (2) without the calibration: everything exists and is in act, `false` is not concrete
  (ExistingInActAt (prof (fun _ => True) (fun b => b = true) (fun _ _ => False)).ontic
      (fun _ _ => True) esse () ∧
    ¬ EsseInReIsConcrete (prof (fun _ => True) (fun b => b = true) (fun _ _ => False))
      (fun _ _ => True) esse ∧
    ¬ EveryExistentConcreteAt (prof (fun _ => True) (fun b => b = true) (fun _ _ => False)).ontic
      (prof (fun _ => True) (fun b => b = true) (fun _ _ => False)).concrete ()) ∧
  -- (3) without the maxim: only `true` exists and is in act; its absent cause `false` lacks being
  (ExistingInActAt (prof (fun b => b = true) (fun _ => True) (fun _ _ => False)).ontic
      (fun b _ => b = true) esse () ∧
    ActOfEsseSufficesForExistenceAt (prof (fun b => b = true) (fun _ => True) (fun _ _ => False)).ontic
      (fun b _ => b = true) esse () ∧
    ¬ CauseOfABeingHasBeing (fun b _ => b = true) causesBeing esse ∧
    ¬ EsseCausesExistAt (prof (fun b => b = true) (fun _ => True) (fun _ _ => False)) ()
      causesBeing esse) ∧
  -- (4) without the existence-to-act contract: nothing is in act, the maxim is vacuous
  (CauseOfABeingHasBeing (fun _ _ => False) causesBeing esse ∧
    ActOfEsseSufficesForExistenceAt (prof (fun b => b = true) (fun _ => True) (fun _ _ => False)).ontic
      (fun _ _ => False) esse () ∧
    ¬ ExistingInActAt (prof (fun b => b = true) (fun _ => True) (fun _ _ => False)).ontic
      (fun _ _ => False) esse () ∧
    ¬ EsseCausesExistAt (prof (fun b => b = true) (fun _ => True) (fun _ _ => False)) ()
      causesBeing esse) ∧
  -- (5) without act sufficing for existence: everything is in act, only `true` exists
  (CauseOfABeingHasBeing (fun _ _ => True) causesBeing esse ∧
    ExistingInActAt (prof (fun b => b = true) (fun _ => True) (fun _ _ => False)).ontic
      (fun _ _ => True) esse () ∧
    ¬ ActOfEsseSufficesForExistenceAt (prof (fun b => b = true) (fun _ => True) (fun _ _ => False)).ontic
      (fun _ _ => True) esse () ∧
    ¬ EsseCausesExistAt (prof (fun b => b = true) (fun _ => True) (fun _ _ => False)) ()
      causesBeing esse) ∧
  -- (6) bridge without cause existence: `false` is absent
  (EveryExistentConcreteAt (prof (fun b => b = true) (fun _ => True) (fun _ _ => True)).ontic
      (prof (fun b => b = true) (fun _ => True) (fun _ _ => True)).concrete () ∧
    EsseEffectDependsOnItsCause causesBeing esse (fun _ _ => True) ∧
    ActualDependenceIsGrounding (prof (fun b => b = true) (fun _ => True) (fun _ _ => True)) ()
      (fun _ _ => True) ∧
    ¬ EsseCausesExistAt (prof (fun b => b = true) (fun _ => True) (fun _ _ => True)) ()
      causesBeing esse ∧
    ¬ TruthCore.Causality.NecessaryConcreteRouteBridge.EsseCauseIsActualConcreteGround
      (prof (fun b => b = true) (fun _ => True) (fun _ _ => True)) () causesBeing esse) ∧
  -- (7) bridge without existent concreteness: `false` exists, is not concrete
  (EsseCausesExistAt (prof (fun _ => True) (fun b => b = true) (fun _ _ => True)) ()
      causesBeing esse ∧
    EsseEffectDependsOnItsCause causesBeing esse (fun _ _ => True) ∧
    ActualDependenceIsGrounding (prof (fun _ => True) (fun b => b = true) (fun _ _ => True)) ()
      (fun _ _ => True) ∧
    ¬ EveryExistentConcreteAt (prof (fun _ => True) (fun b => b = true) (fun _ _ => True)).ontic
      (prof (fun _ => True) (fun b => b = true) (fun _ _ => True)).concrete () ∧
    ¬ TruthCore.Causality.NecessaryConcreteRouteBridge.EsseCauseIsActualConcreteGround
      (prof (fun _ => True) (fun b => b = true) (fun _ _ => True)) () causesBeing esse) ∧
  -- (8) bridge without dependence: nothing depends, nothing grounds
  (EsseCausesExistAt (prof (fun _ => True) (fun _ => True) (fun _ _ => False)) ()
      causesBeing esse ∧
    EveryExistentConcreteAt (prof (fun _ => True) (fun _ => True) (fun _ _ => False)).ontic
      (prof (fun _ => True) (fun _ => True) (fun _ _ => False)).concrete () ∧
    ActualDependenceIsGrounding (prof (fun _ => True) (fun _ => True) (fun _ _ => False)) ()
      (fun _ _ => False) ∧
    ¬ EsseEffectDependsOnItsCause causesBeing esse (fun _ _ => False) ∧
    ¬ TruthCore.Causality.NecessaryConcreteRouteBridge.EsseCauseIsActualConcreteGround
      (prof (fun _ => True) (fun _ => True) (fun _ _ => False)) () causesBeing esse) ∧
  -- (9) bridge without dependence-to-grounding: dependence holds, nothing grounds
  (EsseCausesExistAt (prof (fun _ => True) (fun _ => True) (fun _ _ => False)) ()
      causesBeing esse ∧
    EveryExistentConcreteAt (prof (fun _ => True) (fun _ => True) (fun _ _ => False)).ontic
      (prof (fun _ => True) (fun _ => True) (fun _ _ => False)).concrete () ∧
    EsseEffectDependsOnItsCause causesBeing esse (fun _ _ => True) ∧
    ¬ ActualDependenceIsGrounding (prof (fun _ => True) (fun _ => True) (fun _ _ => False)) ()
      (fun _ _ => True) ∧
    ¬ TruthCore.Causality.NecessaryConcreteRouteBridge.EsseCauseIsActualConcreteGround
      (prof (fun _ => True) (fun _ => True) (fun _ _ => False)) () causesBeing esse) ∧
  -- (10) agency without act-only-insofar-as-being: `false` is in act only in the other respect
  (CauseOfBeingIsInAct (fun b r => b = true ∨ r = true) causesBeing esse ∧
    ¬ TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading
      (fun b r => b = true ∨ r = true) esse ∧
    ¬ CauseOfBeingInActAsToBeing (fun b r => b = true ∨ r = true) causesBeing esse) ∧
  -- (11) act-only-insofar-as-being without agency: `false` is in act in nothing
  (TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading
      (fun b _ => b = true) esse ∧
    ¬ CauseOfBeingIsInAct (fun b _ => b = true) causesBeing esse ∧
    ¬ CauseOfBeingInActAsToBeing (fun b _ => b = true) causesBeing esse) ∧
  -- (12) strictness: the maxim without preexistence of the other perfection
  (CauseOfABeingHasBeing (fun b r => b = true ∨ r = esse) causesBeing esse ∧
    ¬ TruthCore.Latin.Aquinas.SummaTheologiae.PerfectionsOfEffectPreexistInCauseReading
      (fun b r => b = true ∨ r = esse) causesBeing esse) ∧
  -- (13) strictness: the maxim without the unscoped version (the effect lacks being)
  (CauseOfABeingHasBeing (fun _ _ => False) causesBeing esse ∧
    ¬ CauseOfBeingInActAsToBeing (fun _ _ => False) causesBeing esse) ∧
  -- (14) strictness: the cause has being but not the other perfection it gives
  (CauseOfBeingInActAsToBeing (fun _ r => r = esse) causesAll esse ∧
    ¬ TruthCore.Causality.CausalMapsBatch1.CauseOfBeingHasWhatItGives causesAll
      (fun _ r => r = esse) esse) ∧
  -- (16) strictness: a cause of another perfection, of nobody's being, lacks what it gives
  (TruthCore.Causality.CausalMapsBatch1.CauseOfBeingHasWhatItGives
      (fun c x r => c = false ∧ x = true ∧ r = true) (fun _ _ => False) esse ∧
    ¬ TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives
      (fun c x r => c = false ∧ x = true ∧ r = true) (fun (_ : Bool) (_ : Bool) => False)) ∧
  -- (15) nonvacuity: everything exists, is concrete and in act; `false` causes, and
  -- grounds, the being of `true`, on which `true` depends
  (ExistingInActAt (prof (fun _ => True) (fun _ => True) (fun c x => c = false ∧ x = true)).ontic
      (fun _ _ => True) esse () ∧
    EsseInReIsConcrete (prof (fun _ => True) (fun _ => True) (fun c x => c = false ∧ x = true))
      (fun _ _ => True) esse ∧
    ActOfEsseSufficesForExistenceAt
      (prof (fun _ => True) (fun _ => True) (fun c x => c = false ∧ x = true)).ontic
      (fun _ _ => True) esse () ∧
    CauseOfBeingIsInAct (fun _ _ => True) causesBeing esse ∧
    TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading
      (fun (_ : Bool) (_ : Bool) => True) esse ∧
    TruthCore.Latin.Aquinas.SummaTheologiae.PerfectionsOfEffectPreexistInCauseReading
      (fun _ _ => True) causesBeing esse ∧
    TruthCore.Causality.CausalMapsBatch1.CauseOfBeingHasWhatItGives causesBeing
      (fun _ _ => True) esse ∧
    EsseEffectDependsOnItsCause causesBeing esse (fun x c => x = true ∧ c = false) ∧
    ActualDependenceIsGrounding
      (prof (fun _ => True) (fun _ => True) (fun c x => c = false ∧ x = true)) ()
      (fun x c => x = true ∧ c = false) ∧
    TruthCore.Causality.NecessaryConcreteRouteBridge.EsseCauseIsActualConcreteGround
      (prof (fun _ => True) (fun _ => True) (fun c x => c = false ∧ x = true)) ()
      causesBeing esse ∧
    causesBeing false true esse)

end Control

end TruthCore.Case.Catholicism.CauseOfBeingHasBeing
