import TruthCore.Causality.NecessaryRootFork
import TruthCore.Case.Catholicism.StageOneConvergence
import TruthCore.Case.Catholicism.StageOneQuartaVia
import TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaNecessaryPerSeIsMaximeEns.Solution

/-!
# What a necessary concrete root supplies to the root route (#487)

Source-free and stipulative: nothing here is attributed to any author, and
nothing shows that any premise is true or that any model is metaphysically
possible.

`NECESSARY-CONCRETE-FROM-ACTUAL-GROUNDED` (#553) and `NECESSARY-ROOT-CONTROLS`
already give the conditional and its omission models. This module asks what the
conclusion supplies. No direct premise paraphrase of a route to
`STMT-CATHOLICISM-TRUE` mentions necessity, and `Profile` shares no predicate with the
case's vocabulary (`InAct`, `MoreIn`, `CausesIn`, `PriorSimply`), so a connection
needs named bridges:

* `NecessaryActualRootAt` is the conditional's stronger form: the same witness
  is necessary and an actual root of the selected relation.
* `modalPossible` and `modalIsAt` instantiate the tertia via's parameters at
  accessible worlds. This is a reading of parameters, with worlds in the `Time`
  slot. It does not identify temporal plenitude with accessibility
  (`DISAMB-NECESSARY-INDIVIDUAL-SCOPE`).
* `NecessityCausesAreActualConcreteGrounds` and
  `SimplyPriorIsActualConcreteGround` are open, unattributed bridges into the
  selected relation at the one reading world `w`. The case's vocabulary is not
  world-indexed: `InAct`, `MoreIn` and the rest are read at `w`.

The checked verdict, in `NecessaryRouteControls`: with those bridges and the
tertia via's two convergence bridges the route premise
`MaximumInBeingIsFirstBeing` follows; each of the seven non-logical clauses is
omitted in a model in which the other six hold and that conclusion fails; without
bridges a necessary actual root leaves that premise and two others false in one
model; and if `NecessaryBeingHasBeing` and the two necessity-cause bridges are
replaced by two that cover every actual concretum, the same premise follows from asymmetry of the
selected relation with no necessity, root or contingency premise, in a model with
a contingent maximum.
-/
namespace TruthCore.Causality.NecessaryConcreteRouteBridge

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.NecessaryRootFork
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (MaximumInBeingIsFirstBeing NecessaryBeingHasBeing
  CauseOfNecessaryBeingCausesItsNecessity)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

variable {W B Respect : Type}

/-- Some actual root of the selected relation at `w` exists at every world
accessible from `w`. Rootness is relative to `grounds w` and to actual concreta;
it is not claimed at any other world. -/
def NecessaryActualRootAt (m : Profile W B) (w : W) : Prop :=
  ∃ x, ActualRoot m w x ∧ NecessaryAt m.ontic w x

/-- The tertia via's `Possible`, read as: holding at some world accessible from
`w`. -/
def modalPossible (m : Profile W B) (w : W) : (W → Prop) → Prop :=
  fun C => ∃ v, m.ontic.frame.access w v ∧ C v

/-- The tertia via's `IsAt`, read as world-relative existence. -/
def modalIsAt (m : Profile W B) : B → W → Prop :=
  fun x v => m.ontic.ExistsAt v x

/-- Open bridge: whatever causes the necessity of something other than itself is
an actual concrete ground of it at `w`. An absent or non-concrete cause of
necessity would falsify it. -/
def NecessityCausesAreActualConcreteGrounds (m : Profile W B) (w : W)
    (CausesNecessityOf : B → B → Prop) : Prop :=
  ∀ c x, c ≠ x → CausesNecessityOf c x → ActualConcreteGround m w c x

/-- Open bridge: whatever is simply prior to something other than itself is an
actual concrete ground of it at `w`. -/
def SimplyPriorIsActualConcreteGround (m : Profile W B) (w : W)
    (PriorSimply : B → B → Prop) : Prop :=
  ∀ y x, y ≠ x → PriorSimply y x → ActualConcreteGround m w y x

/-- Some actual root of the selected relation at `w` is necessary in the modal
sense and necessary per se in the modal reading, and every maximum in being, if
any exists, is identical with it. No maximum is asserted to exist. -/
def NecessaryRootIsMaximumAt (m : Profile W B) (w : W) (CausesNecessityOf : B → B → Prop)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop) (esse : Respect) : Prop :=
  ∃ n, ActualRoot m w n ∧ NecessaryAt m.ontic w n ∧
    IsNecessaryPerSe (modalPossible m w) (modalIsAt m) CausesNecessityOf n ∧
    ∀ y, IsMaximumIn InAct MoreIn esse y → y = n

/-! ## The stronger conditional -/

/-- Inhabitedness, restricted well-foundedness and the closing premise give one
witness that is both an actual root and necessary. -/
theorem necessaryActualRootOfGrounded (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w) (hWF : ActualGroundingWF m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle) :
    NecessaryActualRootAt m w := by
  obtain ⟨x, hr⟩ := actualRootExists m w hEM hPop hWF
  rcases hEM (NecessaryAt m.ontic w x) with hn | hn
  · exact ⟨x, hr, hn⟩
  · exact ((everyContingentGrounded_iff_noContingentRoot m w hEM).mp hDep
      (contingentRootOfNonnecessary m w hEM ⟨x, hr, hn⟩)).elim

/-- World-indexed necessity gives necessity in the modal reading, with no excluded
middle. -/
theorem isNecessaryOfNecessaryAt (m : Profile W B) (w : W) (x : B)
    (hn : NecessaryAt m.ontic w x) : IsNecessary (modalPossible m w) (modalIsAt m) x :=
  fun ⟨v, hv, habs⟩ => habs (hn v hv)

/-- A necessary actual root has no cause of its necessity from elsewhere, given
the bridge into the selected relation. -/
theorem isNecessaryPerSeOfRoot (m : Profile W B) (w : W) (x : B)
    (CausesNecessityOf : B → B → Prop)
    (hBridge : NecessityCausesAreActualConcreteGrounds m w CausesNecessityOf)
    (hr : ActualRoot m w x) (hn : NecessaryAt m.ontic w x) :
    IsNecessaryPerSe (modalPossible m w) (modalIsAt m) CausesNecessityOf x :=
  ⟨isNecessaryOfNecessaryAt m w x hn, fun ⟨c, hne, hc⟩ => hr.2 c (hBridge c x hne hc)⟩

/-! ## Composition with the tertia via -/

/-- Adding the bridge into the selected relation and the tertia via's convergence
premises at the modal reading, for the SUPPLIED actual necessary root. The
conclusion names n explicitly so downstream composition cannot lose its identity.
No maximum is asserted to exist. -/
theorem necessaryRootIsMaximumOfRoot (m : Profile W B) (w : W) (CausesNecessityOf : B → B → Prop)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (n : B) (hr : ActualRoot m w n) (hn : NecessaryAt m.ontic w n)
    (hEM : ExcludedMiddle)
    (hBridge : NecessityCausesAreActualConcreteGrounds m w CausesNecessityOf)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hHasBeing : NecessaryBeingHasBeing (modalPossible m w) (modalIsAt m) InAct esse)
    (hCause : CauseOfNecessaryBeingCausesItsNecessity (modalPossible m w) (modalIsAt m)
      CausesIn esse CausesNecessityOf) :
    IsNecessaryPerSe (modalPossible m w) (modalIsAt m) CausesNecessityOf n ∧
      ∀ y, IsMaximumIn InAct MoreIn esse y → y = n := by
  have hPerSe := isNecessaryPerSeOfRoot m w n CausesNecessityOf hBridge hr hn
  refine ⟨hPerSe, fun y hy => ?_⟩
  exact (TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaNecessaryPerSeIsMaximeEns.necessaryPerSeIsMaximeEns
    (modalPossible m w) (modalIsAt m) CausesNecessityOf InAct MoreIn CausesIn esse
    hGenus hHasBeing hCause hEM n hPerSe y hy).symm

/-- Adding the bridge into the selected relation and the tertia via's convergence
premises at the modal reading: one necessary actual root is necessary per se, and
every maximum in being, if any exists, is identical with it. -/
theorem necessaryRootIsMaximum (m : Profile W B) (w : W) (CausesNecessityOf : B → B → Prop)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w) (hWF : ActualGroundingWF m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hBridge : NecessityCausesAreActualConcreteGrounds m w CausesNecessityOf)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hHasBeing : NecessaryBeingHasBeing (modalPossible m w) (modalIsAt m) InAct esse)
    (hCause : CauseOfNecessaryBeingCausesItsNecessity (modalPossible m w) (modalIsAt m)
      CausesIn esse CausesNecessityOf) :
    NecessaryRootIsMaximumAt m w CausesNecessityOf InAct MoreIn esse := by
  obtain ⟨n, hr, hn⟩ := necessaryActualRootOfGrounded m w hPop hWF hDep hEM
  obtain ⟨hPerSe, hIdent⟩ := necessaryRootIsMaximumOfRoot m w CausesNecessityOf
    InAct MoreIn CausesIn esse n hr hn hEM hBridge hGenus hHasBeing hCause
  exact ⟨n, hr, hn, hPerSe, hIdent⟩

/-- The route premise `MaximumInBeingIsFirstBeing` from the necessary root. There
is no inhabitedness hypothesis: anything simply prior to a maximum and other than
it is, by the bridge, itself an actual concretum. -/
theorem maximumFirstOfNecessaryRoot (m : Profile W B) (w : W) (CausesNecessityOf : B → B → Prop)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (PriorSimply : B → B → Prop) (esse : Respect)
    (hWF : ActualGroundingWF m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hBridge : NecessityCausesAreActualConcreteGrounds m w CausesNecessityOf)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hHasBeing : NecessaryBeingHasBeing (modalPossible m w) (modalIsAt m) InAct esse)
    (hCause : CauseOfNecessaryBeingCausesItsNecessity (modalPossible m w) (modalIsAt m)
      CausesIn esse CausesNecessityOf) :
    MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply := by
  intro x hMax y hy
  rcases hEM (y = x) with h | hne
  · exact h
  · have g := hPrior y x hne hy
    obtain ⟨n, hr, _, _, hIdent⟩ := necessaryRootIsMaximum m w CausesNecessityOf InAct MoreIn
      CausesIn esse ⟨y, g.1, g.2.1⟩ hWF hDep hEM hBridge hGenus hHasBeing hCause
    have hxn : x = n := hIdent x hMax
    subst hxn
    exact (hr.2 y g).elim

/-! ## The first-being premise without necessity -/

/-- Actual concreta are never mutually related by `grounds w`. Weaker than
`ActualGroundingWF` (`actualGroundingAsymmetricOfWF`). -/
def ActualGroundingAsymmetric (m : Profile W B) (w : W) : Prop :=
  ∀ a b, ActualConcrete m w a → ActualConcrete m w b → m.grounds w a b → ¬ m.grounds w b a

theorem actualGroundingAsymmetricOfWF (m : Profile W B) (w : W)
    (hWF : ActualGroundingWF m w) : ActualGroundingAsymmetric m w := by
  have key : ∀ a b : {x // ActualConcrete m w x},
      m.grounds w a.1 b.1 → m.grounds w b.1 a.1 → False := by
    intro a
    induction a using hWF.induction with
    | _ a ih => exact fun b hab hba => ih b hba a hba hab
  exact fun a b ha hb hab hba => key ⟨a, ha⟩ ⟨b, hb⟩ hab hba

/-- Every actual concretum has being. Covers contingent concreta, unlike
`NecessaryBeingHasBeing`. -/
def ActualConcretaHaveBeing (m : Profile W B) (w : W) (InAct : B → Respect → Prop)
    (esse : Respect) : Prop :=
  ∀ x, ActualConcrete m w x → InAct x esse

/-- A cause of the being of an actual concretum other than itself is an actual
concrete ground of it. Covers contingent concreta, unlike the composition of
`CauseOfNecessaryBeingCausesItsNecessity` with
`NecessityCausesAreActualConcreteGrounds`. -/
def EsseCauseIsActualConcreteGround (m : Profile W B) (w : W)
    (CausesIn : B → B → Respect → Prop) (esse : Respect) : Prop :=
  ∀ c x, c ≠ x → ActualConcrete m w x → CausesIn c x esse → ActualConcreteGround m w c x

/-- The implication certified by `necessityFreeFirstBeing`: no premise about
necessity, contingency, roots or inhabitedness occurs. -/
def NecessityFreeFirstBeing : Prop :=
  ∀ (W B Respect : Type) (m : Profile W B) (w : W) (InAct : B → Respect → Prop)
    (MoreIn : Respect → B → B → Prop) (CausesIn : B → B → Respect → Prop)
    (PriorSimply : B → B → Prop) (esse : Respect),
    ActualGroundingAsymmetric m w → ExcludedMiddle →
    MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn →
    ActualConcretaHaveBeing m w InAct esse →
    EsseCauseIsActualConcreteGround m w CausesIn esse →
    SimplyPriorIsActualConcreteGround m w PriorSimply →
    MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply

theorem necessityFreeFirstBeing : NecessityFreeFirstBeing := by
  intro W B Respect m w InAct MoreIn CausesIn PriorSimply esse hAsym hEM hGenus hBeing hEsse hPrior
    x hMax y hy
  rcases hEM (y = x) with h | hne
  · exact h
  · have g1 := hPrior y x hne hy
    have hYActual : ActualConcrete m w y := ⟨g1.1, g1.2.1⟩
    have hCause : CausesIn x y esse := hGenus esse x hMax y hne (hBeing y hYActual)
    have g2 := hEsse x y (fun h => hne h.symm) hYActual hCause
    exact (hAsym y x hYActual ⟨g2.1, g2.2.1⟩ g1.2.2 g2.2.2).elim

/-! ## Controls -/

/-- The case's vocabulary on the carrier of a profile. -/
structure Vocabulary (B Respect : Type) where
  InAct : B → Respect → Prop
  MoreIn : Respect → B → B → Prop
  CausesIn : B → B → Respect → Prop
  CausesNecessityOf : B → B → Prop
  PriorSimply : B → B → Prop
  esse : Respect

/-- The seven non-logical hypotheses of `maximumFirstOfNecessaryRoot`. -/
inductive Clause
  | wf | dep | necessityBridge | priorBridge | genus | hasBeing | causeOfNecessity

/-- What each clause says of a profile and a vocabulary. -/
def Clause.holds (m : Profile W B) (w : W) (V : Vocabulary B Respect) : Clause → Prop
  | .wf => ActualGroundingWF m w
  | .dep => EveryContingentGroundedAt m w
  | .necessityBridge => NecessityCausesAreActualConcreteGrounds m w V.CausesNecessityOf
  | .priorBridge => SimplyPriorIsActualConcreteGround m w V.PriorSimply
  | .genus => MaximumInGenusCausesAllInGenusReading V.InAct V.MoreIn V.CausesIn
  | .hasBeing => NecessaryBeingHasBeing (modalPossible m w) (modalIsAt m) V.InAct V.esse
  | .causeOfNecessity =>
      CauseOfNecessaryBeingCausesItsNecessity (modalPossible m w) (modalIsAt m) V.CausesIn V.esse
        V.CausesNecessityOf

/-- All seven clauses hold in one model in which something is maximal in being,
something is simply prior to something else, and the bridges are not vacuous. -/
def AllClausesWitness : Prop :=
  ∃ (W B Respect : Type) (m : Profile W B) (w : W) (V : Vocabulary B Respect),
    (∀ c : Clause, c.holds m w V) ∧ (∃ x, IsMaximumIn V.InAct V.MoreIn V.esse x) ∧
    (∃ y x, y ≠ x ∧ V.PriorSimply y x) ∧ (∃ c x, c ≠ x ∧ V.CausesNecessityOf c x)

/-- Each named clause is omitted in a model in which the other six hold and
`MaximumInBeingIsFirstBeing` fails. Excluded middle is not one of the clauses. -/
def EveryClauseOmitted : Prop :=
  ∀ c : Clause, ∃ (W B Respect : Type) (m : Profile W B) (w : W) (V : Vocabulary B Respect),
    (∀ d : Clause, d ≠ c → d.holds m w V) ∧
    ¬ MaximumInBeingIsFirstBeing V.InAct V.MoreIn V.esse V.PriorSimply

/-- With no bridge, one model has inhabitedness, restricted well-foundedness, the
closing premise and two distinct necessary actual roots, while these three route
premises fail: grades have a maximum, something is moved, and the maximum in being
is first. -/
def NoBridgeNoSlot : Prop :=
  ∃ (W B Respect : Type) (m : Profile W B) (w : W),
    InhabitedConcreteAt m.ontic m.concrete w ∧ ActualGroundingWF m w ∧
    EveryContingentGroundedAt m w ∧
    (∃ a b, a ≠ b ∧ ActualRoot m w a ∧ NecessaryAt m.ontic w a ∧
      ActualRoot m w b ∧ NecessaryAt m.ontic w b) ∧
    ∃ (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
      (MovedIn : B → Respect → Prop) (PriorSimply : B → B → Prop) (esse : Respect),
      ¬ GradesByApproachToAMaximumReading InAct MoreIn ∧
      ¬ SomethingIsMovedReading MovedIn ∧
      ¬ MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply

/-- In one model the hypotheses of `NecessityFreeFirstBeing` hold, something is
maximal in being, and no concretum is necessary at the selected world: that
maximum is contingent. -/
def NecessityFreeWitness : Prop :=
  ∃ (W B Respect : Type) (m : Profile W B) (w : W) (V : Vocabulary B Respect),
    ActualGroundingAsymmetric m w ∧
    MaximumInGenusCausesAllInGenusReading V.InAct V.MoreIn V.CausesIn ∧
    ActualConcretaHaveBeing m w V.InAct V.esse ∧
    EsseCauseIsActualConcreteGround m w V.CausesIn V.esse ∧
    SimplyPriorIsActualConcreteGround m w V.PriorSimply ∧
    (∃ x, IsMaximumIn V.InAct V.MoreIn V.esse x ∧ ContingentAt m.ontic w x) ∧
    ¬ NecessaryConcreteAt m w

/-- Rootness is world-relative: an individual is a necessary actual root at one
world and has an actual concrete ground at an accessible world. -/
def RootNotRigid : Prop :=
  ∃ (W B : Type) (m : Profile W B) (w v : W) (x : B),
    ActualRoot m w x ∧ NecessaryAt m.ontic w x ∧ m.ontic.frame.access w v ∧
      ∃ y, ActualConcreteGround m v y x

/-- A "whatever begins has a ground" premise does not give the closing premise.
Times are `Nat` with `n + 1` earlier than `n`, a past with no first moment (`Nat`
rather than `Int` because `Int`'s order lemmas use `propext`). One individual
exists at every time of one history and at no time of another, so it never begins,
it is contingent, and it has no ground. -/
def BeginningLawControl : Prop :=
  ∃ (m : Profile Bool Unit) (ExistsAtTime : Bool → Unit → Nat → Prop),
    (∀ v x, m.ontic.ExistsAt v x ↔ ∃ t, ExistsAtTime v x t) ∧
    (∀ v x t, ExistsAtTime v x t → (∀ s, t < s → ¬ ExistsAtTime v x s) →
      ∃ y, m.grounds v y x) ∧
    ¬ EveryContingentGroundedAt m true

/-- The stronger conditional, quantified over profiles: inhabitedness, restricted
well-foundedness, the closing premise and excluded middle give one witness that is
both an actual root and necessary. -/
def NecessaryActualRootPrinciple : Prop :=
  ∀ (W B : Type) (m : Profile W B) (w : W),
    InhabitedConcreteAt m.ontic m.concrete w → ActualGroundingWF m w →
    EveryContingentGroundedAt m w → ExcludedMiddle → NecessaryActualRootAt m w

/-- The control bundle. -/
def NecessaryRouteControls : Prop :=
  NecessaryActualRootPrinciple ∧ AllClausesWitness ∧ EveryClauseOmitted ∧ NoBridgeNoSlot ∧
    NecessityFreeFirstBeing ∧ NecessityFreeWitness ∧ RootNotRigid ∧ BeginningLawControl

/-! ## Proofs of the controls -/

/-- A two-candidate single-world profile: everything exists and is concrete. -/
def oneWorld (g : Bool → Bool → Prop) : Profile Unit Bool :=
  { ontic := { frame := { access := fun _ _ => True }, ExistsAt := fun _ _ => True,
               Causes := fun _ _ _ => False }
    concrete := fun _ => True
    grounds := fun _ => g }

/-- The relation with the single edge `a → b`. -/
def edge (a b : Bool) : Bool → Bool → Prop := fun y x => y = a ∧ x = b

theorem wf_of_edge (m : Profile W Bool) (w : W) (a b : Bool) (hne : a ≠ b)
    (h : ∀ y x, m.grounds w y x → edge a b y x) : ActualGroundingWF m w := by
  have noPred : ∀ x : {x // ActualConcrete m w x}, x.1 ≠ b →
      Acc (fun a b : {x // ActualConcrete m w x} => m.grounds w a.1 b.1) x :=
    fun x hx => ⟨_, fun y hy => (hx (h _ _ hy).2).elim⟩
  refine ⟨fun x => ⟨_, fun y hy => noPred y ?_⟩⟩
  have hya : y.1 = a := (h _ _ hy).1
  exact fun hyb => hne (hya.symm.trans hyb)

theorem oneWorld_dep (g : Bool → Bool → Prop) : EveryContingentGroundedAt (oneWorld g) () :=
  fun _ _ _ hc => match hc with
    | ⟨_, _, _, habs⟩ => (habs True.intro).elim

/-- `true` is simply prior to the maximum `false`, so `false` is not first. -/
theorem notFirst {R : Type} (InAct : Bool → R → Prop) (MoreIn : R → Bool → Bool → Prop) (esse : R)
    (hMax : IsMaximumIn InAct MoreIn esse false) :
    ¬ MaximumInBeingIsFirstBeing InAct MoreIn esse (edge true false) :=
  fun h => Bool.noConfusion (h false hMax true ⟨rfl, rfl⟩)

/-- Common vocabulary of the omission models: everything has being, `false` is
above `true`, and `true` is simply prior to `false`. -/
def aboveVocab (Cause Necessity : Bool → Bool → Prop) : Vocabulary Bool Unit where
  InAct := fun _ _ => True
  MoreIn := fun _ y x => y = false ∧ x = true
  CausesIn := fun c x _ => Cause c x
  CausesNecessityOf := Necessity
  PriorSimply := edge true false
  esse := ()

theorem aboveVocab_max (C N : Bool → Bool → Prop) :
    IsMaximumIn (aboveVocab C N).InAct (aboveVocab C N).MoreIn (aboveVocab C N).esse false :=
  ⟨True.intro, fun _ hy => Bool.noConfusion hy.2⟩

theorem aboveVocab_genus (C N : Bool → Bool → Prop) (hC : C false true) :
    MaximumInGenusCausesAllInGenusReading (aboveVocab C N).InAct (aboveVocab C N).MoreIn
      (aboveVocab C N).CausesIn := by
  intro r x hMax y hne _
  cases x with
  | true => exact (hMax.2 false ⟨rfl, rfl⟩).elim
  | false =>
    cases y with
    | false => exact (hne rfl).elim
    | true => exact hC

theorem aboveVocab_notFirst (C N : Bool → Bool → Prop) :
    ¬ MaximumInBeingIsFirstBeing (aboveVocab C N).InAct (aboveVocab C N).MoreIn
      (aboveVocab C N).esse (aboveVocab C N).PriorSimply :=
  notFirst _ _ _ (aboveVocab_max C N)

/-- The ground edge `true → false` makes `true` an actual concrete ground of `false`. -/
theorem prior_bridge_oneWorld : SimplyPriorIsActualConcreteGround (oneWorld (edge true false)) ()
    (edge true false) :=
  fun _ _ _ h => ⟨True.intro, True.intro, h⟩

/-- `oneWorld` with a single non-loop edge has well-founded actual grounding. -/
theorem wf_edge_oneWorld (a b : Bool) (hne : a ≠ b) : ActualGroundingWF (oneWorld (edge a b)) () :=
  wf_of_edge _ _ a b hne fun _ _ h => h

/-- `false → true` is the edge of `edge false true`. -/
theorem falseTrueEdgeBool : edge false true false true := ⟨rfl, rfl⟩

theorem allClausesWitness : AllClausesWitness := by
  let V : Vocabulary Bool Unit :=
    { InAct := fun _ _ => True, MoreIn := fun _ => edge true false,
      CausesIn := fun c x _ => edge true false c x, CausesNecessityOf := edge true false,
      PriorSimply := edge true false, esse := () }
  refine ⟨Unit, Bool, Unit, oneWorld (edge true false), (), V, ?_,
    ⟨true, True.intro, fun _ hy => Bool.noConfusion hy.2⟩,
    ⟨true, false, Bool.noConfusion, rfl, rfl⟩, ⟨true, false, Bool.noConfusion, rfl, rfl⟩⟩
  intro c
  cases c with
  | wf => exact wf_edge_oneWorld true false Bool.noConfusion
  | dep => exact oneWorld_dep _
  | necessityBridge => exact fun _ _ _ h => ⟨True.intro, True.intro, h⟩
  | priorBridge => exact fun _ _ _ h => ⟨True.intro, True.intro, h⟩
  | genus =>
    intro r x hMax y hne _
    cases x with
    | false => exact (hMax.2 true ⟨rfl, rfl⟩).elim
    | true =>
      cases y with
      | true => exact (hne rfl).elim
      | false => exact ⟨rfl, rfl⟩
  | hasBeing => exact fun _ _ => True.intro
  | causeOfNecessity => exact fun _ _ _ h => h

/-- The profile of the `dep` omission: `true` exists only at world `true`, `false`
at both, and `true` grounds `false` at every world. -/
def contingentRootProfile : Profile Bool Bool :=
  { ontic := { frame := { access := fun _ _ => True },
               ExistsAt := fun v x => x = false ∨ v = true,
               Causes := fun _ _ _ => False }
    concrete := fun _ => True
    grounds := fun _ => edge true false }

theorem everyClauseOmitted : EveryClauseOmitted := by
  intro c
  cases c with
  | wf =>
    let g : Bool → Bool → Prop := fun y x => y ≠ x
    let C := edge false true
    refine ⟨Unit, Bool, Unit, oneWorld g, (), aboveVocab C C, ?_, aboveVocab_notFirst C C⟩
    intro d hd
    cases d with
    | wf => exact (hd rfl).elim
    | dep => exact oneWorld_dep _
    | necessityBridge =>
      exact fun _ _ hne _ => ⟨True.intro, True.intro, hne⟩
    | priorBridge =>
      exact fun _ _ hne _ => ⟨True.intro, True.intro, hne⟩
    | genus => exact aboveVocab_genus C C falseTrueEdgeBool
    | hasBeing => exact fun _ _ => True.intro
    | causeOfNecessity => exact fun _ _ _ h => h
  | dep =>
    let C := edge false true
    let N : Bool → Bool → Prop := fun _ _ => False
    refine ⟨Bool, Bool, Unit, contingentRootProfile, true, aboveVocab C N, ?_,
      aboveVocab_notFirst C N⟩
    intro d hd
    cases d with
    | wf => exact wf_of_edge _ _ true false Bool.noConfusion fun _ _ h => h
    | dep => exact (hd rfl).elim
    | necessityBridge => exact fun _ _ _ h => h.elim
    | priorBridge =>
      exact fun _ _ _ h => ⟨True.intro, Or.inr rfl, h⟩
    | genus => exact aboveVocab_genus C N falseTrueEdgeBool
    | hasBeing => exact fun _ _ => True.intro
    | causeOfNecessity =>
      intro c x hNec hc
      have hx : x = true := hc.2
      subst hx
      exact (hNec ⟨false, True.intro, fun h => h.elim Bool.noConfusion Bool.noConfusion⟩).elim
  | necessityBridge =>
    let C := edge false true
    refine ⟨Unit, Bool, Unit, oneWorld (edge true false), (), aboveVocab C C, ?_,
      aboveVocab_notFirst C C⟩
    intro d hd
    cases d with
    | wf => exact wf_edge_oneWorld true false Bool.noConfusion
    | dep => exact oneWorld_dep _
    | necessityBridge => exact (hd rfl).elim
    | priorBridge => exact prior_bridge_oneWorld
    | genus => exact aboveVocab_genus C C falseTrueEdgeBool
    | hasBeing => exact fun _ _ => True.intro
    | causeOfNecessity => exact fun _ _ _ h => h
  | priorBridge =>
    let C := edge false true
    refine ⟨Unit, Bool, Unit, oneWorld C, (), aboveVocab C C, ?_, aboveVocab_notFirst C C⟩
    intro d hd
    cases d with
    | wf => exact wf_edge_oneWorld false true Bool.noConfusion
    | dep => exact oneWorld_dep _
    | necessityBridge => exact fun _ _ _ h => ⟨True.intro, True.intro, h⟩
    | priorBridge => exact (hd rfl).elim
    | genus => exact aboveVocab_genus C C falseTrueEdgeBool
    | hasBeing => exact fun _ _ => True.intro
    | causeOfNecessity => exact fun _ _ _ h => h
  | genus =>
    let N : Bool → Bool → Prop := fun _ _ => False
    refine ⟨Unit, Bool, Unit, oneWorld (edge true false), (), aboveVocab N N, ?_,
      aboveVocab_notFirst N N⟩
    intro d hd
    cases d with
    | wf => exact wf_edge_oneWorld true false Bool.noConfusion
    | dep => exact oneWorld_dep _
    | necessityBridge => exact fun _ _ _ h => h.elim
    | priorBridge => exact prior_bridge_oneWorld
    | genus => exact (hd rfl).elim
    | hasBeing => exact fun _ _ => True.intro
    | causeOfNecessity => exact fun _ _ _ h => h
  | hasBeing =>
    let V : Vocabulary Bool Unit :=
      { InAct := fun x _ => x = false, MoreIn := fun _ _ _ => False,
        CausesIn := fun _ _ _ => False, CausesNecessityOf := fun _ _ => False,
        PriorSimply := edge true false, esse := () }
    refine ⟨Unit, Bool, Unit, oneWorld (edge true false), (), V, ?_,
      notFirst V.InAct V.MoreIn () ⟨rfl, fun _ h => h⟩⟩
    intro d hd
    cases d with
    | wf => exact wf_edge_oneWorld true false Bool.noConfusion
    | dep => exact oneWorld_dep _
    | necessityBridge => exact fun _ _ _ h => h.elim
    | priorBridge => exact prior_bridge_oneWorld
    | genus =>
      intro r x hMax y hne hy
      have hxf : x = false := hMax.1
      have hyf : y = false := hy
      exact (hne (hyf.trans hxf.symm)).elim
    | hasBeing => exact (hd rfl).elim
    | causeOfNecessity => exact fun _ _ _ h => h.elim
  | causeOfNecessity =>
    let C := edge false true
    let N : Bool → Bool → Prop := fun _ _ => False
    refine ⟨Unit, Bool, Unit, oneWorld (edge true false), (), aboveVocab C N, ?_,
      aboveVocab_notFirst C N⟩
    intro d hd
    cases d with
    | wf => exact wf_edge_oneWorld true false Bool.noConfusion
    | dep => exact oneWorld_dep _
    | necessityBridge => exact fun _ _ _ h => h.elim
    | priorBridge => exact prior_bridge_oneWorld
    | genus => exact aboveVocab_genus C N falseTrueEdgeBool
    | hasBeing => exact fun _ _ => True.intro
    | causeOfNecessity => exact (hd rfl).elim

theorem noBridgeNoSlot : NoBridgeNoSlot := by
  let g : Bool → Bool → Prop := fun _ _ => False
  have root : ∀ x, ActualRoot (oneWorld g) () x :=
    fun x => ⟨⟨True.intro, True.intro⟩, fun _ h => h.2.2⟩
  refine ⟨Unit, Bool, Bool, oneWorld g, (), ⟨true, True.intro, True.intro⟩,
    wf_of_noEdge _ _ fun _ _ h => h, oneWorld_dep _,
    ⟨true, false, Bool.noConfusion, root true, fun _ _ => True.intro,
      root false, fun _ _ => True.intro⟩,
    fun _ _ => True,
    fun r y x => r = false ∧ y ≠ x ∨ r = true ∧ y = false ∧ x = true,
    fun _ _ => False, edge true false, true, ?_, fun ⟨_, _, h⟩ => h, ?_⟩
  · intro h
    obtain ⟨x, hx⟩ := h false ⟨true, false, Or.inl ⟨rfl, Bool.noConfusion⟩⟩
    cases x with
    | true => exact hx.2 false (Or.inl ⟨rfl, Bool.noConfusion⟩)
    | false => exact hx.2 true (Or.inl ⟨rfl, Bool.noConfusion⟩)
  · exact notFirst _ _ true ⟨True.intro, fun _ hy => hy.elim
      (fun h => Bool.noConfusion h.1) (fun h => Bool.noConfusion h.2.2)⟩

theorem necessityFreeWitness : NecessityFreeWitness := by
  let m : Profile Bool Unit :=
    { ontic := { frame := { access := fun _ _ => True }, ExistsAt := fun v _ => v = true,
                 Causes := fun _ _ _ => False }
      concrete := fun _ => True
      grounds := fun _ _ _ => False }
  let V : Vocabulary Unit Unit :=
    { InAct := fun _ _ => True, MoreIn := fun _ _ _ => False,
      CausesIn := fun _ _ _ => False, CausesNecessityOf := fun _ _ => False,
      PriorSimply := fun _ _ => False, esse := () }
  have hAbsent : ¬ m.ontic.ExistsAt false () := Bool.noConfusion
  refine ⟨Bool, Unit, Unit, m, true, V, fun _ _ _ _ h => h.elim,
    fun _ _ _ _ hne => (hne rfl).elim, fun _ _ => True.intro, fun _ _ _ _ h => h.elim,
    fun _ _ _ h => h.elim,
    ⟨(), ⟨True.intro, fun _ h => h⟩, rfl, false, True.intro, hAbsent⟩, ?_⟩
  rintro ⟨_, _, _, hn⟩
  exact hAbsent (hn false True.intro)

theorem rootNotRigid : RootNotRigid := by
  let m : Profile Bool Bool :=
    { ontic := { frame := { access := fun _ _ => True }, ExistsAt := fun _ _ => True,
                 Causes := fun _ _ _ => False }
      concrete := fun _ => True
      grounds := fun v y x => v = true ∧ y = true ∧ x = false }
  exact ⟨Bool, Bool, m, false, true, false,
    ⟨⟨True.intro, True.intro⟩, fun _ h => Bool.noConfusion h.2.2.1⟩, fun _ _ => True.intro,
    True.intro, true, True.intro, True.intro, rfl, rfl, rfl⟩

theorem beginningLawControl : BeginningLawControl := by
  let E : Bool → Unit → Nat → Prop := fun v _ _ => v = true
  let m : Profile Bool Unit :=
    { ontic := { frame := { access := fun _ _ => True }, ExistsAt := fun v x => ∃ t, E v x t,
                 Causes := fun _ _ _ => False }
      concrete := fun _ => True
      grounds := fun _ _ _ => False }
  refine ⟨m, E, fun _ _ => Iff.rfl, ?_, ?_⟩
  · intro v x t ht hnone
    exact (hnone (t + 1) (Nat.lt_succ_self t) ht).elim
  · intro h
    have hAbsent : ¬ m.ontic.ExistsAt false () := fun ⟨_, ht⟩ => Bool.noConfusion ht
    obtain ⟨_, _, _, hg⟩ := h () True.intro ⟨0, rfl⟩ ⟨⟨0, rfl⟩, false, True.intro, hAbsent⟩
    exact hg

theorem necessaryRouteControls : NecessaryRouteControls :=
  ⟨fun _ _ m w hPop hWF hDep hEM => necessaryActualRootOfGrounded m w hPop hWF hDep hEM,
    allClausesWitness, everyClauseOmitted, noBridgeNoSlot, necessityFreeFirstBeing,
    necessityFreeWitness, rootNotRigid, beginningLawControl⟩

end TruthCore.Causality.NecessaryConcreteRouteBridge
