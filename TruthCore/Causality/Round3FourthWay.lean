module

public import TruthCore.Causality.DirectEsseRootUniquenessAtBeing
public import TruthCore.Causality.MaximumDefinitionFork
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaAscent
public import TruthCore.Case.Catholicism.StageTwo
public import TruthCore.Greek.Aristotle.Metaphysics
public import TruthCore.Logic.ExcludedMiddle

/-! Round 3, Fourth Way: derivations of degree and maximum premises

Analyst formulations, attribution deferred. Nine exploration maps
(`explorations/grades-to-maximum-at-being.toml`, `more-in-strict-degree.toml`,
`bearers-degree-directed.toml`, `greatest-degree-causes-all.toml`,
`maximum-in-genus-causes-all.toml`, `being-graded-by-approach.toml`,
`more-such-has-perfection.toml`, `as-to-being-so-to-truth.toml`,
`god-is-maximal-in-being.toml`) propose derivations of stated or bare
Fourth Way premises on root paths. Every new proposition below is an OPEN
premise: a bare analyst bridge, or a reading recorded as `supported` by an
existing claim with its gap. None is attributed as stated.

Vocabulary reused exactly: `InAct`, `MoreIn`, `CausesIn`, `IsMaximumIn`,
`CausesAllInGenus` of the quarta via (DEF-MORE-IN, DEF-CAUSE-OF-PERFECTION,
DEF-MAXIMUM-IN-A-PERFECTION), `GreatestDegreeBearer` (DEF-GREATEST-DEGREE-IN-A-PERFECTION),
the order by approach to a primary `near`/`p` (DEF-ORDER-BY-APPROACH-TO-A-PRIMARY,
DEF-STRICT-PRIMACY), the calibration `Frame` (DEF-MAXIMUM-CALIBRATION-PROFILE)
and the `Has`/`MoreIn` correspondence of *Metaphysics* II.1. New parameters:

* `deg : R → B → D` (DEF-PER-RESPECT-DEGREE-FAMILY): a represented degree of
  each being in each perfection, in a Mathlib `Preorder` `D`. It extends the
  single selected-respect `value` of the calibration frame to every respect. No
  totality, injectivity or homogeneity of analogical being is assumed.
* `null : D` (DEF-NULL-DEGREE): the represented degree of lacking a perfection
  altogether, as no heat at all. Only what the premises below say constrains it.
* `intel : R` (DEF-INTELLIGIBILITY-OF-THINGS): the respect of being knowable,
  that is, of standing in relation to an intellect (ST I q.16 a.3). It is a
  respect like `truth` and `being`; nothing identifies it with either.

Mathlib order lemmas used here are axiom-free on an abstract `Preorder`; the
results that need case distinctions take excluded middle as an explicit premise.
-/

@[expose] public section

namespace TruthCore.Causality.Round3FourthWay
open TruthCore.Latin.Aquinas.SummaTheologiae

universe u v w

/-! ## Represented degrees in every respect -/

/-- Whatever is more `r` than something has a strictly higher represented
degree of `r` (one direction of a calibration, for every respect and every
pair, bearers or not). -/
def MoreInExceedsDegree {B : Sort u} {R : Sort v} {D : Type w} [Preorder D]
    (MoreIn : R → B → B → Prop) (deg : R → B → D) : Prop :=
  ∀ r x y, MoreIn r x y → deg r y < deg r x

/-- No represented degree lies below the null degree: lacking a perfection
altogether is the lowest standing in it. -/
def NoDegreeBelowNull {B : Sort u} {R : Sort v} {D : Type w} [Preorder D]
    (deg : R → B → D) (null : D) : Prop :=
  ∀ r y, null ≤ deg r y

/-- Whatever stands strictly above the null degree of `r` has `r`: what has some
heat is hot. -/
def AboveNullDegreeHasThePerfection {B : Sort u} {R : Sort v} {D : Type w}
    [Preorder D] (InAct : B → R → Prop) (deg : R → B → D) (null : D) : Prop :=
  ∀ r x, null < deg r x → InAct x r

/-- Among bearers of `r`, a strictly higher represented degree is being more
`r` (the other direction of a calibration, restricted to bearers). -/
def DegreeExcessAmongBearersIsMoreIn {B : Sort u} {R : Sort v} {D : Type w}
    [Preorder D] (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (deg : R → B → D) : Prop :=
  ∀ r x y, InAct x r → InAct y r → deg r y < deg r x → MoreIn r x y

/-- In every perfection, any two bearers have a bearer at a represented degree
at least as high as both (DirectedBearers at every respect). -/
def BearerDegreesDirectedInEveryGenus {B : Sort u} {R : Sort v} {D : Type w}
    [Preorder D] (InAct : B → R → Prop) (deg : R → B → D) : Prop :=
  ∀ r x y, InAct x r → InAct y r →
    ∃ z, InAct z r ∧ deg r x ≤ deg r z ∧ deg r y ≤ deg r z

/-- The greatest-degree genus principle at every perfection: for each `r`, a
bearer at the greatest represented degree of `r` causes `r` in every other
bearer. The strong, every-respect version of
`GreatestDegreeCausesAllInGenusReading`, which is read at one supplied
perfection. -/
def GreatestDegreeCausesAllInEveryGenus {B : Type u} {R : Sort v} {D : Type w}
    [Preorder D] (InAct : B → R → Prop) (CausesIn : B → B → R → Prop)
    (deg : R → B → D) : Prop :=
  ∀ r, GreatestDegreeCausesAllInGenusReading InAct CausesIn r (deg r)

/-! ## Grades of being -/

/-- No infinite ascent in being: there is no sequence of beings each more a
being than the one before. Stated as Lean's `WellFounded` for the relation
"`y` is more in `esse` than `x`". -/
def NoInfiniteAscentInBeing {B : Sort u} {R : Sort v}
    (MoreIn : R → B → B → Prop) (esse : R) : Prop :=
  WellFounded (fun y x => MoreIn esse y x)

/-- Grades are found in being: something is more a being than something. -/
def GradesFoundInBeing {B : Sort u} {R : Sort v}
    (MoreIn : R → B → B → Prop) (esse : R) : Prop :=
  ∃ x y, MoreIn esse x y

/-- Each thing has as much of a perfection as it approaches the primary
(*unumquodque tantum habet de esse, quantum ei appropinquat*, ST I q.3 a.5
ad 2): the represented degrees and the nearness to the primary are ordered
alike, for every pair of beings. -/
def AsMuchAsItApproaches {B : Sort u} {D : Type w} {E : Type v} [Preorder D]
    [Preorder E] (value : B → D) (near : B → E) : Prop :=
  ∀ x y, value x ≤ value y ↔ near x ≤ near y

/-- For every pair of beings, one is more `r` than another exactly when its
represented degree of `r` is strictly higher (global calibration: unlike
`StrictDegreeCalibration`, not restricted to bearers). -/
def MoreInMatchesDegreeEverywhere {B : Sort u} {R : Sort v} {D : Type w}
    [Preorder D] (MoreIn : R → B → B → Prop) (r : R) (value : B → D) : Prop :=
  ∀ x y, MoreIn r x y ↔ value y < value x

/-- Whatever is God is the primary of the order of being by approach: the
being every other is measured against (ST I q.3 a.5 ad 2, *dicitur tamen
mensura omnium*). -/
def GodIsThePrimaryOfBeing {B : Sort u} (IsGod : B → Prop) (p : B) : Prop :=
  ∀ g, IsGod g → g = p

/-! ## Calibration frame (one selected perfection) -/

section Frame
open TruthCore.Causality.MaximumDefinitionFork

/-- Any two bearers of the selected perfection have comparable represented
degrees. Totality on bearers only; ties are allowed. -/
def BearerDegreesComparable {Degree : Type} [Preorder Degree]
    (f : Frame Degree) : Prop :=
  ∀ x y, f.InAct x f.selected → f.InAct y f.selected →
    f.value x ≤ f.value y ∨ f.value y ≤ f.value x

/-- Some bearer of the selected perfection is at its greatest represented
degree. -/
def SomeBearerHasGreatestDegree {Degree : Type} [Preorder Degree]
    (f : Frame Degree) : Prop :=
  ∃ m, GreatestDegreeBearer f.InAct f.selected f.value m

end Frame

/-! ## Truth of things -/

/-- Truth said of things is intelligibility (ST I q.16 a.1, a.3): a thing has
truth exactly when it is intelligible, and one thing is more true than another
exactly when it is more intelligible. -/
def TruthOfThingsIsIntelligibility {E : Sort u} {R : Sort v}
    (Has : E → R → Prop) (MoreIn : R → E → E → Prop) (truth intel : R) : Prop :=
  (∀ x, Has x truth ↔ Has x intel) ∧ ∀ x y, MoreIn truth x y ↔ MoreIn intel x y

/-- Intelligibility is proportioned to being (ST I q.16 a.3, *unumquodque
inquantum habet de esse, intantum est cognoscibile*): a thing is intelligible
exactly when it has being, and more intelligible exactly when it is more a
being. -/
def IntelligibilityProportionedToBeing {E : Sort u} {R : Sort v}
    (Has : E → R → Prop) (MoreIn : R → E → E → Prop) (intel being : R) : Prop :=
  (∀ x, Has x intel ↔ Has x being) ∧ ∀ x y, MoreIn intel x y ↔ MoreIn being x y

/-! ## Controls

Hand-written finite (and one infinite) interpretations: for each premise of
each derivation other than excluded middle, a model in which the other
premises hold and the conclusion fails, and one joint nonvacuity witness.
Carriers are `Bool`, `Unit`, the three-element `Trio` and `Nat`; degrees are
`Nat` or the product `Nat × Nat` (for incomparable degrees). `scripts/countermodel.py`
does not handle the `Preorder` parameter, so these models are written by hand.
Satisfiability and omission only; no model is claimed to describe reality.
Excluded middle is not stated in the omission conditions: it is logical, and
it is not provable without an axiom. -/

namespace Control
open TruthCore.Causality.MaximumDefinitionFork
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Case.Catholicism
open TruthCore.Greek.Aristotle.Metaphysics

/-- One-element carriers are `Unit`; these instances decide its quantifiers
without axioms. -/
instance unitForallDecidable (P : Unit → Prop) [h : Decidable (P ())] : Decidable (∀ x, P x) :=
  match h with
  | isTrue hp => isTrue (fun _ => hp)
  | isFalse hn => isFalse (fun hall => hn (hall ()))

instance unitExistsDecidable (P : Unit → Prop) [h : Decidable (P ())] : Decidable (∃ x, P x) :=
  match h with
  | isTrue hp => isTrue ⟨(), hp⟩
  | isFalse hn => isFalse (fun ⟨_, hx⟩ => hn hx)

/-- A three-element carrier: a primary `top` and two lower beings `a`, `b`.
It has no `Fintype` instance, so its quantifiers are decided by the instances
below, without axioms. -/
inductive Trio where
  | top
  | a
  | b
  deriving DecidableEq

instance trioForallDecidable (P : Trio → Prop) [DecidablePred P] :
    Decidable (∀ x, P x) :=
  if h0 : P .top then
    if h1 : P .a then
      if h2 : P .b then
        isTrue (fun x => match x with
          | .top => h0
          | .a => h1
          | .b => h2)
      else isFalse (fun hall => h2 (hall .b))
    else isFalse (fun hall => h1 (hall .a))
  else isFalse (fun hall => h0 (hall .top))

instance trioExistsDecidable (P : Trio → Prop) [DecidablePred P] :
    Decidable (∃ x, P x) :=
  if h0 : P .top then isTrue ⟨.top, h0⟩
  else if h1 : P .a then isTrue ⟨.a, h1⟩
  else if h2 : P .b then isTrue ⟨.b, h2⟩
  else isFalse (fun ⟨x, hx⟩ => match x, hx with
    | .top, hx => h0 hx
    | .a, hx => h1 hx
    | .b, hx => h2 hx)

/-- `top` is the only non-bearer. -/
def Trio.low : Trio → Bool
  | .top => false
  | .a => true
  | .b => true

/-! Shared Boolean dictionaries: `true` is the higher being. -/

/-- Everything has the perfection. -/
abbrev all : Bool → Unit → Prop := fun _ _ => True
/-- Nothing has the perfection. -/
abbrev none' : Bool → Unit → Prop := fun _ _ => False
/-- Only `true` has the perfection. -/
abbrev onlyTrue : Bool → Unit → Prop := fun b _ => b = true
/-- Only `false` has the perfection. -/
abbrev onlyFalse : Bool → Unit → Prop := fun b _ => b = false
/-- `true` is more such than `false`, and nothing else. -/
abbrev up : Unit → Bool → Bool → Prop := fun _ x y => x = true ∧ y = false
/-- `false` is more such than `true`, and nothing else. -/
abbrev down : Unit → Bool → Bool → Prop := fun _ x y => x = false ∧ y = true
/-- No comparisons. -/
abbrev flat : Unit → Bool → Bool → Prop := fun _ _ _ => False
/-- Represented degree: `true` at 1, `false` at 0. -/
abbrev val2 : Bool → Nat := fun b => if b then 1 else 0
/-- Represented degree: `true` at 0, `false` at 1. -/
abbrev valRev : Bool → Nat := fun b => if b then 0 else 1
/-- Every being at degree 0. -/
abbrev zero : Bool → Nat := fun _ => 0
/-- `val2` in every respect. -/
abbrev deg2 : Unit → Bool → Nat := fun _ => val2
/-- `true` causes the perfection in everything. -/
abbrev fromTrue : Bool → Bool → Unit → Prop := fun c _ _ => c = true
/-- `false` causes the perfection in everything. -/
abbrev fromFalse : Bool → Bool → Unit → Prop := fun c _ _ => c = false
/-- No causing. -/
abbrev noCause : Bool → Bool → Unit → Prop := fun _ _ _ => False
/-- `false` is a creature; `true` is not. -/
abbrev isFalse' : Bool → Prop := fun b => b = false
/-- `true` is God. -/
abbrev isTrue' : Bool → Prop := fun b => b = true
/-- Nothing is a creature. -/
abbrev noCreature : Bool → Prop := fun _ => False

/-- Two incomparable represented degrees in the product order. -/
abbrev incomparableValue : Bool → Nat × Nat := fun b => if b then (1, 0) else (0, 1)

/-- A calibration frame on the Boolean dictionaries. -/
abbrev boolFrame (Degree : Type) (InAct : Bool → Unit → Prop) (MoreIn : Unit → Bool → Bool → Prop)
    (CausesIn : Bool → Bool → Unit → Prop) (value : Bool → Degree) : Frame Degree where
  Being := Bool
  Respect := Unit
  InAct := InAct
  MoreIn := MoreIn
  CausesIn := CausesIn
  selected := ()
  value := value
  Maxime := fun _ => True

/-! ### moreSuchFromPositiveDegree -/

def moreSuch.omit_hExceed : Prop :=
  ¬ MoreInExceedsDegree up (fun _ _ => (0 : Nat)) ∧
  NoDegreeBelowNull (fun (_ : Unit) (_ : Bool) => (0 : Nat)) 0 ∧
  AboveNullDegreeHasThePerfection none' (fun _ _ => (0 : Nat)) 0 ∧
  ¬ MoreSuchHasThePerfectionReading none' up

def moreSuch.omit_hNull : Prop :=
  MoreInExceedsDegree up deg2 ∧ ¬ NoDegreeBelowNull deg2 1 ∧
  AboveNullDegreeHasThePerfection none' deg2 1 ∧
  ¬ MoreSuchHasThePerfectionReading none' up

def moreSuch.omit_hPos : Prop :=
  MoreInExceedsDegree up deg2 ∧ NoDegreeBelowNull deg2 0 ∧
  ¬ AboveNullDegreeHasThePerfection none' deg2 0 ∧
  ¬ MoreSuchHasThePerfectionReading none' up

/-! ### gradesAtBeingFromNoInfiniteAscent -/

/-- On `Nat`, each number is more a being than every smaller one. -/
abbrev natUp : Unit → Nat → Nat → Prop := fun _ y x => x < y

/-- Without the ascent premise: an unbounded ascent in which everything has being. -/
def gradesAscent.omit_hWF : Prop :=
  ¬ NoInfiniteAscentInBeing natUp () ∧
  MoreSuchHasThePerfectionReading (fun (_ : Nat) (_ : Unit) => True) natUp ∧
  ¬ GradesToMaximumAtBeing (fun (_ : Nat) (_ : Unit) => True) natUp ()

def gradesAscent.omit_hMore : Prop :=
  NoInfiniteAscentInBeing up () ∧ ¬ MoreSuchHasThePerfectionReading none' up ∧
  ¬ GradesToMaximumAtBeing none' up ()

/-! ### gradesAtBeingFromApproach -/

def gradesApproach.omit_hApproach : Prop :=
  ¬ ApproachToPrimaryReading none' up () valRev false ∧ StrictPrimacyReading valRev false ∧
  ¬ GradesToMaximumAtBeing none' up ()

def gradesApproach.omit_hStrict : Prop :=
  ApproachToPrimaryReading onlyFalse up () val2 false ∧ ¬ StrictPrimacyReading val2 false ∧
  ¬ GradesToMaximumAtBeing onlyFalse up ()

/-! ### godMaximalFromPrimaryOfBeing -/

def godPrimary.omit_hPrimary : Prop :=
  ¬ GodIsThePrimaryOfBeing isTrue' false ∧ ApproachToPrimaryReading all down () valRev false ∧
  StrictPrimacyReading valRev false ∧ ¬ GodIsMaximalInBeing isTrue' all down ()

def godPrimary.omit_hApproach : Prop :=
  GodIsThePrimaryOfBeing isFalse' false ∧ ¬ ApproachToPrimaryReading none' down () valRev false ∧
  StrictPrimacyReading valRev false ∧ ¬ GodIsMaximalInBeing isFalse' none' down ()

def godPrimary.omit_hStrict : Prop :=
  GodIsThePrimaryOfBeing isFalse' false ∧ ApproachToPrimaryReading all up () val2 false ∧
  ¬ StrictPrimacyReading val2 false ∧ ¬ GodIsMaximalInBeing isFalse' all up ()

/-! ### strictCalibrationFromApproachMeasure -/

def calibration.omit_hApproach : Prop :=
  ¬ ApproachToPrimaryReading all flat () val2 true ∧ AsMuchAsItApproaches val2 val2 ∧
  ¬ StrictDegreeCalibration (boolFrame Nat all flat noCause val2)

def calibration.omit_hMeasure : Prop :=
  ApproachToPrimaryReading all up () val2 true ∧ ¬ AsMuchAsItApproaches zero val2 ∧
  ¬ StrictDegreeCalibration (boolFrame Nat all up noCause zero)

/-! ### directedFromComparableDegrees, directedFromGreatestBearer -/

def directed.omit_hComp : Prop :=
  ¬ BearerDegreesComparable (boolFrame (Nat × Nat) all flat noCause incomparableValue) ∧
  ¬ DirectedBearers (boolFrame (Nat × Nat) all flat noCause incomparableValue)

def directed.omit_hTop : Prop :=
  ¬ SomeBearerHasGreatestDegree (boolFrame (Nat × Nat) all flat noCause incomparableValue) ∧
  ¬ DirectedBearers (boolFrame (Nat × Nat) all flat noCause incomparableValue)

/-! ### greatestCausesFromOrderedPrimary -/

/-- Trio dictionaries: `top` is the primary, `a` and `b` bear the
perfection, are creatures and are tied below it. -/
abbrev optIn : Trio → Unit → Prop := fun o _ => o.low = true
abbrev optFlat : Unit → Trio → Trio → Prop := fun _ _ _ => False
abbrev optValue : Trio → Nat := fun o => if o.low then 1 else 2
abbrev optFromNone : Trio → Trio → Unit → Prop := fun c _ _ => c = .top
abbrev optCreature : Trio → Prop := fun o => o.low = true

def greatestOrdered.omit_hApproach : Prop :=
  ¬ ApproachToPrimaryReading optIn optFlat () optValue .top ∧
  StrictPrimacyReading optValue .top ∧
  OrderedToPrimaryAsCauseReading optIn optFromNone optCreature () .top ∧
  OthersAreCreaturesReading optCreature .top ∧
  ¬ GreatestDegreeCausesAllInGenusReading optIn optFromNone () optValue

def greatestOrdered.omit_hStrict : Prop :=
  ApproachToPrimaryReading all flat () zero true ∧ ¬ StrictPrimacyReading zero true ∧
  OrderedToPrimaryAsCauseReading all fromTrue isFalse' () true ∧
  OthersAreCreaturesReading isFalse' true ∧
  ¬ GreatestDegreeCausesAllInGenusReading all fromTrue () zero

def greatestOrdered.omit_hOrdered : Prop :=
  ApproachToPrimaryReading all up () val2 true ∧ StrictPrimacyReading val2 true ∧
  ¬ OrderedToPrimaryAsCauseReading all noCause isFalse' () true ∧
  OthersAreCreaturesReading isFalse' true ∧
  ¬ GreatestDegreeCausesAllInGenusReading all noCause () val2

def greatestOrdered.omit_hOthers : Prop :=
  ApproachToPrimaryReading all up () val2 true ∧ StrictPrimacyReading val2 true ∧
  OrderedToPrimaryAsCauseReading all noCause noCreature () true ∧
  ¬ OthersAreCreaturesReading noCreature true ∧
  ¬ GreatestDegreeCausesAllInGenusReading all noCause () val2

/-! ### greatestCausesFromMaximalPrinciple -/

def greatestMaximal.omit_hMax : Prop :=
  ¬ MaximumInGenusCausesAllInGenusReading all up noCause ∧
  MoreSuchHasThePerfectionReading all up ∧
  StrictDegreeCalibration (boolFrame Nat all up noCause val2) ∧
  ¬ GreatestDegreeCausesAllInGenusReading all noCause () val2

/-- `top` is more such than `a` and `b` without having the perfection. -/
abbrev optOver : Unit → Trio → Trio → Prop :=
  fun _ x y => x = .top ∧ y.low = true
abbrev optLow : Trio → Nat := fun o => if o.low then 0 else 5
abbrev optNoCause : Trio → Trio → Unit → Prop := fun _ _ _ => False

/-- A calibration frame on `Trio`. -/
abbrev optFrame : Frame Nat where
  Being := Trio
  Respect := Unit
  InAct := optIn
  MoreIn := optOver
  CausesIn := optNoCause
  selected := ()
  value := optLow
  Maxime := fun _ => True

def greatestMaximal.omit_hMore : Prop :=
  MaximumInGenusCausesAllInGenusReading optIn optOver optNoCause ∧
  ¬ MoreSuchHasThePerfectionReading optIn optOver ∧
  StrictDegreeCalibration optFrame ∧
  ¬ GreatestDegreeCausesAllInGenusReading optIn optNoCause () optLow

def greatestMaximal.omit_hCal : Prop :=
  MaximumInGenusCausesAllInGenusReading all down fromFalse ∧
  MoreSuchHasThePerfectionReading all down ∧
  ¬ StrictDegreeCalibration (boolFrame Nat all down fromFalse zero) ∧
  ¬ GreatestDegreeCausesAllInGenusReading all fromFalse () zero

/-! ### maximumInGenusFromGreatestEveryGenus -/

def maximumEvery.omit_hGreatest : Prop :=
  ¬ GreatestDegreeCausesAllInEveryGenus all noCause deg2 ∧
  DegreeExcessAmongBearersIsMoreIn all up deg2 ∧
  BearerDegreesDirectedInEveryGenus all deg2 ∧
  ¬ MaximumInGenusCausesAllInGenusReading all up noCause

def maximumEvery.omit_hExcess : Prop :=
  GreatestDegreeCausesAllInEveryGenus all fromTrue deg2 ∧
  ¬ DegreeExcessAmongBearersIsMoreIn all flat deg2 ∧
  BearerDegreesDirectedInEveryGenus all deg2 ∧
  ¬ MaximumInGenusCausesAllInGenusReading all flat fromTrue

def maximumEvery.omit_hDir : Prop :=
  GreatestDegreeCausesAllInEveryGenus all noCause (fun _ => incomparableValue) ∧
  DegreeExcessAmongBearersIsMoreIn all flat (fun _ => incomparableValue) ∧
  ¬ BearerDegreesDirectedInEveryGenus all (fun _ => incomparableValue) ∧
  ¬ MaximumInGenusCausesAllInGenusReading all flat noCause

/-! ### asToBeingSoToTruthFromIntelligibility

Respects are `Bool`: `false` is truth, `true` is being; the single thing is
`Unit`. Generated by `scripts/countermodel.py` (Fin carriers renamed). -/

def truthIntel.omit_hTruth : Prop :=
  ¬ TruthOfThingsIsIntelligibility (fun (_ : Unit) (_ : Bool) => False)
      (fun r _ _ => r = false) false true ∧
  IntelligibilityProportionedToBeing (fun (_ : Unit) (_ : Bool) => False)
      (fun r _ _ => r = false) true true ∧
  ¬ AsToBeingSoToTruthReading (fun (_ : Unit) (_ : Bool) => False)
      (fun r _ _ => r = false) false true

def truthIntel.omit_hBeing : Prop :=
  TruthOfThingsIsIntelligibility (fun (_ : Unit) (_ : Bool) => False)
      (fun r _ _ => r = true) false false ∧
  ¬ IntelligibilityProportionedToBeing (fun (_ : Unit) (_ : Bool) => False)
      (fun r _ _ => r = true) false true ∧
  ¬ AsToBeingSoToTruthReading (fun (_ : Unit) (_ : Bool) => False)
      (fun r _ _ => r = true) false true

/-! ### approachToPrimaryFromDegreeMeasure -/

def approach.omit_hCal : Prop :=
  ¬ MoreInMatchesDegreeEverywhere down () val2 ∧ AsMuchAsItApproaches val2 val2 ∧
  StrictPrimacyReading val2 true ∧ MoreSuchHasThePerfectionReading all down ∧
  GradesFoundInBeing down () ∧ ¬ ApproachToPrimaryReading all down () val2 true

def approach.omit_hMeasure : Prop :=
  MoreInMatchesDegreeEverywhere down () valRev ∧ ¬ AsMuchAsItApproaches valRev val2 ∧
  StrictPrimacyReading val2 true ∧ MoreSuchHasThePerfectionReading all down ∧
  GradesFoundInBeing down () ∧ ¬ ApproachToPrimaryReading all down () val2 true

def approach.omit_hStrict : Prop :=
  MoreInMatchesDegreeEverywhere up () val2 ∧ AsMuchAsItApproaches val2 val2 ∧
  ¬ StrictPrimacyReading val2 false ∧ MoreSuchHasThePerfectionReading onlyTrue up ∧
  GradesFoundInBeing up () ∧ ¬ ApproachToPrimaryReading onlyTrue up () val2 false

def approach.omit_hMore : Prop :=
  MoreInMatchesDegreeEverywhere up () val2 ∧ AsMuchAsItApproaches val2 val2 ∧
  StrictPrimacyReading val2 true ∧ ¬ MoreSuchHasThePerfectionReading none' up ∧
  GradesFoundInBeing up () ∧ ¬ ApproachToPrimaryReading none' up () val2 true

/-- A single being: strict primacy holds vacuously and nothing is compared. -/
def approach.omit_hGrades : Prop :=
  MoreInMatchesDegreeEverywhere (fun (_ : Unit) (_ _ : Unit) => False) () (fun _ => (0 : Nat)) ∧
  AsMuchAsItApproaches (fun (_ : Unit) => (0 : Nat)) (fun _ => (0 : Nat)) ∧
  StrictPrimacyReading (fun (_ : Unit) => (0 : Nat)) () ∧
  MoreSuchHasThePerfectionReading (fun (_ : Unit) (_ : Unit) => False)
    (fun (_ : Unit) (_ _ : Unit) => False) ∧
  ¬ GradesFoundInBeing (fun (_ : Unit) (_ _ : Unit) => False) () ∧
  ¬ ApproachToPrimaryReading (fun (_ : Unit) (_ : Unit) => False)
    (fun (_ : Unit) (_ _ : Unit) => False) () (fun _ => (0 : Nat)) ()

/-! ### Joint nonvacuity witness

`true` is God, the primary, the greatest and maximal being and the cause of the
perfection in `false`, a creature; `true` is more such than `false`. One
respect `()` serves as truth, being and intelligibility (so the truth premises
hold trivially here; their omission models above use distinct respects). -/

abbrev witnessFrame : Frame Nat := boolFrame Nat all up fromTrue val2

def witness : Prop :=
  MoreInExceedsDegree up deg2 ∧ NoDegreeBelowNull deg2 0 ∧
  AboveNullDegreeHasThePerfection all deg2 0 ∧ MoreSuchHasThePerfectionReading all up ∧
  NoInfiniteAscentInBeing up () ∧ GradesToMaximumAtBeing all up () ∧
  ApproachToPrimaryReading all up () val2 true ∧ StrictPrimacyReading val2 true ∧
  GodIsThePrimaryOfBeing isTrue' true ∧ GodIsMaximalInBeing isTrue' all up () ∧
  AsMuchAsItApproaches val2 val2 ∧ StrictDegreeCalibration witnessFrame ∧
  BearerDegreesComparable witnessFrame ∧ SomeBearerHasGreatestDegree witnessFrame ∧
  DirectedBearers witnessFrame ∧
  OrderedToPrimaryAsCauseReading all fromTrue isFalse' () true ∧
  OthersAreCreaturesReading isFalse' true ∧
  GreatestDegreeCausesAllInGenusReading all fromTrue () val2 ∧
  MaximumInGenusCausesAllInGenusReading all up fromTrue ∧
  DegreeExcessAmongBearersIsMoreIn all up deg2 ∧
  BearerDegreesDirectedInEveryGenus all deg2 ∧
  GreatestDegreeCausesAllInEveryGenus all fromTrue deg2 ∧
  TruthOfThingsIsIntelligibility all up () () ∧
  IntelligibilityProportionedToBeing all up () () ∧
  AsToBeingSoToTruthReading all up () () ∧
  MoreInMatchesDegreeEverywhere up () val2 ∧ GradesFoundInBeing up ()

/-- The batch controls: one omission model per premise of each derivation
(excluded middle excepted) and one joint nonvacuity witness. -/
def Certificate : Prop :=
  moreSuch.omit_hExceed ∧ moreSuch.omit_hNull ∧ moreSuch.omit_hPos ∧
  gradesAscent.omit_hWF ∧ gradesAscent.omit_hMore ∧
  gradesApproach.omit_hApproach ∧ gradesApproach.omit_hStrict ∧
  godPrimary.omit_hPrimary ∧ godPrimary.omit_hApproach ∧ godPrimary.omit_hStrict ∧
  calibration.omit_hApproach ∧ calibration.omit_hMeasure ∧
  directed.omit_hComp ∧ directed.omit_hTop ∧
  greatestOrdered.omit_hApproach ∧ greatestOrdered.omit_hStrict ∧
  greatestOrdered.omit_hOrdered ∧ greatestOrdered.omit_hOthers ∧
  greatestMaximal.omit_hMax ∧ greatestMaximal.omit_hMore ∧ greatestMaximal.omit_hCal ∧
  maximumEvery.omit_hGreatest ∧ maximumEvery.omit_hExcess ∧ maximumEvery.omit_hDir ∧
  truthIntel.omit_hTruth ∧ truthIntel.omit_hBeing ∧
  approach.omit_hCal ∧ approach.omit_hMeasure ∧ approach.omit_hStrict ∧
  approach.omit_hMore ∧ approach.omit_hGrades ∧
  witness

end Control

end TruthCore.Causality.Round3FourthWay
