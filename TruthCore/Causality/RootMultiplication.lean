import TruthCore.Causality.ConstitutiveNatureUniqueness
import TruthCore.Logic.ExcludedMiddle

/-! #697: what remains of the two-root rival after the existing first-mover
premises, and one proposed bridge excluding it. Source-free stipulative vocabulary:
nothing here is attributed to any author, is a definition of God, or settles
whether the represented relations are real. First movers only; applicability to
a selected necessary or underived individual is not addressed. -/
namespace TruthCore.Causality.RootMultiplication
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.ConstitutiveNatureUniqueness

variable {B P R : Type}

/-- `x` and `y` agree on the supplied act predicate in every supplied respect. -/
def SameActProfile (InAct : B → R → Prop) (x y : B) : Prop :=
  ∀ r, InAct x r ↔ InAct y r

/-- First movers with one act profile have one represented nature. Strictly
weaker than `ConstitutiveContentComplete` with `FirstMoverContentAgreesWithAct`;
it names no content assignment. -/
def FirstMoverActDeterminesNature
    (Moved : B → R → Prop) (Moves : B → B → R → Prop) (InAct : B → R → Prop)
    (essence : B → P) : Prop :=
  ∀ f g, IsFirstUnmovedMover Moved Moves f → IsFirstUnmovedMover Moved Moves g →
    SameActProfile InAct f g → essence f = essence g

/-- Any two first movers have one represented nature. -/
def FirstMoversShareNature
    (Moved : B → R → Prop) (Moves : B → B → R → Prop) (essence : B → P) : Prop :=
  ∀ f g, IsFirstUnmovedMover Moved Moves f → IsFirstUnmovedMover Moved Moves g →
    essence f = essence g

/-- Under individuation, the first-mover suppositum/nature adapter and
every-perfection: distinct first movers have one act profile and different
represented natures, and at-most-one is equivalent to each of the two preceding
nature conditions. Supplies no first mover. -/
def PluralityResidue
    (Moved : B → R → Prop) (Moves : B → B → R → Prop) (InAct : B → R → Prop)
    (essence : B → P) : Prop :=
  (∀ f g, IsFirstUnmovedMover Moved Moves f → IsFirstUnmovedMover Moved Moves g →
    f ≠ g → SameActProfile InAct f g ∧ essence f ≠ essence g) ∧
  (AtMostOneFirstUnmovedMover Moved Moves ↔
    FirstMoverActDeterminesNature Moved Moves InAct essence) ∧
  (AtMostOneFirstUnmovedMover Moved Moves ↔
    FirstMoversShareNature Moved Moves essence)

/-- `x` is composite, or its esse is other than its essence, or some other being
is simply prior to it. Exactly these three represented disjuncts: a whole
essence differing from another whole essence is none of them by itself. -/
def HasLimitingPrinciple
    (Composite : B → Prop) (Prior : B → B → Prop) (essence esse : B → P) (x : B) : Prop :=
  Composite x ∨ esse x ≠ essence x ∨ ∃ y, y ≠ x ∧ Prior y x

/-- OPEN bridge: any two beings without a limiting principle have one represented
nature. It ranges over all beings, not first movers, and is vacuous at every pair
with a limited member. -/
def UnlimitedBeingsShareNature
    (Composite : B → Prop) (Prior : B → B → Prop) (essence esse : B → P) : Prop :=
  ∀ x y, ¬ HasLimitingPrinciple Composite Prior essence esse x →
    ¬ HasLimitingPrinciple Composite Prior essence esse y → essence x = essence y

namespace Control
open TruthCore.Causality.PartFreePlurality
abbrev JB := TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.B
abbrev firstMover := IsFirstUnmovedMover moved moves
abbrev atMostOne := AtMostOneFirstUnmovedMover moved moves
abbrev limited := HasLimitingPrinciple composite prior essence esse

/-- One constant represented nature and esse on the part-free carrier. -/
def constant : Being → Being := fun _ => .left

/-- The unchanged part-free model keeps its joint certificate and its #715
content controls. It fails the bridge and act-determines-nature, and its only
beings without a limiting principle are the two roots. No field is altered. -/
def SurvivingRival : Prop :=
  TruthCore.Causality.ConstitutiveNatureUniqueness.Control.Certificate ∧
  ¬ FirstMoverActDeterminesNature moved moves inAct essence ∧
  ¬ UnlimitedBeingsShareNature composite prior essence esse ∧
  (∀ x, ¬ limited x ↔ root x)

/-- For the five hypotheses of the bridge's uniqueness theorem, each omission
retains the other four on the part-free motion tables and fails at-most-one.
The bridge omission is `SurvivingRival`; the other four vary the stated
parameters only, so they need not preserve the full joint model. -/
def OmissionControls : Prop :=
  -- individuation omitted: constant suppositum, nature and esse
  (¬ IndividuatingBasisIsIncommunicableReading constant ∧
    FirstMoverSuppositumIsNature moved moves constant constant ∧
    FirstUnmovedMoverIsSimpleReading moved moves body matterForm composite constant constant ∧
    FirstUnmovedMoverIsFirstBeing moved moves prior ∧
    UnlimitedBeingsShareNature composite prior constant constant ∧ ¬ atMostOne) ∧
  -- adapter omitted: identity suppositum, constant nature and esse
  (IndividuatingBasisIsIncommunicableReading suppositum ∧
    ¬ FirstMoverSuppositumIsNature moved moves suppositum constant ∧
    FirstUnmovedMoverIsSimpleReading moved moves body matterForm composite constant constant ∧
    FirstUnmovedMoverIsFirstBeing moved moves prior ∧
    UnlimitedBeingsShareNature composite prior constant constant ∧ ¬ atMostOne) ∧
  -- simplicity omitted: every being counts as composite
  (IndividuatingBasisIsIncommunicableReading suppositum ∧
    FirstMoverSuppositumIsNature moved moves suppositum essence ∧
    ¬ FirstUnmovedMoverIsSimpleReading moved moves body matterForm (fun _ => True) essence esse ∧
    FirstUnmovedMoverIsFirstBeing moved moves prior ∧
    UnlimitedBeingsShareNature (fun _ => True) prior essence esse ∧ ¬ atMostOne) ∧
  -- first-being omitted: every other being counts as prior
  (IndividuatingBasisIsIncommunicableReading suppositum ∧
    FirstMoverSuppositumIsNature moved moves suppositum essence ∧
    FirstUnmovedMoverIsSimpleReading moved moves body matterForm composite essence esse ∧
    ¬ FirstUnmovedMoverIsFirstBeing moved moves (fun y x => y ≠ x) ∧
    UnlimitedBeingsShareNature composite (fun y x => y ≠ x) essence esse ∧ ¬ atMostOne)

/-- The act table with `right` lacking `heat`, reusing the #715 code. -/
abbrev partialAct := TruthCore.Causality.ConstitutiveNatureUniqueness.Control.separatingContent

/-- The three horns of the coverage clause are each witnessed by the two part-free
first movers under a stated assignment: differing act, one nature, two natures. -/
def HornWitnesses : Prop :=
  firstMover .left ∧ firstMover .right ∧ Being.left ≠ Being.right ∧
  ¬ SameActProfile partialAct Being.left .right ∧
  (SameActProfile inAct Being.left .right ∧ constant .left = constant .right) ∧
  (SameActProfile inAct Being.left .right ∧ essence .left ≠ essence .right)

/-- Coverage, given excluded middle as an explicit hypothesis. -/
def ForkCoverage : Prop :=
  ∀ {B P R : Type} (InAct : B → R → Prop) (essence : B → P) (f g : B),
    TruthCore.Logic.ExcludedMiddle →
    ¬ SameActProfile InAct f g ∨
      (SameActProfile InAct f g ∧ essence f = essence g) ∨
      (SameActProfile InAct f g ∧ essence f ≠ essence g)

/-- The #715 content bundle yields act-determines-nature, and the converse fails:
with two first movers differing in act and one constant nature, act-determines-
nature holds and no content whatever agrees with that act table. -/
def ContentBundleStrict : Prop :=
  (∀ {B P R : Type} (Moved : B → R → Prop) (Moves : B → B → R → Prop)
      (InAct : B → R → Prop) (essence : B → P) (content : P → R → Prop),
    ConstitutiveContentComplete content →
    FirstMoverContentAgreesWithAct Moved Moves InAct essence content →
    FirstMoverActDeterminesNature Moved Moves InAct essence) ∧
  FirstMoverActDeterminesNature moved moves partialAct constant ∧
  ∀ content : Being → Respect → Prop,
    ¬ FirstMoverContentAgreesWithAct moved moves partialAct constant content

open TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint (movedIn movesIn) in
/-- Priority on the existing `OneFirstMover.Joint` carrier: only `g` precedes, and
exactly the listed beings follow it. -/
def jointPrior (p a : JB) : Prop := p = (.g : JB) ∧ (a = (.f : JB) ∨ a = (.x : JB))

open TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint (movedIn movesIn) in
/-- Independence from at-most-one in the remaining direction: on the single-mover
carrier, individuation, the adapter, simplicity and first-being hold with
at-most-one and an actual first mover, while `c`, unlimited and no first mover,
has a nature other than `g`'s, so the bridge fails. The bridge is strictly
stronger than first-mover uniqueness under these four. Body, matter/form and
composite are constant-false new assignments, not the carrier's original
commentary; `c` is an inert test row, not an attributed kind of being. -/
def BridgeExceedsUniqueness : Prop :=
  IndividuatingBasisIsIncommunicableReading (fun a : JB => a) ∧
  FirstMoverSuppositumIsNature movedIn movesIn (fun a : JB => a) (fun a => a) ∧
  FirstUnmovedMoverIsSimpleReading movedIn movesIn (fun _ => False) (fun _ => False)
    (fun _ => False) (fun a : JB => a) (fun a => a) ∧
  FirstUnmovedMoverIsFirstBeing movedIn movesIn jointPrior ∧
  AtMostOneFirstUnmovedMover movedIn movesIn ∧
  IsFirstUnmovedMover movedIn movesIn (.g : JB) ∧
  ¬ IsFirstUnmovedMover movedIn movesIn (.c : JB) ∧
  ¬ HasLimitingPrinciple (fun _ => False) jointPrior (fun a : JB => a) (fun a => a) (.c : JB) ∧
  ¬ UnlimitedBeingsShareNature (fun _ => False) jointPrior (fun a : JB => a) (fun a => a)

open TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint (movedIn movesIn) in
/-- Priority where `g` precedes every other being, so only `g` is unlimited. -/
def fullPrior (p a : JB) : Prop := p = (.g : JB) ∧ a ≠ (.g : JB)

open TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint (movedIn movesIn) in
/-- Nonvacuity: all five hypotheses of the bridge's uniqueness theorem hold on the
single-mover carrier with an actual first mover. -/
def PositiveWitness : Prop :=
  IndividuatingBasisIsIncommunicableReading (fun a : JB => a) ∧
  FirstMoverSuppositumIsNature movedIn movesIn (fun a : JB => a) (fun a => a) ∧
  FirstUnmovedMoverIsSimpleReading movedIn movesIn (fun _ => False) (fun _ => False)
    (fun _ => False) (fun a : JB => a) (fun a => a) ∧
  FirstUnmovedMoverIsFirstBeing movedIn movesIn fullPrior ∧
  UnlimitedBeingsShareNature (fun _ => False) fullPrior (fun a : JB => a) (fun a => a) ∧
  IsFirstUnmovedMover movedIn movesIn (.g : JB)

/-- Finite interpretations only: satisfiability of the encoded bundles, not
metaphysical possibility. -/
def Certificate : Prop :=
  SurvivingRival ∧ OmissionControls ∧ HornWitnesses ∧ ForkCoverage ∧
  ContentBundleStrict ∧ BridgeExceedsUniqueness ∧ PositiveWitness

end Control
end TruthCore.Causality.RootMultiplication
