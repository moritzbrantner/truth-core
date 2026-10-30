import Mathlib.Logic.Relation
import TruthCore.Causality.NecessarilyUnderived
import TruthCore.Greek.Aristotle.Categories
import TruthCore.Logic.CogitoConcrete

/-!
# Does the support ancestry of a thought's bearer terminate? (#562)

Source-free analyst investigation. Nothing here shows that a thought occurs,
that any premise is true, or that any branch is metaphysically possible.

Relations kept apart (`DISAMB-BEARS-INHERES-SUPPORTS`):

* `Bears b e` (#532): `b` is the bearer of the thought episode `e`;
* `R w c x`, read through `PresentEsseSupport` (#495): `c` exists at `w` and is
  a direct existential supporter of `x` at `w`;
* Aristotle's `In` and `SaidOf`, supplied primitive relations of the *Categories*
  reading; they are linked to `R` only by the open bridges below.

No model or theorem identifies these relations. The bearer enters the support
order only as the start of the ancestry: the episode is not in that ancestry
unless a model separately puts it there. A bearer of a bearer is never used.

`Dependent` and `Substance` are unconstrained supplied predicates. `Dependent`
is not defined as having a supporter, so `BearerAncestryDependentsSupported`
can fail. The `¬ Dependent` clause of a terminus is only the contraposition of
that premise at a point with no existing supporter.

Coverage is `someBearerOutcome`. It uses excluded middle as an explicit
hypothesis, so its case split on accessibility is classical. Its nonterminating
branches have positive content (a cycle, or a nonempty ancestor set in which
each member has an existing supporter in the set), but it adds nothing to
`Acc ∨ ¬ Acc` about which case holds. Exclusivity is treated separately:
`OutcomeExclusions` proves the exclusions that hold and `BothTerminiModel` shows
that the two terminus branches can hold together. A "non-substantial terminus"
is only a terminus failing the supplied `Substance`; it is not shown to be a
process or event.
-/
namespace TruthCore.Causality.BearerRegress

open TruthCore.Causality.NecessarilyUnderived
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt)
open TruthCore.Greek.Aristotle.Categories (PrimarySubstanceBySubjectRelationsReading)
open TruthCore.Logic.CogitoSubject
open TruthCore.Logic.CogitoConcrete

variable {W B Episode : Type}

/-- `x` is `b` or reached from `b` by a finite chain of existing direct
supporters at `w`. Mathlib's reflexive-transitive closure (invariant 14). -/
def SupportAncestor (m : Ontic W B) (R : W → B → B → Prop) (w : W) (x b : B) : Prop :=
  Relation.ReflTransGen (PresentEsseSupport m R w) x b

/-- Every existing support-ancestor of a bearer of an occurring thought
(the bearer included) that satisfies `Dependent` has an existing direct
supporter at `w`. Open and unattributed. Silent about entities outside these
ancestries, and it does not say that an ancestor is dependent. -/
def BearerAncestryDependentsSupported (m : Ontic W B) (R : W → B → B → Prop)
    (Dependent : B → Prop) (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (w : W) : Prop :=
  ∀ b e x, Occurs e → Bears b e → SupportAncestor m R w x b → m.ExistsAt w x →
    Dependent x → ∃ c, PresentEsseSupport m R w c x

/-- `x` is a terminus of `b`'s ancestry: an existing ancestor with no existing
direct supporter at `w`, failing `Dependent`. A root of `R` at `w` only:
nothing is said of other worlds or of relations other than `R`. -/
def SupportTerminus (m : Ontic W B) (R : W → B → B → Prop) (Dependent : B → Prop)
    (w : W) (b x : B) : Prop :=
  SupportAncestor m R w x b ∧ m.ExistsAt w x ∧ NoExistingSupportAt m R w x ∧ ¬ Dependent x

/-- Every support chain descending from `b` is finite in Lean's inductive sense,
and some terminus satisfies `Substance`. Other termini may fail it. -/
def SubstantialTerminusBelow (m : Ontic W B) (R : W → B → B → Prop)
    (Dependent Substance : B → Prop) (w : W) (b : B) : Prop :=
  Acc (PresentEsseSupport m R w) b ∧ ∃ x, SupportTerminus m R Dependent w b x ∧ Substance x

/-- Every support chain descending from `b` is finite in Lean's inductive sense,
and some terminus fails `Substance`. Other termini may satisfy it. -/
def NonSubstantialTerminusBelow (m : Ontic W B) (R : W → B → B → Prop)
    (Dependent Substance : B → Prop) (w : W) (b : B) : Prop :=
  Acc (PresentEsseSupport m R w) b ∧ ∃ x, SupportTerminus m R Dependent w b x ∧ ¬ Substance x

/-- Some ancestor of `b` is a proper support-ancestor of itself: a chain of one
or more edges returns to it (a self-edge counts). -/
def SupportCycleBelow (m : Ontic W B) (R : W → B → B → Prop) (w : W) (b : B) : Prop :=
  ∃ x, SupportAncestor m R w x b ∧ Relation.TransGen (PresentEsseSupport m R w) x x

/-- Some set of ancestors of `b` contains `b`, and each member has an existing
direct supporter in the set. A cycle gives a finite such set. The set form avoids
the choice principle needed to extract a sequence. -/
def EndlessSupportBelow (m : Ontic W B) (R : W → B → B → Prop) (w : W) (b : B) : Prop :=
  ∃ S : B → Prop, S b ∧ ∀ x, S x →
    SupportAncestor m R w x b ∧ ∃ y, S y ∧ PresentEsseSupport m R w y x

/-- An endless ancestor set with no cycle among `b`'s ancestors. -/
def AcyclicEndlessSupportBelow (m : Ontic W B) (R : W → B → B → Prop) (w : W) (b : B) : Prop :=
  EndlessSupportBelow m R w b ∧ ¬ SupportCycleBelow m R w b

/-- The four outcome forms for one bearer. -/
def BearerOutcome (m : Ontic W B) (R : W → B → B → Prop) (Dependent Substance : B → Prop)
    (w : W) (b : B) : Prop :=
  SubstantialTerminusBelow m R Dependent Substance w b ∨
    NonSubstantialTerminusBelow m R Dependent Substance w b ∨
      SupportCycleBelow m R w b ∨
        AcyclicEndlessSupportBelow m R w b

/-- Some bearer of an occurring thought has one of the four outcome forms. -/
def SomeBearerOutcome (m : Ontic W B) (R : W → B → B → Prop) (Dependent Substance : B → Prop)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (w : W) : Prop :=
  ∃ b e, Occurs e ∧ Bears b e ∧ BearerOutcome m R Dependent Substance w b

/-- Open and unattributed: for an existing `x`, if `x` is in `y` (the supplied
*Categories* relation), then `y` exists and directly supports `x` at `w`.
*Categories* I.2 speaks of inability to exist apart from what something is in;
a direct existing supporter is stronger than that. -/
def InSubjectIsExistentSupport (m : Ontic W B) (R : W → B → B → Prop)
    (In : B → B → Prop) (w : W) : Prop :=
  ∀ x y, m.ExistsAt w x → In x y → m.ExistsAt w y ∧ R w y x

/-- Open and unattributed: for an existing `x`, if `x` is said of `y` (the
supplied *Categories* relation), then `y` exists and directly supports `x` at
`w`. Independent of `InSubjectIsExistentSupport`. -/
def SaidOfSubjectIsExistentSupport (m : Ontic W B) (R : W → B → B → Prop)
    (SaidOf : B → B → Prop) (w : W) : Prop :=
  ∀ x y, m.ExistsAt w x → SaidOf x y → m.ExistsAt w y ∧ R w y x

/-- Some bearer of an occurring thought has a terminus that satisfies the
supplied primary-substance predicate. -/
def PrimarySubstanceTerminusOfBearer (m : Ontic W B) (R : W → B → B → Prop)
    (Dependent IsPrimarySubstance : B → Prop) (Occurs : Episode → Prop)
    (Bears : B → Episode → Prop) (w : W) : Prop :=
  ∃ b e x, Occurs e ∧ Bears b e ∧ SupportTerminus m R Dependent w b x ∧ IsPrimarySubstance x

/-! ## Controls -/

/-- The premises shared by the controls: a thought occurs, every occurring
thought has a bearer, every such bearer exists at `w`, and the ancestry premise. -/
def Base (m : Ontic W B) (R : W → B → B → Prop) (Dependent : B → Prop)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (w : W) : Prop :=
  ThoughtOccurs Occurs ∧ EveryThoughtHasSubject Occurs Bears ∧
    EveryBearerExistsAt m Occurs Bears w ∧
      BearerAncestryDependentsSupported m R Dependent Occurs Bears w

/-- One world; every candidate of the carrier exists there. `Causes` is unused. -/
def oneWorld (B : Type) : Ontic Unit B where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := fun _ _ _ => False

/-- A model of the `Base` premises and the well-foundedness premise in which
a terminus of the bearer satisfies `Substance` and none fails it. -/
def SubstanceBranchModel : Prop :=
  let m := oneWorld Unit
  let R : Unit → Unit → Unit → Prop := fun _ _ _ => False
  let Bears : Unit → Unit → Prop := fun _ _ => True
  Base m R (fun _ => False) (fun _ : Unit => True) Bears () ∧
    WellFoundedPresentEsseSupport m R () ∧
    SubstantialTerminusBelow m R (fun _ => False) (fun _ => True) () () ∧
    ¬ NonSubstantialTerminusBelow m R (fun _ => False) (fun _ => True) () ()

/-- Support on `Bool` is empty. The episode `true` is borne by `false`. -/
def eventBears (b e : Bool) : Prop := b = false ∧ e = true

/-- The well-founded non-substantial terminus: `Base` and well-foundedness hold,
the bearer's terminus fails `Substance`, and nothing bears that bearer. The
episode `true` lies in the same carrier, has an existing bearer and has no
existing supporter, so bearing yields no support edge here. Satisfiability of
the formula only; nothing marks the terminus as an event or process. -/
def NonSubstanceBranchModel : Prop :=
  let m := oneWorld Bool
  let R : Unit → Bool → Bool → Prop := fun _ _ _ => False
  Base m R (fun _ => False) (fun e : Bool => e = true) eventBears () ∧
    WellFoundedPresentEsseSupport m R () ∧
    NonSubstantialTerminusBelow m R (fun _ => False) (fun _ => False) () false ∧
    ¬ SubstantialTerminusBelow m R (fun _ => False) (fun _ => False) () false ∧
    (¬ ∃ b, eventBears b false) ∧
    eventBears false true ∧ NoExistingSupportAt m R () true

/-- Two entities support each other. -/
def cycleSupport (_ : Unit) (c b : Bool) : Prop := c ≠ b

/-- The two-node cycle: `Base` holds with every entity dependent; a cycle lies
below the bearer, support is not well-founded and there is no terminus. -/
def CycleBranchModel : Prop :=
  let m := oneWorld Bool
  Base m cycleSupport (fun _ => True) (fun _ : Unit => True) (fun b _ => b = false) () ∧
    SupportCycleBelow m cycleSupport () false ∧
    ¬ WellFoundedPresentEsseSupport m cycleSupport () ∧
    ¬ ∃ x, SupportTerminus m cycleSupport (fun _ => True) () false x

/-- `n + 1` directly supports `n`. -/
def chainSupport (_ : Unit) (c b : Nat) : Prop := c = b + 1

/-- The infinite chain: `Base` holds with every entity dependent; the bearer `0`
has an acyclic endless ancestry and no terminus. -/
def ChainBranchModel : Prop :=
  let m := oneWorld Nat
  Base m chainSupport (fun _ => True) (fun _ : Unit => True) (fun b _ => b = 0) () ∧
    AcyclicEndlessSupportBelow m chainSupport () 0 ∧
    ¬ WellFoundedPresentEsseSupport m chainSupport () ∧
    ¬ ∃ x, SupportTerminus m chainSupport (fun _ => True) () 0 x

/-- A thought, its bundle bearer and two members of the bundle. -/
inductive BundleNode where
  | thought | bundle | left | right

/-- Each member supports the bundle and the other member. -/
def bundleSupport (_ : Unit) : BundleNode → BundleNode → Prop
  | .left, .bundle | .right, .bundle | .left, .right | .right, .left => True
  | _, _ => False

/-- The bundle bears the thought only. -/
def bundleBears (b e : BundleNode) : Prop := b = .bundle ∧ e = .thought

/-- The bundle case: mutual support among members lies below the bearer, the
bundle is on no cycle, and nothing bears the bundle. So a support cycle below
a bearer is here no regress of bearers. -/
def BundleCycleModel : Prop :=
  let m := oneWorld BundleNode
  Base m bundleSupport (fun x => x = .bundle ∨ x = .left ∨ x = .right)
      (fun e : BundleNode => e = .thought) bundleBears () ∧
    SupportCycleBelow m bundleSupport () .bundle ∧
    ¬ Relation.TransGen (PresentEsseSupport m bundleSupport ()) .bundle .bundle ∧
    ¬ ∃ b, bundleBears b .bundle

/-- A bearer with two unsupported supporters. -/
def rootsSupport (_ : Unit) (c b : Fin 3) : Prop := b = 0 ∧ c ≠ 0

/-- Non-exclusivity of the terminus branches: one bearer, with `Base` and
well-foundedness, has a terminus satisfying `Substance` and one failing it. -/
def BothTerminiModel : Prop :=
  let m := oneWorld (Fin 3)
  let Dep : Fin 3 → Prop := fun x => x = 0
  let Sub : Fin 3 → Prop := fun x => x = 1
  Base m rootsSupport Dep (fun _ : Unit => True) (fun b _ => b = 0) () ∧
    WellFoundedPresentEsseSupport m rootsSupport () ∧
    SubstantialTerminusBelow m rootsSupport Dep Sub () 0 ∧
    NonSubstantialTerminusBelow m rootsSupport Dep Sub () 0

/-- `1` supports `0`; `2` supports `0` and itself. -/
def mixedSupport (_ : Unit) (c b : Fin 3) : Prop :=
  (c = 1 ∧ b = 0) ∨ (c = 2 ∧ (b = 0 ∨ b = 2))

/-- Having a terminus does not exclude regress: under `Base` one bearer has a
terminus and also a support cycle below it. -/
def TerminusWithCycleModel : Prop :=
  let m := oneWorld (Fin 3)
  let Dep : Fin 3 → Prop := fun x => x ≠ 1
  Base m mixedSupport Dep (fun _ : Unit => True) (fun b _ => b = 0) () ∧
    (∃ x, SupportTerminus m mixedSupport Dep () 0 x) ∧
    SupportCycleBelow m mixedSupport () 0

/-- Omitting the ancestry premise: support is empty, hence well-founded, a
thought occurs with an existing bearer, the bearer is dependent, and no terminus
in the `¬ Dependent` sense exists. -/
def OmitAncestryPremiseModel : Prop :=
  let m := oneWorld Unit
  let R : Unit → Unit → Unit → Prop := fun _ _ _ => False
  ThoughtOccurs (fun _ : Unit => True) ∧
    EveryThoughtHasSubject (fun _ : Unit => True) (fun (_ : Unit) _ => True) ∧
    EveryBearerExistsAt m (fun _ : Unit => True) (fun (_ : Unit) _ => True) () ∧
    WellFoundedPresentEsseSupport m R () ∧
    ¬ BearerAncestryDependentsSupported m R (fun _ => True)
        (fun _ : Unit => True) (fun (_ : Unit) _ => True) () ∧
    ¬ ∃ x, SupportTerminus m R (fun _ => True) () () x

/-- Two mutually accessible worlds; the one candidate exists only at `false`. -/
def contingentOntic : Ontic Bool Unit where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun w _ => w = false
  Causes := fun _ _ _ => False

/-- No modal conclusion: under `Base` and well-foundedness at `false`, the
terminus satisfying `Substance` is contingent and not necessary at `false`. -/
def ContingentTerminusModel : Prop :=
  let m := contingentOntic
  let R : Bool → Unit → Unit → Prop := fun _ _ _ => False
  Base m R (fun _ => False) (fun _ : Unit => True) (fun _ _ => True) false ∧
    WellFoundedPresentEsseSupport m R false ∧
    SubstantialTerminusBelow m R (fun _ => False) (fun _ => True) false () ∧
    ContingentAt m false () ∧ ¬ NecessaryAt m false ()

/-- `false` is in `true`, and nothing is said of anything. -/
def omitIn (x y : Bool) : Prop := x = false ∧ y = true

/-- Omitting `InSubjectIsExistentSupport`: every other premise of the
primary-substance theorem holds, and no terminus of the bearer `false` passes
the *Categories* test, because that terminus is in something that does not
support it. -/
def OmitInBridgeModel : Prop :=
  let m := oneWorld Bool
  let R : Unit → Bool → Bool → Prop := fun _ _ _ => False
  let Dep : Bool → Prop := fun _ => False
  let SaidOf : Bool → Bool → Prop := fun _ _ => False
  let IsPS : Bool → Prop := fun x => x = true
  Base m R Dep (fun _ : Unit => True) (fun b _ => b = false) () ∧
    WellFoundedPresentEsseSupport m R () ∧
    PrimarySubstanceBySubjectRelationsReading IsPS SaidOf omitIn ∧
    SaidOfSubjectIsExistentSupport m R SaidOf () ∧
    ¬ InSubjectIsExistentSupport m R omitIn () ∧
    ¬ PrimarySubstanceTerminusOfBearer m R Dep IsPS (fun _ : Unit => True)
        (fun b _ => b = false) ()

/-- `false` is said of `true`, and nothing is in anything. -/
def omitSaidOf (x y : Bool) : Prop := x = false ∧ y = true

/-- Omitting `SaidOfSubjectIsExistentSupport`: every other premise of the
primary-substance theorem holds, and no terminus of the bearer `false` passes
the *Categories* test. -/
def OmitSaidOfBridgeModel : Prop :=
  let m := oneWorld Bool
  let R : Unit → Bool → Bool → Prop := fun _ _ _ => False
  let Dep : Bool → Prop := fun _ => False
  let In : Bool → Bool → Prop := fun _ _ => False
  let IsPS : Bool → Prop := fun x => x = true
  Base m R Dep (fun _ : Unit => True) (fun b _ => b = false) () ∧
    WellFoundedPresentEsseSupport m R () ∧
    PrimarySubstanceBySubjectRelationsReading IsPS omitSaidOf In ∧
    InSubjectIsExistentSupport m R In () ∧
    ¬ SaidOfSubjectIsExistentSupport m R omitSaidOf () ∧
    ¬ PrimarySubstanceTerminusOfBearer m R Dep IsPS (fun _ : Unit => True)
        (fun b _ => b = false) ()

/-- The negative test does not settle the supplied kind: all premises of the
primary-substance theorem hold and the terminus passes the *Categories* test
because nothing is in or said of anything, while it fails a separately supplied
`Substance`. So the theorem's conclusion gives no such `Substance` predicate,
and a kind-classifier rival is not refuted by that test. -/
def NegativeTestControl : Prop :=
  let m := oneWorld Unit
  let R : Unit → Unit → Unit → Prop := fun _ _ _ => False
  let Dep : Unit → Prop := fun _ => False
  let None₂ : Unit → Unit → Prop := fun _ _ => False
  let IsPS : Unit → Prop := fun _ => True
  Base m R Dep (fun _ : Unit => True) (fun _ _ => True) () ∧
    WellFoundedPresentEsseSupport m R () ∧
    PrimarySubstanceBySubjectRelationsReading IsPS None₂ None₂ ∧
    InSubjectIsExistentSupport m R None₂ () ∧
    SaidOfSubjectIsExistentSupport m R None₂ () ∧
    PrimarySubstanceTerminusOfBearer m R Dep IsPS (fun _ : Unit => True) (fun _ _ => True) () ∧
    NonSubstantialTerminusBelow m R Dep (fun _ => False) () ()

/-- For every interpretation and bearer, each terminus branch excludes each
nonterminating branch. The cycle branch and the acyclic branch exclude each other
by the definition of the latter. `BothTerminiModel` shows the two terminus
branches are not exclusive of each other. -/
def OutcomeExclusions : Prop :=
  ∀ (W B : Type) (m : Ontic W B) (R : W → B → B → Prop) (Dependent Substance : B → Prop)
    (w : W) (b : B),
    (SubstantialTerminusBelow m R Dependent Substance w b ∨
        NonSubstantialTerminusBelow m R Dependent Substance w b) →
      ¬ (SupportCycleBelow m R w b ∨ AcyclicEndlessSupportBelow m R w b)

/-- The controls of this investigation, one conjunct each. Finite and infinite
logical models only, none of which includes excluded middle in its premises: no
premise is discharged and no model is claimed metaphysically possible. -/
def BearerRegressControls : Prop :=
  SubstanceBranchModel ∧ NonSubstanceBranchModel ∧ CycleBranchModel ∧ ChainBranchModel ∧
    BundleCycleModel ∧ BothTerminiModel ∧ TerminusWithCycleModel ∧
    OmitAncestryPremiseModel ∧ ContingentTerminusModel ∧ OmitInBridgeModel ∧
    OmitSaidOfBridgeModel ∧ NegativeTestControl ∧ OutcomeExclusions

end TruthCore.Causality.BearerRegress
