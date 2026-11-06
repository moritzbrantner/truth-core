module

public import TruthCore.Logic.ExcludedMiddle
public import TruthCore.Logic.CorrectionCriterion
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question5.Article1
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question5.UltimatePerfection
public import TruthCore.English.Boyd.MoralRealism
public import TruthCore.English.Railton.MoralRealism

/-!
# Goodness, due actuality, and rival accounts (#1116)

The owner's thesis is a proposition, not an adopted definition of `GoodIn`.
`DueActualityThesis` says that goodness in a respect coextends with actually
having a perfection due to the bearer's form and end. `GoodIn` and `Has` remain
independent parameters, and the thesis can fail. A form/end assignment supplies
an explicit standard of due perfection; it does not prove that the standard is
correct for reality, causally efficacious, or categorically reason-giving.

The exhaustive fork is by a shared question, not a list of historical schools:
coextension, some surplus good, or some omitted due actuality. The latter cells
may overlap. Excluding them is equivalent to the thesis in this profile; this
supplies no independent warrant for excluding them. Property identity remains
a stronger reading, so extensional agreement does not settle Moore's objection.

The finite controls use a knife and a counterweight. Both exist and have mass;
the knife lacks an edge. Edge is due to the cutter/cutting profile, mass to the
weight/balancing profile. This is a stipulated artifact illustration, not an
empirical or metaphysical possibility claim about natural kinds. The Boyd and
Railton comparisons instantiate their existing schemas on supplied aspect
ascriptions. This domain transfer is an analyst test, not an attribution that
moral goodness, personal welfare and ontological goodness are interchangeable.
-/

@[expose] public section

namespace TruthCore.Metaethics.GoodnessFormEnd

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic.CorrectionCriterion

/-- One fixed interpretation. `DueFor F E p` specifies which perfection p is
appropriate to form F relative to end E. No teleological causal law follows. -/
structure Frame where
  Being : Type
  Perfection : Type
  Form : Type
  End : Type
  Feature : Type
  form : Being → Form
  endOf : Form → End
  DueFor : Form → End → Perfection → Prop
  Has : Being → Perfection → Prop
  GoodIn : Being → Perfection → Prop
  feature : Being → Feature
  substantial : Perfection
  ultimate : Being → Perfection
  GoodSimply : Being → Prop

/-- Due relative to this bearer's supplied form/end standard. -/
def Due (f : Frame) (x : f.Being) (p : f.Perfection) : Prop :=
  f.DueFor (f.form x) (f.endOf (f.form x)) p

/-- Actually having a perfection appropriate under that supplied standard. -/
def DueActuality (f : Frame) (x : f.Being) (p : f.Perfection) : Prop :=
  Due f x p ∧ f.Has x p

/-- Owner's proposed proposition, in its extensional, per-perfection reading.
It is neither a definition of `GoodIn` nor a floor marking. -/
def DueActualityThesis (f : Frame) : Prop :=
  ∀ x p, f.GoodIn x p ↔ DueActuality f x p

/-- Some item is called good without possessing the appropriate due actuality.
This does not distinguish lack of actuality from lack of due status. -/
def SurplusGood (f : Frame) : Prop :=
  ∃ x p, f.GoodIn x p ∧ ¬ DueActuality f x p

/-- Some due actuality is omitted from goodness. -/
def OmittedDueGood (f : Frame) : Prop :=
  ∃ x p, DueActuality f x p ∧ ¬ f.GoodIn x p

/-- Coverage of the three extensional cells for every fixed profile. Cells are
not asserted exclusive, and are not named historical theories. -/
def DefinitionFork : Prop :=
  ∀ f : Frame, DueActualityThesis f ∨ SurplusGood f ∨ OmittedDueGood f

/-- Eliminating both failure cells entails the thesis; requires no choice of a
preferred historical theory. The decision principle is an explicit premise. -/
def FailureElimination : Prop :=
  ∀ f : Frame, ¬ SurplusGood f → ¬ OmittedDueGood f → DueActualityThesis f

/-- The exact extra condition needed to turn due coextension into unrestricted
q.5 per-perfection coextension. This is not silently assumed. -/
def AllActualitiesDue (f : Frame) : Prop := ∀ x p, f.Has x p → Due f x p

/-- Semantic presentations distinguish property identity from coextension.
Calibration fixes the denotation of each supplied referent; it does not assert
that they are the same property or provide a criterion of property identity. -/
structure PropertyPresentation (f : Frame) where
  Property : Type
  denotes : Property → f.Being → f.Perfection → Prop
  good : Property
  dueActual : Property
  goodMeaning : ∀ x p, denotes good x p ↔ f.GoodIn x p
  dueMeaning : ∀ x p, denotes dueActual x p ↔ DueActuality f x p

/-- A stronger intensional reading; no natural/non-natural classification or
simplicity/indefinability judgment is smuggled into equality. -/
def PropertyIdentity {f : Frame} (p : PropertyPresentation f) : Prop := p.good = p.dueActual

/-- The same due actualities can be classified by the supplied feature data
exactly iff they are constant on equal-data fibers. This is extensional
classification, not computability, knowledge, or a natural-property identity. -/
def FeatureCriterionBoundary : Prop :=
  ∀ (f : Frame) (observe : f.Being × f.Perfection → f.Feature),
    AdmitsCriterion observe (fun a => DueActuality f a.1 a.2) ↔
      FiberInvariant observe (fun a => DueActuality f a.1 a.2)

/-- Candidate identity denotes a supplied definition proposal, not mere spelling.
The class of admissible proposals and its named coverage are explicit open
inputs. Feature-based and fixed-assessor approval reductions are analyst
formulations, not attributed identities for Boyd, Railton or expressivism. -/
structure DefinitionSpace (f : Frame) where
  Candidate : Type
  denotes : Candidate → f.Being → f.Perfection → Prop
  admissible : Candidate → Prop
  dueAccount : Candidate
  featureAccount : Candidate
  approvalAccount : Candidate
  featureCriterion : f.Feature → f.Perfection → Prop
  approves : f.Being → f.Perfection → Prop
  dueMeaning : ∀ x p, denotes dueAccount x p ↔ DueActuality f x p
  featureMeaning : ∀ x p, denotes featureAccount x p ↔ featureCriterion (f.feature x) p
  approvalMeaning : ∀ x p, denotes approvalAccount x p ↔ approves x p

def Named {f : Frame} (s : DefinitionSpace f) (d : s.Candidate) : Prop :=
  d = s.dueAccount ∨ d = s.featureAccount ∨ d = s.approvalAccount

/-- Philosophical coverage hypothesis for this supplied class of proposals.
It is not asserted by the structural surplus/omission fork. -/
def NamedCoverage {f : Frame} (s : DefinitionSpace f) : Prop :=
  ∀ d, s.admissible d → Named s d

/-- A first-class further relevant definition outside the named proposals.
No claim that such a proposal actually exists follows from failed proof search. -/
def AdditionalRelevantDefinition {f : Frame} (s : DefinitionSpace f) : Prop :=
  ∃ d, s.admissible d ∧ ¬ Named s d

/-- Correct extensional description of goodness under the fixed profile.
Admissibility alone does not assert correctness. -/
def CorrectAccount {f : Frame} (s : DefinitionSpace f) (d : s.Candidate) : Prop :=
  ∀ x p, f.GoodIn x p ↔ s.denotes d x p

/-- Nonvacuity/scope input: the chosen admissible class contains an account
that correctly describes the profile's goodness relation. -/
def CorrectAccountExists {f : Frame} (s : DefinitionSpace f) : Prop :=
  ∃ d, s.admissible d ∧ CorrectAccount s d

def FeatureAccountFails {f : Frame} (s : DefinitionSpace f) : Prop :=
  ¬ CorrectAccount s s.featureAccount

def ApprovalAccountFails {f : Frame} (s : DefinitionSpace f) : Prop :=
  ¬ CorrectAccount s s.approvalAccount

/-- Named philosophical coverage or an explicit further-definition witness.
This is a logical coverage fork, not proof of either philosophical branch. -/
def NamedCoverageFork : Prop :=
  ∀ (f : Frame) (s : DefinitionSpace f), NamedCoverage s ∨ AdditionalRelevantDefinition s

/-- Pointwise equivalence of definition extensions. This does not identify
candidate objects or property intensions. No propositional extensionality axiom
is needed. -/
def Coextensive {f : Frame} (s : DefinitionSpace f) (a b : s.Candidate) : Prop :=
  ∀ x p, s.denotes a x p ↔ s.denotes b x p

def SemanticallyNamed {f : Frame} (s : DefinitionSpace f) (d : s.Candidate) : Prop :=
  Coextensive s d s.dueAccount ∨ Coextensive s d s.featureAccount ∨
    Coextensive s d s.approvalAccount

/-- Weakest named coverage used for the extensional target: every admissible
proposal has the extension of a named proposal, even if it has a distinct name
or intension. The stronger identity coverage above is preserved separately. -/
def SemanticNamedCoverage {f : Frame} (s : DefinitionSpace f) : Prop :=
  ∀ d, s.admissible d → SemanticallyNamed s d

/-- A further relevant proposal with a genuinely different extension, not a
new spelling or a coextensive property presentation. -/
def AdditionalSemanticDefinition {f : Frame} (s : DefinitionSpace f) : Prop :=
  ∃ d, s.admissible d ∧ ¬ SemanticallyNamed s d

def SemanticNamedCoverageFork : Prop :=
  ∀ (f : Frame) (s : DefinitionSpace f),
    SemanticNamedCoverage s ∨ AdditionalSemanticDefinition s

inductive Bearer | knife | counterweight deriving DecidableEq
inductive Perfection | existence | edge | mass deriving DecidableEq
inductive Form | cutter | weight deriving DecidableEq
inductive End | cutting | balancing deriving DecidableEq

def artifactForm : Bearer → Form
  | .knife => .cutter
  | .counterweight => .weight

def artifactEnd : Form → End
  | .cutter => .cutting
  | .weight => .balancing

def artifactDueTable : Form → End → Perfection → Bool
  | .cutter => fun e p => match e with
    | .cutting => match p with
      | .existence => true
      | .edge => true
      | .mass => false
    | .balancing => false
  | .weight => fun e p => match e with
    | .cutting => false
    | .balancing => match p with
      | .existence => true
      | .edge => false
      | .mass => true

/-- The non-overlapping table avoids an equation-compiler propext dependency
from overlapping patterns; its extensional table is unchanged. -/
def artifactDue (F : Form) (E : End) (p : Perfection) : Prop :=
  if artifactDueTable F E p then True else False

def artifactHas (_ : Bearer) : Perfection → Prop
  | .existence => True
  | .edge => False
  | .mass => True

def artifactGood (x : Bearer) (p : Perfection) : Prop :=
  artifactDue (artifactForm x) (artifactEnd (artifactForm x)) p ∧ artifactHas x p

/-- The named fixed finite profile is retained by every exported control. -/
def artifact : Frame where
  Being := Bearer
  Perfection := Perfection
  Form := Form
  End := End
  Feature := Unit
  form := artifactForm
  endOf := artifactEnd
  DueFor := artifactDue
  Has := artifactHas
  GoodIn := artifactGood
  feature := fun _ => ()
  substantial := .existence
  ultimate := fun x => match x with | .knife => .edge | .counterweight => .mass
  GoodSimply := fun x => x = .counterweight

def surplusArtifact : Frame := { artifact with GoodIn := artifactHas }
def omissionArtifact : Frame :=
  { artifact with GoodIn := fun x p => x = .counterweight ∧ artifactGood x p }
def mixedArtifact : Frame :=
  { artifact with GoodIn := fun x p => x = .knife ∧ p = .mass }

def coarse (a : Bearer × Perfection) : Unit × Perfection := ((), a.2)
def formSensitive (a : Bearer × Perfection) : Form × End × Perfection :=
  (artifactForm a.1, artifactEnd (artifactForm a.1), a.2)

/-- Explicit analyst aspect-ascription test of Boyd's sufficient positive-case
schema. Fostering and sustaining are fixed, nonempty predicates in the controls;
this is not a universal definition attributed to Boyd. -/
def BoydAspectFragment (f : Frame)
    (Fosters Sustains : f.Being × f.Perfection → Prop) : Prop :=
  TruthCore.English.Boyd.ClusterGoodnessReading
    (fun a : f.Being × f.Perfection => f.GoodIn a.1 a.2) Fosters Sustains

def fosters (a : Bearer × Perfection) : Prop :=
  a.1 = .counterweight ∧ a.2 = .mass

def sustains (a : Bearer × Perfection) : Prop :=
  a.1 = .counterweight ∧ a.2 = .existence

/-- Explicit analyst welfare-aspect identification. It does not identify
Railton's personal welfare with ontological goodness in the source records. -/
def RailtonAspectFragment (f : Frame) (interest : f.Being × f.Perfection → Prop) : Prop :=
  TruthCore.English.Railton.WelfareReading
    (fun (_ : Unit) a => f.GoodIn a.1 a.2) (fun _ a => interest a)

/-- The positive-case fragment can occupy each extensional cell, under the
same supplied actuality/form/end and fixed positive criteria. The full source
accounts remain stronger than these recorded fragments. -/
def RivalOccupancy : Prop :=
  BoydAspectFragment artifact fosters sustains ∧
  BoydAspectFragment surplusArtifact fosters sustains ∧
  BoydAspectFragment omissionArtifact fosters sustains ∧
  fosters (.counterweight, .mass) ∧ sustains (.counterweight, .existence) ∧
  RailtonAspectFragment artifact (fun a => artifactGood a.1 a.2) ∧
  RailtonAspectFragment surplusArtifact (fun a => artifactHas a.1 a.2)

inductive Proposal | due | feature | approval | other deriving DecidableEq

def artifactWithGood (mixed : Bool) : Frame :=
  { artifact with GoodIn := if mixed then mixedArtifact.GoodIn else artifactGood }

/-- A fixed finite candidate space with a named additional proposal. -/
def artifactSpace (mixed : Bool) : DefinitionSpace (artifactWithGood mixed) where
  Candidate := Proposal
  denotes := fun d x p => match d with
    | .due => artifactGood x p
    | .feature => artifactHas x p
    | .approval => x = .counterweight ∧ artifactGood x p
    | .other => x = .knife ∧ p = .mass
  admissible := fun d => if mixed then True else d ≠ .other
  dueAccount := .due
  featureAccount := .feature
  approvalAccount := .approval
  featureCriterion := fun _ p => artifactHas .knife p
  approves := fun x p => x = .counterweight ∧ artifactGood x p
  dueMeaning := by cases mixed <;> intro x p <;> exact Iff.rfl
  featureMeaning := by cases mixed <;> intro x p <;> exact Iff.rfl
  approvalMeaning := by cases mixed <;> intro x p <;> exact Iff.rfl

/-- Both the named-coverage path and an explicit missing-definition path have
concrete models. In the latter, rejecting the feature and approval accounts
still does not imply the due-actuality thesis. -/
def NamedSpaceControls : Prop :=
  (NamedCoverage (artifactSpace false) ∧ CorrectAccountExists (artifactSpace false) ∧
    FeatureAccountFails (artifactSpace false) ∧ ApprovalAccountFails (artifactSpace false)) ∧
  (AdditionalRelevantDefinition (artifactSpace true) ∧
    CorrectAccountExists (artifactSpace true) ∧ FeatureAccountFails (artifactSpace true) ∧
    ApprovalAccountFails (artifactSpace true) ∧ ¬ DueActualityThesis mixedArtifact)

/-- Actual extension-different further proposal in the mixed model, and
semantic named coverage in the due-actuality model. Alias proposals alone would
not refute this weaker coverage. -/
def SemanticScopeControls : Prop :=
  SemanticNamedCoverage (artifactSpace false) ∧
  AdditionalSemanticDefinition (artifactSpace true)

/-- Boundaries and witnesses, not an independently defended goodness thesis. -/
def BoundaryCertificate : Prop :=
  (∀ f : Frame, DueActualityThesis f →
    (GoodnessIsActualityReading f.GoodIn f.Has ↔ AllActualitiesDue f)) ∧
  (∀ f : Frame, DueActualityThesis f → ¬ SurplusGood f ∧ ¬ OmittedDueGood f) ∧
  DueActualityThesis artifact ∧
  SurplusGood surplusArtifact ∧ ¬ OmittedDueGood surplusArtifact ∧
  OmittedDueGood omissionArtifact ∧ ¬ SurplusGood omissionArtifact ∧
  SurplusGood mixedArtifact ∧ OmittedDueGood mixedArtifact ∧
  ¬ GoodnessIsActualityReading artifact.GoodIn artifact.Has ∧
  GoodnessIsActualityReading surplusArtifact.GoodIn surplusArtifact.Has ∧
  (artifact.GoodIn .knife .existence ∧ Due artifact .knife .edge ∧
    ¬ artifact.Has .knife .edge ∧ ¬ artifact.GoodSimply .knife) ∧
  UltimateDuePerfectionRequiredReading artifact.GoodSimply
    (fun x => artifact.Has x (artifact.ultimate x)) ∧
  ¬ AdmitsCriterion coarse (fun a => artifact.GoodIn a.1 a.2) ∧
  AdmitsCriterion formSensitive (fun a => artifact.GoodIn a.1 a.2) ∧
  FeatureCriterionBoundary ∧
  (∃ p : PropertyPresentation artifact,
    DueActualityThesis artifact ∧ ¬ PropertyIdentity p) ∧
  RivalOccupancy ∧ NamedSpaceControls

end TruthCore.Metaethics.GoodnessFormEnd
