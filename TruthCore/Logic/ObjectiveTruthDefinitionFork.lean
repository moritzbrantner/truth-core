module

public import TruthCore.Logic.ExcludedMiddle
public import TruthCore.English.OConnor.Metaethics
public import TruthCore.English.OConnor.ProblemOfEvil

/-!
# Operational readings of objective truth

The legacy source vocabulary leaves ObjectiveTruth as a parameter. These are
analyst propositions calibrating that parameter against one supplied family of
truth evaluations over attitude profiles. The content and all non-attitude
facts are intended to stay fixed across those profiles; whether an application
really has that interpretation is a separate bridge, not proved here.

Actual truth plus profile stability, profile stability alone, and actual truth
alone are different proposed accounts. Pointwise calibration is not property
identity, robust representation, causal independence, or a definition of every
philosophical use of objective. In particular a false content can be stable.

NamedCoverage is an openly supplied coverage proposition. RemainingDefinition
names a classifier with a genuinely different extension in the same profile;
it is not another spelling of a named account. The ambient comparison class is
all supplied binary classifiers. Nothing proves that each is an adequate
natural-language account, or that these three historical schools exhaust truth.
-/

@[expose] public section
namespace TruthCore.Logic.ObjectiveTruthDefinitionFork

/-- Fixed content and truth evaluations under supplied attitude profiles.
`objective` is independent data so all proposed calibrations can fail. -/
structure Frame where
  Sentence : Type
  AttitudeProfile : Type
  actual : AttitudeProfile
  holds : AttitudeProfile → Sentence → Prop
  objective : Sentence → Prop

/-- Stable truth status across this supplied attitude-profile family. Stability
alone does not assert actual truth. -/
def Stable (f : Frame) (s : f.Sentence) : Prop :=
  ∀ p, f.holds p s ↔ f.holds f.actual s

/-- Analyst operational proposal: objectively true iff actually true and stable.
This is not silently adopted as the legacy source predicate's meaning. -/
def ActualStableDefinition (f : Frame) : Prop :=
  ∀ s, f.objective s ↔ (f.holds f.actual s ∧ Stable f s)

/-- Alternative calibration that omits the actual-truth component. It is not
claimed to be logically weaker than the biconditional actual-stable account. -/
def InvariantOnlyDefinition (f : Frame) : Prop :=
  ∀ s, f.objective s ↔ Stable f s

/-- A different account that adds no profile-independence requirement to truth. -/
def ActualTruthOnlyDefinition (f : Frame) : Prop :=
  ∀ s, f.objective s ↔ f.holds f.actual s

/-- The weakest bridge used in the external-evil composition below. It does not
select a full account of objective truth. -/
def HasTruthComponent (f : Frame) : Prop :=
  ∀ s, f.objective s → f.holds f.actual s

/-- The current classifier is calibrated by at least one named account.
This is a coverage premise, not an established fact about all definitions. -/
def NamedCoverage (f : Frame) : Prop :=
  ActualStableDefinition f ∨ InvariantOnlyDefinition f ∨ ActualTruthOnlyDefinition f

/-- A first-class remaining account in the same extensional comparison class.
The finite control realizes it with an actually different extension. -/
def RemainingDefinition (f : Frame) : Prop :=
  ¬ ActualStableDefinition f ∧ ¬ InvariantOnlyDefinition f ∧ ¬ ActualTruthOnlyDefinition f

def NotInvariantOnlyDefinition (f : Frame) : Prop := ¬ InvariantOnlyDefinition f

def NotActualTruthOnlyDefinition (f : Frame) : Prop := ¬ ActualTruthOnlyDefinition f

/-- Structural coverage including the explicit remaining-account branch;
it does not prove NamedCoverage. -/
def DefinitionFork : Prop :=
  ∀ f : Frame, ActualStableDefinition f ∨ InvariantOnlyDefinition f ∨
    ActualTruthOnlyDefinition f ∨ RemainingDefinition f

/-- The external moral-evil premise is not objective under this supplied
classifier. No assertion or attitude-act predicate is inferred. -/
def ExternalEvilNotObjective (f : Frame) (evil : f.Sentence) : Prop :=
  ¬ f.objective evil

/-! Finite controls. Constructor labels have their baseline meanings in holds. -/
inductive Content where
  | stableTrue | stableFalse | actualTrueVariable | actualFalseVariable
  deriving DecidableEq

def holds : Bool → Content → Prop
  | false, .stableTrue => True
  | true, .stableTrue => True
  | false, .stableFalse => False
  | true, .stableFalse => False
  | false, .actualTrueVariable => True
  | true, .actualTrueVariable => False
  | false, .actualFalseVariable => False
  | true, .actualFalseVariable => True

def actualStable : Frame where
  Sentence := Content
  AttitudeProfile := Bool
  actual := false
  holds := holds
  objective := fun s => s = .stableTrue

def invariantOnly : Frame :=
  { actualStable with objective := fun s => s = .stableTrue ∨ s = .stableFalse }

def actualOnly : Frame :=
  { actualStable with objective := fun s => s = .stableTrue ∨ s = .actualTrueVariable }

/-- A true-but-variable singleton, distinct from all three named extensions.
A formal remaining classifier, not a defended account of philosophical truth. -/
def remaining : Frame :=
  { actualStable with objective := fun s => s = .actualTrueVariable }

/-- A nontrivial truth profile where all three calibrations coextend. The
false-at-actual content becomes true at the other profile, so it is not stable. -/
def overlap : Frame where
  Sentence := Bool
  AttitudeProfile := Bool
  actual := false
  holds := fun p s => s = true ∨ p = true
  objective := fun s => s = true

/-- Each advertised difference survives in the exported proposition, rather
than only as incidental facts of a hidden model witness. -/
def Controls : Prop :=
  (ActualStableDefinition actualStable ∧ HasTruthComponent actualStable ∧
    ¬ InvariantOnlyDefinition actualStable ∧ ¬ ActualTruthOnlyDefinition actualStable) ∧
  (InvariantOnlyDefinition invariantOnly ∧ ¬ HasTruthComponent invariantOnly ∧
    invariantOnly.objective Content.stableFalse ∧
    ¬ invariantOnly.holds invariantOnly.actual Content.stableFalse) ∧
  (ActualTruthOnlyDefinition actualOnly ∧ HasTruthComponent actualOnly ∧
    ¬ ActualStableDefinition actualOnly ∧ actualOnly.objective Content.actualTrueVariable ∧
    ¬ Stable actualOnly Content.actualTrueVariable) ∧
  (RemainingDefinition remaining ∧ HasTruthComponent remaining ∧
    remaining.objective Content.actualTrueVariable ∧
    remaining.holds remaining.actual Content.actualTrueVariable ∧ ¬ NamedCoverage remaining) ∧
  (ActualStableDefinition overlap ∧ InvariantOnlyDefinition overlap ∧
    ActualTruthOnlyDefinition overlap ∧ overlap.objective true ∧
    ¬ overlap.holds overlap.actual false)

/-- The model's moral/badness predicate picks one stably false content; truth
aptness coextends with actual truth for the other supplied contents. These are
model assignments satisfying the old four premises, not historical assertions. -/
def modelMoral (s : Content) : Prop := s = .stableFalse

def BridgeOmissionControl : Prop :=
  InvariantOnlyDefinition invariantOnly ∧
  TruthCore.English.OConnor.MoralStatementsLackTruthValueReading modelMoral (holds false) ∧
  TruthCore.English.OConnor.LackingTruthValueExcludesTruthReading
    (holds false) (invariantOnly.holds invariantOnly.actual) ∧
  TruthCore.English.OConnor.BadnessAscriptionsAreMoralReading modelMoral modelMoral ∧
  TruthCore.English.OConnor.ManMadeEvilPremiseSaysSomethingBadReading
    modelMoral Content.stableFalse ∧
  invariantOnly.objective Content.stableFalse ∧
  ¬ invariantOnly.holds invariantOnly.actual Content.stableFalse ∧
  ¬ HasTruthComponent invariantOnly

end TruthCore.Logic.ObjectiveTruthDefinitionFork
