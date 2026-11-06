module

public import TruthCore.Alternatives.Fideism
public import TruthCore.Case.Catholicism.Root
public import TruthCore.Logic.ExcludedMiddle

/-!
# Revelation capability and practice insulation

The root's RevealsRecognizably is a capability, not an actual recognition
move. A RecognitionProfile supplies candidate admissible situations, each with
its own practice, and a distinguished actual situation. Admissibility is an
open framework input; the carrier is not asserted to exhaust real possibilities
or satisfy a particular modal logic. Recognition is a move judging a candidate
revelation to be from the selected divine being. Correctness remains a separate
practice predicate. No perception, institutional endorsement or successful
recognition is inferred from its name.

Ordinary analogy: a message may be publicly recognizable in one permitted
circumstance even though the actual community accepts no publicly answerable
recognition move. Capability and actual uptake differ. Correct recognition may
also use only private standards unless the shared-reason bridge is supplied.
These distinctions are interpretation constraints, not empirical assertions.
-/

@[expose] public section

namespace TruthCore.Alternatives.RevelationRecognition

open TruthCore.Alternatives.Fideism
open TruthCore.Case.Catholicism

/-- Candidate recognition situations with actual situation explicitly indexed. -/
structure RecognitionProfile (σ : Signature) where
  Situation : Type
  admissible : Situation → Prop
  practice : Situation → Practice
  actual : Situation
  RecognizesAsDivine : (s : Situation) → σ.Being → (practice s).Move → Prop

/-- Actuality's inclusion in the selected possibility domain is explicit. -/
def ActualAdmissible (σ : Signature) (R : RecognitionProfile σ) : Prop :=
  R.admissible R.actual

/-- Some correct recognition move exists in an admissible situation. This
alone says nothing about actual uptake or outsider-shared standards. -/
def PossibleCorrectRecognition (σ : Signature) (R : RecognitionProfile σ)
    (g : σ.Being) : Prop :=
  ∃ s, R.admissible s ∧ ∃ m, R.RecognizesAsDivine s g m ∧ (R.practice s).Correct m

/-- Weak open realization bridge: capability can be realized correctly
somewhere admissible. The witness need not be in the actual practice. -/
def RecognizableCapacityRealized (σ : Signature) (R : RecognitionProfile σ) : Prop :=
  ∀ g, σ.IsGod g → σ.RevealsRecognizably g → PossibleCorrectRecognition σ R g

/-- Candidate-carrier realization, before any admissibility filter. Adequacy
of that candidate carrier to real possibility is not thereby established. -/
def CandidateRecognitionRealized (σ : Signature) (R : RecognitionProfile σ) : Prop :=
  ∀ g, σ.IsGod g → σ.RevealsRecognizably g →
    ∃ s, ∃ m, R.RecognizesAsDivine s g m ∧ (R.practice s).Correct m

/-- Open coverage of recognition witnesses by the admitted subset. This is a
real assumption: a candidate witness need not be an admitted witness. -/
def AdmissibleRecognitionCoverage (σ : Signature) (R : RecognitionProfile σ) : Prop :=
  ∀ g, σ.IsGod g → σ.RevealsRecognizably g →
    (∃ s, ∃ m, R.RecognizesAsDivine s g m ∧ (R.practice s).Correct m) →
    PossibleCorrectRecognition σ R g

/-- An additional relevant situation is explicit: correct recognition of a
God candidate with the capacity exists outside the admitted subset, while no
admitted situation contains correct recognition of that same candidate. -/
def OutsideAdmissibleRecognition (σ : Signature) (R : RecognitionProfile σ) : Prop :=
  ∃ g, σ.IsGod g ∧ σ.RevealsRecognizably g ∧
    ∃ s, ¬ R.admissible s ∧ ∃ m,
      R.RecognizesAsDivine s g m ∧ (R.practice s).Correct m ∧
      ¬ PossibleCorrectRecognition σ R g

/-- Structural coverage or a precise further-situation witness in this
candidate carrier. It does not exhaust real possibilities outside the profile. -/
def RecognitionAdmissibilityCases (σ : Signature) (R : RecognitionProfile σ) : Prop :=
  AdmissibleRecognitionCoverage σ R ∨ OutsideAdmissibleRecognition σ R

/-- Stronger open calibration: capability coextends with possible correct
recognition on the God candidates. No equality of philosophical meanings. -/
def RecognitionCapacityDefinition (σ : Signature) (R : RecognitionProfile σ) : Prop :=
  ∀ g, σ.IsGod g → (σ.RevealsRecognizably g ↔ PossibleCorrectRecognition σ R g)

/-- Separate open bridge: correct recognition of an actual God candidate in
an admissible situation answers to outsider-shared reason in that situation. -/
def RecognitionAnswersToSharedReason (σ : Signature) (R : RecognitionProfile σ) : Prop :=
  ∀ s g m, R.admissible s → σ.IsGod g → R.RecognizesAsDivine s g m →
    (R.practice s).Correct m → (R.practice s).AnswersToSharedReason m

/-- Insulation holds in every selected admissible situation, rather than only
of the actual practice. No universal real-possibility domain is assumed. -/
def AllAdmissiblePracticesCutOff (σ : Signature) (R : RecognitionProfile σ) : Prop :=
  ∀ s, R.admissible s → CutOffReading (R.practice s)

/-- Open modal-scope bridge: the actual cut-off policy persists throughout
the selected admissible situations. Its failure is a serious escape. -/
def CutOffPersistsToAdmissible (σ : Signature) (R : RecognitionProfile σ) : Prop :=
  CutOffReading (R.practice R.actual) → AllAdmissiblePracticesCutOff σ R

/-- Exact opposing sibling to the root's capability proposition. -/
def RevelationCapabilityRejected (σ : Signature) : Prop :=
  ¬ RevelationPossibleAndRecognizable σ

/-- Relevant calibration failures stay explicit. This is structural coverage
of two bridge tests, not named philosophical or modal theory exhaustion. -/
def RecognitionBridgeCasesCover (σ : Signature) (R : RecognitionProfile σ) : Prop :=
  (RecognizableCapacityRealized σ R ∧ RecognitionAnswersToSharedReason σ R) ∨
    ¬ RecognizableCapacityRealized σ R ∨ ¬ RecognitionAnswersToSharedReason σ R

/-- Six interpretation controls: actual cut-off can coexist with capability;
realization, sharedness and a God witness each matter; the one-way bridge is
strictly weaker than full calibration; a recognition witness can lie only
outside the admitted subset. These are schema interpretations. -/
def RecognitionModels : Prop :=
  (∃ σ : Signature, ∃ R : RecognitionProfile σ,
    GodExists σ.IsGod ∧ RevelationPossibleAndRecognizable σ ∧
    CutOffReading (R.practice R.actual) ∧ ActualAdmissible σ R ∧
    RecognizableCapacityRealized σ R ∧ RecognitionAnswersToSharedReason σ R ∧
    ¬ AllAdmissiblePracticesCutOff σ R ∧ ¬ CutOffPersistsToAdmissible σ R) ∧
  (∃ σ : Signature, ∃ R : RecognitionProfile σ,
    GodExists σ.IsGod ∧ RevelationPossibleAndRecognizable σ ∧
    AllAdmissiblePracticesCutOff σ R ∧ RecognitionAnswersToSharedReason σ R ∧
    ¬ RecognizableCapacityRealized σ R) ∧
  (∃ σ : Signature, ∃ R : RecognitionProfile σ,
    GodExists σ.IsGod ∧ RevelationPossibleAndRecognizable σ ∧
    AllAdmissiblePracticesCutOff σ R ∧ RecognizableCapacityRealized σ R ∧
    ¬ RecognitionAnswersToSharedReason σ R) ∧
  (∃ σ : Signature, ∃ R : RecognitionProfile σ,
    ¬ GodExists σ.IsGod ∧ RevelationPossibleAndRecognizable σ ∧
    AllAdmissiblePracticesCutOff σ R ∧ RecognizableCapacityRealized σ R ∧
    RecognitionAnswersToSharedReason σ R) ∧
  (∃ σ : Signature, ∃ R : RecognitionProfile σ,
    GodExists σ.IsGod ∧ RecognizableCapacityRealized σ R ∧
    ¬ RecognitionCapacityDefinition σ R) ∧
  (∃ σ : Signature, ∃ R : RecognitionProfile σ,
    GodExists σ.IsGod ∧ RevelationPossibleAndRecognizable σ ∧
    CandidateRecognitionRealized σ R ∧ OutsideAdmissibleRecognition σ R ∧
    ¬ AdmissibleRecognitionCoverage σ R ∧ ¬ RecognizableCapacityRealized σ R)

end TruthCore.Alternatives.RevelationRecognition
