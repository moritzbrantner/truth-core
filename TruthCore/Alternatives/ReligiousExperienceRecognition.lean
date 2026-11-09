module
public import TruthCore.Alternatives.RevelationRecognition
public import TruthCore.Case.Catholicism.StageThree.DivineFounding
@[expose] public section
namespace TruthCore.Alternatives.ReligiousExperienceRecognition
open TruthCore.Case.Catholicism
open TruthCore.Alternatives.RevelationRecognition
/-- Two selected experience tokens, not an exhaustive psychology or theology.
Occurrence is having the experience, veridicality is its presenting its actual
source accurately, and defeated means an undefeated counterconsideration exists.
None implies the others. Normative warrant is a separate primitive judgment.
A hallucination can occur without being veridical. Competing candidates can
both be presented without both being actual sources. -/
structure Experience (σ : Signature) (R : RecognitionProfile σ) where
  occurs : Bool → Prop
  defeated : Bool → Prop
  source : Bool → Option σ.Being
  warranted : Bool → Prop
  candidate : Bool → σ.Being
  situation : Bool → R.Situation
  move : (e : Bool) → (R.practice (situation e)).Move
def Veridical {σ : Signature} {R : RecognitionProfile σ} (E : Experience σ R) (e : Bool) : Prop :=
  E.source e = some (E.candidate e)
/-- Local zero-false-positive calibration only for occurring undefeated tokens;
not statistical reliability, and not warranted by absence of known defeaters. -/
def Calibrated {σ : Signature} {R : RecognitionProfile σ} (E : Experience σ R) : Prop :=
  ∀ e, E.occurs e → ¬ E.defeated e → Veridical E e
/-- Theological identification is OPEN, distinct from accurate source presentation.
It includes admissibility and correctness, neither hidden in veridicality. -/
def Identified {σ : Signature} {R : RecognitionProfile σ} (E : Experience σ R) : Prop :=
  ∀ e, Veridical E e → σ.IsGod (E.candidate e) ∧ R.admissible (E.situation e) ∧
    R.RecognizesAsDivine (E.situation e) (E.candidate e) (E.move e) ∧
    (R.practice (E.situation e)).Correct (E.move e)
def Occurrence {σ : Signature} {R : RecognitionProfile σ} (E : Experience σ R) : Prop :=
  ∃ e, E.occurs e ∧ ¬ E.defeated e
def RecognizedGod (σ : Signature) (R : RecognitionProfile σ) : Prop :=
  ∃ g, σ.IsGod g ∧ PossibleCorrectRecognition σ R g
/-- Open normative rule, intentionally nonfactive. -/
def Permission {σ : Signature} {R : RecognitionProfile σ} (E : Experience σ R) : Prop :=
  ∀ e, E.occurs e → ¬ E.defeated e → E.warranted e
def WarrantedToken {σ : Signature} {R : RecognitionProfile σ} (E : Experience σ R) : Prop :=
  ∃ e, E.warranted e
/-- Extra universal coverage; cannot be obtained from one existential token. -/
def CoversGods {σ : Signature} {R : RecognitionProfile σ} (E : Experience σ R) : Prop :=
  ∀ g, σ.IsGod g → ∃ e, E.occurs e ∧ ¬ E.defeated e ∧ E.candidate e = g
/-- Only the reverse of existing full calibration is required. This is an OPEN
assembly bridge to the primitive root capability, not its definition. -/
def CapacityBridge (σ : Signature) (R : RecognitionProfile σ) : Prop :=
  ∀ g, σ.IsGod g → PossibleCorrectRecognition σ R g → σ.RevealsRecognizably g
/-- Finite controls reuse the existing Bool God signature. Flags vary occurrence,
source accuracy, recognition correctness, and root capability independently. -/
def modelSignature (b : Bool) : Signature :=
  { TruthCore.Case.Catholicism.StageThree.DivineFounding.modelSig True with
    RevealsRecognizably := fun _ => b = true }
def modelProfile (i b : Bool) : RecognitionProfile (modelSignature b) where
  Situation := Bool
  admissible := fun _ => True
  practice _ :=
    { Move := Unit, Correct := fun _ => i = true,
      OwnStandard := fun _ => False, Defined := fun _ => False,
      AffirmsNaturalKnowability := fun _ => False, AnswersToSharedReason := fun _ => True }
  actual := true
  RecognizesAsDivine := fun _ g _ => g = true
def modelExperience (o v i b : Bool) : Experience (modelSignature b) (modelProfile i b) where
  occurs e := o = true ∧ e = true
  defeated _ := False
  source _ := if v then some true else none
  warranted _ := True
  candidate _ := true
  situation _ := true
  move _ := ()
/-- Both tokens occur and present competing sources. The false presentation has
an undefeated defeater; calibration survives only on the selected clean token. -/
def mixedExperience : Experience (modelSignature true) (modelProfile true true) :=
  { modelExperience true true true true with
    occurs := fun _ => True
    defeated := fun e => e = false
    candidate := fun e => e }
/-- A genuine finite witness and four omission controls, plus permission with a
false-positive hallucination and no correct recognition. These are model
interpretations only. The reverse capability bridge is independently needed. -/
def Controls : Prop :=
  (Occurrence (modelExperience true true true true) ∧
   Calibrated (modelExperience true true true true) ∧
   Identified (modelExperience true true true true) ∧
   CoversGods (modelExperience true true true true) ∧
   CapacityBridge (modelSignature true) (modelProfile true true)) ∧
  (Calibrated (modelExperience false false false false) ∧
   Identified (modelExperience false false false false) ∧
   CapacityBridge (modelSignature false) (modelProfile false false) ∧
   ¬ RecognizedGod (modelSignature false) (modelProfile false false)) ∧
  (Occurrence (modelExperience true false false false) ∧
   Identified (modelExperience true false false false) ∧
   Permission (modelExperience true false false false) ∧
   WarrantedToken (modelExperience true false false false) ∧
   ¬ RecognizedGod (modelSignature false) (modelProfile false false)) ∧
  (Occurrence (modelExperience true true false false) ∧
   Calibrated (modelExperience true true false false) ∧
   ¬ RecognizedGod (modelSignature false) (modelProfile false false)) ∧
  (Calibrated (modelExperience true true true false) ∧
   Identified (modelExperience true true true false) ∧
   CoversGods (modelExperience true true true false) ∧
   ¬ RevelationPossibleAndRecognizable (modelSignature false)) ∧
  (mixedExperience.occurs false ∧ mixedExperience.occurs true ∧
   ¬ Veridical mixedExperience false ∧ Veridical mixedExperience true ∧
   Calibrated mixedExperience ∧ Identified mixedExperience)
end TruthCore.Alternatives.ReligiousExperienceRecognition
