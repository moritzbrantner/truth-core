module

public import TruthCore.Logic.CorrectionCriterion
public import TruthCore.Alternatives.RevelationRecognition
public import TruthCore.Causality.NamingVeracityBatch1

@[expose] public section
namespace TruthCore.Logic.RevelationPositive

/-- Explicitly admitted situations, a fixed selected event, and a fixed candidate.
Authorship is supplied independently of observation; no exhaustiveness is claimed. -/
structure Frame where
  Candidate : Type
  Event : Type
  Situation : Type
  Evidence : Type
  admitted : Situation → Prop
  observe : Event → Situation → Evidence
  authored : Candidate → Event → Situation → Prop

/-- An extensional evidence predicate that is sound on the admitted domain and
positively certifies one admitted instance of this same candidate/event. -/
def SoundPositive (F : Frame) (g : F.Candidate) (a : F.Event) : Prop :=
  ∃ certify : F.Evidence → Prop,
    (∀ w, F.admitted w → certify (F.observe a w) → F.authored g a w) ∧
    ∃ w, F.admitted w ∧ certify (F.observe a w) ∧ F.authored g a w

/-- One inhabited positive observation fiber is pure for this candidate/event. -/
def PureFiber (F : Frame) (g : F.Candidate) (a : F.Event) : Prop :=
  ∃ w₀, F.admitted w₀ ∧ F.authored g a w₀ ∧
    ∀ w, F.admitted w → F.observe a w = F.observe a w₀ → F.authored g a w

/-- The stronger criterion is the existing exact-classifier definition on the
admitted subtype, not a second notion of global classification. -/
def FullClassifier (F : Frame) (g : F.Candidate) (a : F.Event) : Prop :=
  CorrectionCriterion.AdmitsCriterion
    (fun w : {w // F.admitted w} => F.observe a w.val)
    (fun w => F.authored g a w.val)

def Characterization : Prop :=
  ∀ (F : Frame) (g : F.Candidate) (a : F.Event),
    SoundPositive F g a ↔ PureFiber F g a

/-- Finite reports are not metaphysical sources. 0,1 are two public report
values; all four candidate situations are admitted unless explicitly removed. -/
abbrev finite (n : Nat) (obs : Fin n → Nat) (source : Fin n → Prop) : Frame where
  Candidate := Unit
  Event := Unit
  Situation := Fin n
  Evidence := Nat
  admitted _ := True
  observe _ := obs
  authored _ _ := source

abbrev ambiguous := finite 2 (fun _ => 0) (fun w => w.val = 0)
abbrev distinctive := finite 3 (fun w => if w.val = 0 then 1 else 0)
  (fun w => w.val < 2)
abbrev discriminated := finite 2 (fun w => if w.val = 0 then 1 else 0)
  (fun w => w.val = 0)
abbrev imitated := finite 4 (fun w => if w.val = 0 ∨ w.val = 3 then 1 else 0)
  (fun w => w.val < 2)

def Controls : Prop :=
  (¬ SoundPositive ambiguous () () ∧ ¬ FullClassifier ambiguous () ()) ∧
  (SoundPositive distinctive () () ∧ ¬ FullClassifier distinctive () ()) ∧
  (SoundPositive discriminated () () ∧ FullClassifier discriminated () ()) ∧
  (¬ SoundPositive imitated () () ∧ ¬ FullClassifier imitated () ())

/-- Independently supplied content and recipient context. The proposition is
what the message says, not a claim that it is true or authored by anyone.
Recipient and occasion are typed identifiers, not recognition-success flags. -/
structure MessageContext where
  Recipient : Type
  Occasion : Type
  content : Prop
  recipient : Recipient
  occasion : Occasion

/-- Open interface to existing practice vocabulary. Neither move correctness
nor access/warrant follows from the existence of an extensional certificate. -/
def EvidenceUptake (σ : TruthCore.Case.Catholicism.Signature)
    (R : TruthCore.Alternatives.RevelationRecognition.RecognitionProfile σ)
    (F : Frame) (candidate : σ.Being → F.Candidate) : Prop :=
  ∀ g a, SoundPositive F (candidate g) a →
    TruthCore.Alternatives.RevelationRecognition.PossibleCorrectRecognition σ R g

/-- Open ability-to-realize premise, preserving the same being through candidate.
It requires a pure fiber, not merely a task that only gods can perform. -/
def AbilityEvidence (σ : TruthCore.Case.Catholicism.Signature)
    (P : TruthCore.Causality.NamingVeracityBatch1.Power σ)
    (F : Frame) (candidate : σ.Being → F.Candidate) : Prop :=
  ∀ g, P.CanDo g P.revealWithSigns → ∃ a, PureFiber F (candidate g) a

/-- Conditional interface to the unchanged old analysis. Full capacity
calibration is openly assumed; its reverse direction remains application of
an open bridge, not independent warrant for the primitive capability. -/
def Bridge : Prop :=
  ∀ (σ : TruthCore.Case.Catholicism.Signature)
    (P : TruthCore.Causality.NamingVeracityBatch1.Power σ)
    (R : TruthCore.Alternatives.RevelationRecognition.RecognitionProfile σ)
    (F : Frame) (candidate : σ.Being → F.Candidate),
    AbilityEvidence σ P F candidate → EvidenceUptake σ R F candidate →
    TruthCore.Alternatives.RevelationRecognition.RecognitionCapacityDefinition σ R →
    TruthCore.Causality.NamingVeracityBatch1.RecognizableRevelationAnalysis σ P

end TruthCore.Logic.RevelationPositive
