module

public import TruthCore.Logic.Verificationism
public import TruthCore.Logic.ExcludedMiddle
public import TruthCore.Logic.SelfApplication
public import TruthCore.Results.Logic.Verificationism.VerdictSilent.Solution
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3TertiaVia
public import TruthCore.Logic.Verificationism.Model

/-!
Analyst investigation motivated by the existing unencoded q46a2 beginning
statement. Finite-observation conclusive verification is ONE proof standard;
its failure is not impossibility of logical consequence, warrant, natural
theology or the source's broader demonstration claim. Content, presented
premise origins and declared method are separately recorded. Their tags do not
change the fixed empirical proof standard or define theological as unverifiable.
-/
@[expose] public section
namespace TruthCore.Logic.ScopedEmpiricalProofBarrier
open TruthCore.Logic.Verificationism

variable {L : Language}

/-- A true content has an observation-indistinguishable false alternative.
This is a structural epistemic interface, not a mere topic label. -/
def ObservationBarrier (F : Frame L) (s : L.Sentence) : Prop :=
  ∀ w, L.holds w s → ∃ v,
    (∀ o, F.observation o → (L.holds w o ↔ L.holds v o)) ∧ ¬ L.holds v s

inductive Subject where
  | divine | cosmological | ordinary
  deriving DecidableEq
inductive PremiseOrigin where
  | observation | revelation
  deriving DecidableEq
inductive Method where
  | observational | deductive | revelatory
  deriving DecidableEq
inductive Criterion where
  | subject | premises | method
  deriving DecidableEq

/-- Presentations of inquiries: their recorded premises/method classify the
presentation, not all possible alternative proofs of its target. -/
structure Inquiries (L : Language) where
  Inquiry : Type
  target : Inquiry → L.Sentence
  subject : Inquiry → Subject
  premises : Inquiry → List PremiseOrigin
  method : Inquiry → Method

def Classified (q : Inquiries L) : Criterion → q.Inquiry → Prop
  | .subject, t => q.subject t = .divine
  | .premises, t => .revelation ∈ q.premises t
  | .method, t => q.method t = .revelatory

def DomainCalibration (q : Inquiries L) (T : q.Inquiry → Prop) (c : Criterion) : Prop :=
  ∀ t, T t ↔ Classified q c t

def SubjectDefinition (q : Inquiries L) (T : q.Inquiry → Prop) : Prop :=
  DomainCalibration q T .subject

def PremiseDefinition (q : Inquiries L) (T : q.Inquiry → Prop) : Prop :=
  DomainCalibration q T .premises

def MethodDefinition (q : Inquiries L) (T : q.Inquiry → Prop) : Prop :=
  DomainCalibration q T .method

def NamedDomainCoverage (q : Inquiries L) (T : q.Inquiry → Prop) : Prop :=
  SubjectDefinition q T ∨ PremiseDefinition q T ∨ MethodDefinition q T

def RemainingDomain (q : Inquiries L) (T : q.Inquiry → Prop) : Prop :=
  ¬ SubjectDefinition q T ∧ ¬ PremiseDefinition q T ∧ ¬ MethodDefinition q T

def DomainFork : Prop :=
  ∀ (L : Language) (q : Inquiries L) (T : q.Inquiry → Prop),
    NamedDomainCoverage q T ∨ RemainingDomain q T

def GlobalNoEmpiricalProof (F : Frame L) (q : Inquiries L) : Prop :=
  ∀ t, ¬ ConclusivelyVerifiable F (q.target t)

def RestrictedNoEmpiricalProof (F : Frame L) (q : Inquiries L)
    (T : q.Inquiry → Prop) : Prop :=
  ∀ t, T t → ¬ ConclusivelyVerifiable F (q.target t)

/-- Consequential OPEN scoped input; classification by itself does not imply it. -/
def ScopedObservationBarrier (F : Frame L) (q : Inquiries L)
    (T : q.Inquiry → Prop) : Prop := ∀ t, T t → ObservationBarrier F (q.target t)

/-- Coverage of the proposed barrier only for empirically unprovable targets.
This remains OPEN; finite insufficiency can persist without this barrier. -/
def BarrierExplainsAll (F : Frame L) (q : Inquiries L) (T : q.Inquiry → Prop) : Prop :=
  ∀ t, T t → ¬ ConclusivelyVerifiable F (q.target t) → ObservationBarrier F (q.target t)

def AdditionalRelevantBarrier (F : Frame L) (q : Inquiries L) (T : q.Inquiry → Prop) : Prop :=
  ∃ t, T t ∧ ¬ ObservationBarrier F (q.target t) ∧
    ¬ ConclusivelyVerifiable F (q.target t)

/-- Existing self-application norm, instantiated at this exact proof standard.
Use of its metathesis requires an actual T(self) witness and a representation
bridge; neither is built in by calling an inquiry theological. -/
def noProofNorm (q : Inquiries L) (T : q.Inquiry → Prop) :
    TruthCore.Logic.SelfApplication.Norm q.Inquiry := ⟨T, fun _ => False⟩

/-- Actual application of the existing scope schema. An inquiry is not a
metathesis merely because named self; representation and actual T-membership
must be supplied before applying this conditional to one. -/
theorem inScopeConstraint {L : Language} (F : Frame L) (q : Inquiries L)
    (T : q.Inquiry → Prop) (self : q.Inquiry) (hScope : T self) :
    (RestrictedNoEmpiricalProof F q T → ¬ ConclusivelyVerifiable F (q.target self)) ∧
    (ConclusivelyVerifiable F (q.target self) → ¬ RestrictedNoEmpiricalProof F q T) := by
  have h := TruthCore.Logic.SelfApplication.Norm.selfApplication
    (N := noProofNorm q T)
    (Acceptable := fun t => ConclusivelyVerifiable F (q.target t))
    hScope (fun hFalse => hFalse)
  exact ⟨h.1, fun hp => TruthCore.Logic.SelfApplication.Norm.not_holds_of_counterexample (h.2 hp)⟩

namespace Control
open TruthCore.Results.Logic.Verificationism.VerdictSilent
open TruthCore.Latin.Aquinas.SummaTheologiae

def beginning : twoCoordinate.Sentence := fun w => w.2
def observable : twoCoordinate.Sentence := fun w => w.1
def tautology : twoCoordinate.Sentence := fun _ => true

/-- A discrete beginning profile versus a past with no earliest time. These
are analytical temporal orders, not actual cosmos histories or q46 source identity. -/
def pastOrder (hasBeginning : Bool) (s t : Nat) : Prop :=
  if hasBeginning then s < t else t < s

inductive Inquiry where
  | beginningQuestion | divineHidden | ordinaryHidden | theologicalTautology | ordinaryObservable
  deriving DecidableEq

def inquiries : Inquiries twoCoordinate where
  Inquiry := Inquiry
  target
    | .beginningQuestion => beginning
    | .divineHidden => beginning
    | .ordinaryHidden => beginning
    | .theologicalTautology => tautology
    | .ordinaryObservable => observable
  subject
    | .beginningQuestion => .cosmological
    | .divineHidden => .divine
    | .ordinaryHidden => .ordinary
    | .theologicalTautology => .divine
    | .ordinaryObservable => .ordinary
  premises
    | .beginningQuestion => [.revelation]
    | .divineHidden => []
    | .ordinaryHidden => []
    | .theologicalTautology => [.revelation]
    | .ordinaryObservable => []
  method
    | .beginningQuestion => .revelatory
    | .divineHidden => .deductive
    | .ordinaryHidden => .observational
    | .theologicalTautology => .revelatory
    | .ordinaryObservable => .observational

def selected (t : Inquiry) : Prop := t = .beginningQuestion

/-- All advertised finite properties are retained, including proof-positive
contents in every named theological class. No artificially selected class is
advertised as the entirety of theology. -/
def Properties : Prop :=
  (∀ w, twoCoordinate.holds w beginning ↔ PastIsFinite (pastOrder w.2) 0) ∧
  ScopedObservationBarrier observableFrame inquiries selected ∧
  RestrictedNoEmpiricalProof observableFrame inquiries selected ∧
  ¬ GlobalNoEmpiricalProof observableFrame inquiries ∧
  RemainingDomain inquiries selected ∧
  (∀ c, Classified inquiries c .theologicalTautology ∧
    ConclusivelyVerifiable observableFrame (inquiries.target .theologicalTautology)) ∧
  (¬ Classified inquiries .subject .beginningQuestion ∧
    Classified inquiries .premises .beginningQuestion ∧
    Classified inquiries .method .beginningQuestion) ∧
  (Classified inquiries .subject .divineHidden ∧
    ¬ Classified inquiries .premises .divineHidden ∧
    ¬ Classified inquiries .method .divineHidden) ∧
  (¬ Classified inquiries .subject .ordinaryHidden ∧
    ¬ Classified inquiries .premises .ordinaryHidden ∧
    ¬ Classified inquiries .method .ordinaryHidden ∧
    ¬ ConclusivelyVerifiable observableFrame (inquiries.target .ordinaryHidden)) ∧
  (inquiries.target .beginningQuestion = inquiries.target .divineHidden ∧
    inquiries.target .divineHidden = inquiries.target .ordinaryHidden) ∧
  twoCoordinate.Entails [beginning] beginning ∧
  ConclusivelyVerifiable observableFrame observable

def lawInquiries : Inquiries Model.lawLanguage where
  Inquiry := Unit
  target _ := Model.ravens.law
  subject _ := .ordinary
  premises _ := []
  method _ := .observational

/-- A second cause of finite empirical nonverification: all observations
jointly discriminate the law, but no finite observation set proves it. -/
def FinitaryControl : Prop :=
  ¬ ObservationBarrier Model.lawFrame Model.ravens.law ∧
  ¬ ConclusivelyVerifiable Model.lawFrame Model.ravens.law ∧
  AdditionalRelevantBarrier Model.lawFrame lawInquiries (fun _ => True) ∧
  ¬ BarrierExplainsAll Model.lawFrame lawInquiries (fun _ => True)

end Control
end TruthCore.Logic.ScopedEmpiricalProofBarrier
