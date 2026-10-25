import TruthCore.Metaethics.AnswerMap

/-! Enquiry IV–V and Treatise I.3.6: bounded induction tests (#269).
Source commitments below are open interfaces; tests do not prove their fidelity.
Histories are mathematical alternatives, not claims of metaphysical possibility.
No modal fixtures or regularity/causal-direction semantics are introduced here.
-/
namespace TruthCore.Modern.Hume.Induction

abbrev Trace := Nat → Bool

/-- A finite record of matches, with the next case deliberately outside it. -/
def Recorded (f : Trace) (n : Nat) : Prop := ∀ i, i < n → f i = true

def delayedFailure (n : Nat) : Trace := fun i => if i < n then true else false

/-- E 4.18: a demonstration of uniform continuation is denied. This parameter
represents Hume's kind of demonstration, not Lean provability. -/
def NoDemonstration (demonstratesUniformity : Prop) : Prop :=
  ¬ demonstratesUniformity

/-- E 4.19; T 1.3.6.7: the proposed experimental justification already depends
on the uniformity it purports to establish. Dependency is not entailment. -/
def CircularProposal {A : Type} (experimental : A → Prop)
    (dependsOnUniformity : A → Prop) : Prop :=
  ∀ a, experimental a → dependsOnUniformity a

/-- E 5.5, 5.8: repeated conjunction with a present trigger produces expectation
through custom. Parameters leave the psychology and circumstances explicit. -/
def CustomAccount {E : Type} (repeated trigger expects : E → Prop) : Prop :=
  ∀ e, repeated e → trigger e → expects e

/-- E 5.2 expressly conditions continued influence on unchanged human nature. -/
def ConditionalPersistence {T : Type} (sameNature effectiveCustom : T → Prop) : Prop :=
  ∀ t, sameNature t → effectiveCustom t

/-- E 5.6: absence of custom precludes adjustment of means to ends. Not the
claim that every customary choice succeeds or is epistemically entitled. -/
def MeansEndsDependence {E : Type} (adjusts custom : E → Prop) : Prop :=
  ∀ e, adjusts e → custom e

/-- E 5.21 reports correspondence so far; no assertion about every future case. -/
def ObservedCorrespondence (f : Trace) (n : Nat) : Prop := Recorded f n

/-- E 4.21 separates satisfaction as agent from the philosopher's unsatisfied
request for the foundation of experiential inference. -/
def AgentPhilosopher (satisfiedAgent foundFoundation : Prop) : Prop :=
  satisfiedAgent ∧ ¬ foundFoundation

/-- E 5.7: a categorical experiential inference is anchored in memory or sense. -/
def PresentAnchor {E : Type} (categorical presentFact : E → Prop) : Prop :=
  ∀ e, categorical e → presentFact e

/-- T 1.3.6.11: reason has not proved extension beyond observed instances. -/
def UnprovedExtension (provedUniformExtension : Prop) : Prop :=
  ¬ provedUniformExtension

/-- T 1.3.6.13 denies infallibility of the three associative relations. This
is not an attribution that custom never works or that causal order disappears. -/
def AssociationNotInfallible {E : Type} (associated transitions : E → Prop) : Prop :=
  ¬ (∀ e, associated e → transitions e)

inductive Topic where
  | habit | prediction | intervention | science | cosmology | theology
  deriving DecidableEq

inductive Verdict where
  | entitled | withheld | unsettled
  deriving DecidableEq

/-- Separate practical reliance, reasoning-based foundation, and entitlement.
`entitled` is the critic's normative predicate, not Hume's mere confidence. -/
structure Assessment where
  /-- Practical reliance offered as rational by the assessed position, rather
  than every involuntary expectation or arbitrary action. -/
  relies : Topic → Bool
  reasonFounded : Topic → Bool
  verdict : Topic → Verdict

/-- Stronger than lack of an argument: an explicit denial of entitlement. -/
def StrongSkeptic (a : Assessment) : Prop :=
  ∀ q, a.verdict q = .withheld

/-- Open bridge: practical reliance offered as rational requires epistemic entitlement. -/
def RelianceRequiresEntitlement (a : Assessment) : Prop :=
  ∀ q, a.relies q = true → a.verdict q = .entitled

/-- An internal-critique bridge requiring the skeptic to offer its habit
persistence forecast as entitled, rather than merely customary or conditional. -/
def CertifiesHabit (a : Assessment) : Prop := a.verdict .habit = .entitled

/-- A universal standard applies only where the same relevant evidential basis
is independently established; sharing a topic label is not enough. -/
def UniformStandard (a : Assessment) (sameBasis : Topic → Topic → Prop) : Prop :=
  ∀ x y, sameBasis x y → a.verdict x = a.verdict y

def SomeReliance (a : Assessment) : Prop := ∃ q, a.relies q = true

def RejectStrong (a : Assessment) : Prop := ¬ StrongSkeptic a

def ScienceEntitled (a : Assessment) : Prop := a.verdict .science = .entitled

def TheologyWithheld (a : Assessment) : Prop := a.verdict .theology = .withheld

def SameScienceTheology (sameBasis : Topic → Topic → Prop) : Prop :=
  sameBasis .science .theology

def RejectTheologyWithheld (a : Assessment) : Prop := ¬ TheologyWithheld a

/-- Limited skepticism with ordinary reliance and no explicit entitlement denial. -/
def limited : Assessment :=
  ⟨fun _ => true, fun _ => false, fun _ => .unsettled⟩

/-- A stronger practical position is still consistent until a normative bridge
is imposed. It is a test reconstruction, not an attributed Humean doctrine. -/
def strong : Assessment :=
  ⟨fun _ => true, fun _ => false, fun _ => .withheld⟩

/-- Different verdicts can be consistent under a standard sensitive to evidence. -/
def differentiated : Assessment :=
  ⟨fun _ => true, fun _ => false,
   fun q => if q = .science then .entitled else .unsettled⟩

/-- Identical observed performance can have different next intervention outcomes.
Only the chosen action's outcome is recorded; no causal identification is claimed. -/
structure Trials where
  choose : Nat → Bool
  outcome : Nat → Bool → Bool

def SuccessfulRecord (t : Trials) (n : Nat) : Prop :=
  ∀ i, i < n → t.outcome i (t.choose i) = true

def successful : Trials := ⟨fun _ => true, fun _ a => a⟩
def failingAfter (n : Nat) : Trials :=
  ⟨fun _ => true, fun i a => if i < n then a else false⟩

/-- No universal next-case guarantee follows from the finite record alone.
The same theorem applies to habit transitions, predictions or achieved ends. -/
def FiniteUnderdetermination : Prop :=
  ∀ n, ∃ good bad : Trace,
    Recorded good n ∧ Recorded bad n ∧ good n = true ∧ bad n = false

def InterventionUnderdetermination : Prop :=
  ∀ n, SuccessfulRecord successful n ∧ SuccessfulRecord (failingAfter n) n ∧
    successful.outcome n (successful.choose n) = true ∧
    (failingAfter n).outcome n ((failingAfter n).choose n) = false

/-- Conditional internal critiques. These are bridge-explicit transcriptions,
not independent refutations of any historical source commitment. -/
def BridgeConflicts : Prop :=
  (∀ a : Assessment, StrongSkeptic a → CertifiesHabit a → False) ∧
  (∀ a : Assessment, StrongSkeptic a → RelianceRequiresEntitlement a →
    (∃ q, a.relies q = true) → False) ∧
  (∀ (a : Assessment) (sameBasis : Topic → Topic → Prop),
    UniformStandard a sameBasis → ∀ x y, sameBasis x y →
    a.verdict x = .entitled → a.verdict y = .withheld → False)

inductive Question where
  | originOfExpectation | practicalMeansEnds | nonCircularEntitlement
  | necessaryConnection | equalEvidenceStandard
  deriving DecidableEq

/-- A bounded answer profile, using the shared AnswerMap. Answer availability
is explanatory coverage, not the truth of the answer or a complete worldview.
The two supplied propositions are the source commitments, left unproved. -/
def humeReply (custom practice : Prop) : TruthCore.Metaethics.AnswerMap Question where
  answers q := q = .originOfExpectation ∨ q = .practicalMeansEnds
  says q := if q = .originOfExpectation then custom
    else if q = .practicalMeansEnds then practice else False

/-- A critic asks for a normative entitlement account as an additional answer.
No assertion that this account has been delivered by a rival worldview. -/
def entitlementDemand (entitlement : Prop) : TruthCore.Metaethics.AnswerMap Question where
  answers q := q = .nonCircularEntitlement
  says _ := entitlement

def AnswerCoverage : Prop :=
  ∀ custom practice entitlement : Prop,
    (humeReply custom practice).answers .originOfExpectation ∧
    (humeReply custom practice).answers .practicalMeansEnds ∧
    ¬ (humeReply custom practice).answers .nonCircularEntitlement ∧
    ¬ (humeReply custom practice).answers .necessaryConnection ∧
    ¬ (humeReply custom practice).answers .equalEvidenceStandard ∧
    ¬ TruthCore.Metaethics.Matches (humeReply custom practice)
      (entitlementDemand entitlement) .nonCircularEntitlement

/-- A stipulated set of admissible traces; this is not a new modal logic.
Lack of a demonstration does not fix which histories this set contains. -/
def EveryNextAllowed (admissible : Trace → Prop) (n : Nat) : Prop :=
  ∀ b, ∃ f, admissible f ∧ f n = b

/-- Conditional persistence without invariant nature does not guarantee future
habit. Recorded success without a cross-time bridge does not certify reliability. -/
def Checks : Prop :=
  FiniteUnderdetermination ∧ InterventionUnderdetermination ∧ BridgeConflicts ∧
  (∀ q, limited.relies q = true ∧ limited.reasonFounded q = false ∧
    limited.verdict q = .unsettled) ∧
  (StrongSkeptic strong ∧ (∀ q, strong.relies q = true) ∧
    ¬ RelianceRequiresEntitlement strong) ∧
  (UniformStandard differentiated (fun x y => x = y) ∧
    differentiated.verdict .science = .entitled ∧
    differentiated.verdict .theology = .unsettled) ∧
  (ConditionalPersistence (fun t : Nat => t = 0) (fun t => t = 0) ∧
    ¬ ((fun t : Nat => t = 0) 1)) ∧
  (NoDemonstration False ∧
    ¬ EveryNextAllowed (fun f => ∀ i, f i = true) 0) ∧
  AnswerCoverage

end TruthCore.Modern.Hume.Induction
