module

public import TruthCore.Logic.ExcludedMiddle

/-! Analyst semantics for the face-value/internal-context boundary. Neither old
unbound source statement is identified with a new profile. Content-bearing
assertion and descriptive fact reporting at one discourse are distinct from
truth invariance across discourses. A matched comparison requires the same
apparent content in both. Context is a discourse, not a possible world.
Existing Practice lacks sentence content and assertion/fact-role fields;
Verificationism.Language encodes entailment/observation rather than these
speech roles, so this supplied profile does not silently identify either.
No claim about Phillips' intentions or exhaustive religious-language theories.
-/
@[expose] public section
namespace TruthCore.Alternatives.ReligiousLanguageSemantics

/-- Two supplied discourse positions, false=selected religious setting and
true=comparison setting. Their truth/fact criteria are independent inputs,
not actual context-relative reality postulated as a theorem. -/
structure Profile where
  Sentence : Type
  Content : Type
  Religious : Sentence → Prop
  ApparentContent : Sentence → Content
  HasContent : Bool → Sentence → Content → Prop
  BeliefAssertion : Bool → Sentence → Content → Prop
  FactRepresentation : Bool → Sentence → Content → Prop
  TrueIn : Bool → Sentence → Prop
  FactHoldsIn : Bool → Content → Prop

/-- The selected sentences have their apparent content, assert a belief and
represent a fact, with truth iff that content's fact holds in the selected
setting. This is a local analyst fragment, not a relabelling of the old
historical face-value source proposition. -/
def LocalFaceValue (P : Profile) : Prop :=
  ∀ s, P.Religious s →
    P.HasContent false s (P.ApparentContent s) ∧
    P.BeliefAssertion false s (P.ApparentContent s) ∧
    P.FactRepresentation false s (P.ApparentContent s) ∧
    (P.TrueIn false s ↔ P.FactHoldsIn false (P.ApparentContent s))

/-- Stronger cross-discourse invariance, only where the same selected content
is actually assigned in both settings. General differences elsewhere do not
refute this. Applicability to a theory remains an open analyst bridge. -/
def MatchedTruthUniform (P : Profile) : Prop :=
  ∀ s, P.Religious s → P.HasContent false s (P.ApparentContent s) →
    P.HasContent true s (P.ApparentContent s) →
    (P.TrueIn false s ↔ P.TrueIn true s)

def CrossDiscourseFaceValue (P : Profile) : Prop :=
  LocalFaceValue P ∧ MatchedTruthUniform P

/-- Actual same-content religious comparison witness, not merely different
extensions of 'true' on unrelated scientific/historical sentences. -/
def MatchedReligiousTruthDifference (P : Profile) : Prop :=
  ∃ s, P.Religious s ∧ P.HasContent false s (P.ApparentContent s) ∧
    P.HasContent true s (P.ApparentContent s) ∧
    ((P.TrueIn false s ∧ ¬ P.TrueIn true s) ∨
      (P.TrueIn true s ∧ ¬ P.TrueIn false s))

def CrossDiscourseFaceValueRejected (P : Profile) : Prop :=
  ¬ CrossDiscourseFaceValue P

/-- Local face-value status with actual matched religious truth variation:
an independent analyst configuration, distinct from the uniform sibling. -/
def LocalVariableTruthFaceValue (P : Profile) : Prop :=
  LocalFaceValue P ∧ MatchedReligiousTruthDifference P

/-- Explicit comparison menu; coverage is open without a local-face-value
commitment. It is not a roster of historical schools. -/
def NamedLocalProfilesCover (P : Profile) : Prop :=
  CrossDiscourseFaceValue P ∨
    (LocalFaceValue P ∧ MatchedReligiousTruthDifference P)

/-- Further relevant option outside that menu: the local content/assertion/
fact/truth characterization itself fails. No preferred theory follows. -/
def LocalFaceValueFails (P : Profile) : Prop := ¬ LocalFaceValue P

def ReligiousSemanticCases (P : Profile) : Prop :=
  CrossDiscourseFaceValue P ∨
    (LocalFaceValue P ∧ MatchedReligiousTruthDifference P) ∨ LocalFaceValueFails P

/-- Exact negation of uniform application in the supplied matched scope. -/
def MatchedTruthUniformRejected (P : Profile) : Prop := ¬ MatchedTruthUniform P

def NamedLocalProfilesRejected (P : Profile) : Prop := ¬ NamedLocalProfilesCover P

/-- A difference somewhere need not concern a matched religious sentence. -/
def SomeDiscourseTruthDifference (P : Profile) : Prop :=
  ∃ s, (P.TrueIn false s ∧ ¬ P.TrueIn true s) ∨
    (P.TrueIn true s ∧ ¬ P.TrueIn false s)

/-- Concrete two-sentence constructions: the false constructor names the religious sentence,
the true constructor the unrelated sentence. A flag decides whether belief assertion is present and
whether the religious or unrelated sentence changes truth application. -/
def model (belief : Prop) (religiousDiff : Bool) : Profile where
  Sentence := Bool
  Content := Unit
  Religious s := s = false
  ApparentContent _ := ()
  HasContent _ _ _ := True
  BeliefAssertion _ _ _ := belief
  FactRepresentation _ _ _ := True
  TrueIn context s := context = false ∨ s ≠ religiousDiff
  FactHoldsIn context _ := context = false ∨ false ≠ religiousDiff

/-- Coarse exported controls. The second does not specify whether its truth
variation is on a nonreligious or unmatched sentence; the third does not
identify which local clause fails. The detailed sibling exports those fields. -/
def ReligiousSemanticModels : Prop :=
  (∃ P : Profile, LocalFaceValue P ∧ MatchedReligiousTruthDifference P ∧
    CrossDiscourseFaceValueRejected P) ∧
  (∃ P : Profile, CrossDiscourseFaceValue P ∧ SomeDiscourseTruthDifference P ∧
    ¬ MatchedReligiousTruthDifference P) ∧
  (∃ P : Profile, MatchedTruthUniform P ∧ LocalFaceValueFails P)
/-- A substantive local descriptive-role objection: an actual religious
sentence does not represent its apparent-content fact in the selected setting.
This is stronger than merely saying religious concepts have internal uses. -/
def NonDescriptiveReligiousWitness (P : Profile) : Prop :=
  ∃ s, P.Religious s ∧ ¬ P.FactRepresentation false s (P.ApparentContent s)

def NonDescriptiveReligiousModel : Prop :=
  ∃ P : Profile, NonDescriptiveReligiousWitness P ∧ MatchedTruthUniform P ∧
    LocalFaceValueFails P
/-- An actual religious sentence has the selected content assigned in both
settings, so an invariance control need not rely on an empty matched scope. -/
def MatchedReligiousSentenceExists (P : Profile) : Prop :=
  ∃ s, P.Religious s ∧ P.HasContent false s (P.ApparentContent s) ∧
    P.HasContent true s (P.ApparentContent s)

def NonReligiousTruthDifference (P : Profile) : Prop :=
  ∃ s, ¬ P.Religious s ∧
    ((P.TrueIn false s ∧ ¬ P.TrueIn true s) ∨
      (P.TrueIn true s ∧ ¬ P.TrueIn false s))

def NonBeliefReligiousWitness (P : Profile) : Prop :=
  ∃ s, P.Religious s ∧ ¬ P.BeliefAssertion false s (P.ApparentContent s)

/-- The three local clauses other than belief assertion, without asserting
its presence or absence. Combined with NonBeliefReligiousWitness below. -/
def LocalExceptBelief (P : Profile) : Prop :=
  ∀ s, P.Religious s → P.HasContent false s (P.ApparentContent s) ∧
    P.FactRepresentation false s (P.ApparentContent s) ∧
    (P.TrueIn false s ↔ P.FactHoldsIn false (P.ApparentContent s))

/-- The three local clauses other than descriptive representation. -/
def LocalExceptDescription (P : Profile) : Prop :=
  ∀ s, P.Religious s → P.HasContent false s (P.ApparentContent s) ∧
    P.BeliefAssertion false s (P.ApparentContent s) ∧
    (P.TrueIn false s ↔ P.FactHoldsIn false (P.ApparentContent s))

/-- A consistency check on the supplied dictionary: truth agrees with the
corresponding fact criterion whenever that content is assigned. It is a model
property, not an independent truth theory or actual-world applicability claim. -/
def AssignedTruthTracksFact (P : Profile) : Prop :=
  ∀ context s content, P.HasContent context s content →
    (P.TrueIn context s ↔ P.FactHoldsIn context content)

/-- Content is the sentence's Boolean identifier. Roles can fail separately,
while truth tracks the actual assigned content's criterion in each setting. -/
def detailedModel (belief descriptive : Prop) (religiousDiff : Bool) : Profile where
  Sentence := Bool
  Content := Bool
  Religious s := s = false
  ApparentContent s := s
  HasContent _ s content := content = s
  BeliefAssertion _ s content := belief ∧ content = s
  FactRepresentation _ s content := descriptive ∧ content = s
  TrueIn context s := context = false ∨ s ≠ religiousDiff
  FactHoldsIn context content := context = false ∨ content ≠ religiousDiff

/-- Four stronger controls export every advertised distinction: actual
matched religious content, explicitly nonreligious variation, and isolated
belief/descriptive-role failures with the other local clauses retained. -/
def DetailedReligiousSemanticModels : Prop :=
  (∃ P : Profile, AssignedTruthTracksFact P ∧ LocalFaceValue P ∧
    MatchedReligiousTruthDifference P ∧ CrossDiscourseFaceValueRejected P) ∧
  (∃ P : Profile, AssignedTruthTracksFact P ∧ CrossDiscourseFaceValue P ∧
    MatchedReligiousSentenceExists P ∧ NonReligiousTruthDifference P ∧
    ¬ MatchedReligiousTruthDifference P) ∧
  (∃ P : Profile, AssignedTruthTracksFact P ∧ MatchedTruthUniform P ∧
    MatchedReligiousSentenceExists P ∧ LocalExceptBelief P ∧
    NonBeliefReligiousWitness P ∧ LocalFaceValueFails P) ∧
  (∃ P : Profile, AssignedTruthTracksFact P ∧ MatchedTruthUniform P ∧
    MatchedReligiousSentenceExists P ∧ LocalExceptDescription P ∧
    NonDescriptiveReligiousWitness P ∧ LocalFaceValueFails P)
end TruthCore.Alternatives.ReligiousLanguageSemantics
