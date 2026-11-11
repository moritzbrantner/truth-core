module

public import TruthCore.Logic.CogitoSubject
public import TruthCore.Logic.EpistemicReasons
public import TruthCore.Logic.PerformedDenial

/-!
# Assertion and the witnesses a universal denial excludes

Analyst formulations with attribution deferred. Assertion, belief, cognitive
meaning, episode occurrence and represented existence have separate
interpretations. The local bridges below need only the selected content,
rather than a norm for every speech act or a theory of truth. The assertion
relation is a primitive for use of a content in an actual assertion; no
truth, belief, mental realization or ontic consequence is built into it.
-/

@[expose] public section

namespace TruthCore.Logic.AssertionRetorsion

open TruthCore.Logic.CogitoSubject (ThoughtOccurs)
open TruthCore.Logic.EpistemicReasons (ThereAreEpistemicReasons)
open TruthCore.Logic.PerformedDenial (NoEpisodeOccurs)

variable {Agent Content Episode Being : Type}

/-- Someone actually asserts the selected content. -/
def AssertionMade (Asserts : Agent → Content → Prop) (claim : Content) : Prop :=
  ∃ a, Asserts a claim

/-- Local cognitive realization bridge: each assertion of the selected content
has a realizing, occurring thought episode. `Realizes` tracks the same agent
and content; an unrelated episode does not satisfy the intended bridge. -/
def AssertionRealized (Asserts : Agent → Content → Prop) (claim : Content)
    (Occurs : Episode → Prop) (Realizes : Agent → Content → Episode → Prop) : Prop :=
  ∀ a, Asserts a claim → ∃ e, Occurs e ∧ Realizes a claim e

/-- Local phenomenal bridge: for this content, each occurring thought that
realizes an assertion by an agent is experienced. The phenomenal classification
is primitive; an unconscious realization is an omission case. -/
def AssertionRealizationsExperienced (Asserts : Agent → Content → Prop) (claim : Content)
    (Occurs Experienced : Episode → Prop) (Realizes : Agent → Content → Episode → Prop) : Prop :=
  ∀ a e, Asserts a claim → Occurs e → Realizes a claim e → Experienced e

/-- There is phenomenal experience among the supplied episodes. Candidates
classified as experienced count only if they occur. -/
def ExperienceOccurs (Occurs Experienced : Episode → Prop) : Prop :=
  ∃ e, Occurs e ∧ Experienced e

/-- No occurring episode has the phenomenal property under consideration. -/
def NoExperienceOccurs (Occurs Experienced : Episode → Prop) : Prop :=
  ¬ ExperienceOccurs Occurs Experienced

/-- Selected existence interpretation: each occurring thought episode is
represented by an existing candidate. Applying this at a world requires
interpreting `ExistsIn` as that world's existence predicate and `represent`
as mapping episodes to their own representatives. -/
def OccurringThoughtIsRepresentedAsExisting (Occurs : Episode → Prop) (ExistsIn : Being → Prop)
    (represent : Episode → Being) : Prop :=
  ∀ e, Occurs e → ExistsIn (represent e)

/-- The existence extension is inhabited. Candidate-domain membership by
itself has no existential import about the selected interpretation. -/
def SomeExistent (ExistsIn : Being → Prop) : Prop :=
  ∃ b, ExistsIn b

/-- No candidate is in the existence extension of this interpretation. -/
def NothingExistsIn (ExistsIn : Being → Prop) : Prop :=
  ¬ SomeExistent ExistsIn

/-- A local constitutive requirement for assertion in the cognitive sense:
assertion of this content requires its cognitive meaningfulness. No truth or
verification criterion is included. -/
def AssertedContentIsMeaningful (Asserts : Agent → Content → Prop) (claim : Content)
    (Meaningful : Content → Prop) : Prop :=
  ∀ a, Asserts a claim → Meaningful claim

/-- Some content in the supplied domain has cognitive significance. -/
def SomeMeaningfulContent (Meaningful : Content → Prop) : Prop :=
  ∃ c, Meaningful c

/-- The supplied domain contains no cognitively meaningful content. -/
def NoMeaningfulContent (Meaningful : Content → Prop) : Prop :=
  ¬ SomeMeaningfulContent Meaningful

/-- Local sincerity bridge: every agent who asserts this content believes that
same content. Asserts and Believes are independent relations before the bridge
is imposed. The bridge can fail for insincere or merely conventional speech. -/
def AssertedContentIsBelieved (Asserts Believes : Agent → Content → Prop) (claim : Content) :
    Prop :=
  ∀ a, Asserts a claim → Believes a claim

/-- Some agent believes some content. The belief relation is primitive. -/
def SomeBelief (Believes : Agent → Content → Prop) : Prop :=
  ∃ a c, Believes a c

/-- There is no belief among the supplied agents and contents. -/
def NoBeliefs (Believes : Agent → Content → Prop) : Prop :=
  ¬ SomeBelief Believes

/-- When the domain includes Lean propositions, this agent asserts the very
proposition that there are no beliefs. -/
def NoBeliefsIsAsserted (Asserts Believes : Agent → Prop → Prop) : Prop :=
  AssertionMade Asserts (NoBeliefs Believes)

/-- Sincerity on this denial alone. -/
def NoBeliefsAssertionIsSincere (Asserts Believes : Agent → Prop → Prop) : Prop :=
  AssertedContentIsBelieved Asserts Believes (NoBeliefs Believes)

/-- In the same one-agent interpretation, the no-beliefs denial is asserted,
there are no beliefs, and the agent has an epistemic reason to believe that
very denial. F6 follows in this interpretation without any actual belief. -/
def AssertionWithoutBeliefControl : Prop :=
  ∃ (Asserts Believes Reason : Unit → Prop → Prop),
    NoBeliefsIsAsserted Asserts Believes ∧
    NoBeliefs Believes ∧
    Reason () (NoBeliefs Believes) ∧
    ThereAreEpistemicReasons Reason ∧
    ¬ NoBeliefsAssertionIsSincere Asserts Believes

/-- The same putative assertion can be marked as uttered under an empty
cognitive-meaning interpretation when the cognitive bridge is omitted.
This models a speech marker used for assertion, without demonstrating that
such a marker would count as a genuine assertion. -/
def SpeechMarkerWithoutMeaningControl : Prop :=
  ∃ (Asserts : Unit → Unit → Prop) (Meaningful : Unit → Prop),
    AssertionMade Asserts () ∧
    NoMeaningfulContent Meaningful ∧
    ¬ AssertedContentIsMeaningful Asserts () Meaningful

/-- A speech marker alone can leave the thought interpretation empty. -/
def AssertionWithoutThoughtControl : Prop :=
  ∃ (Asserts : Unit → Unit → Prop) (Occurs : Unit → Prop) (Realizes : Unit → Unit → Unit → Prop),
    AssertionMade Asserts () ∧ NoEpisodeOccurs Occurs ∧
    ¬ AssertionRealized Asserts () Occurs Realizes

/-- A thought can realize an assertion while no episode is experienced.
Even an existing representative of that thought does not settle this issue. -/
def UnexperiencedRealizationControl : Prop :=
  ∃ (Asserts : Unit → Unit → Prop) (Occurs Experienced ExistsIn : Unit → Prop)
    (Realizes : Unit → Unit → Unit → Prop) (represent : Unit → Unit),
    AssertionMade Asserts () ∧
    AssertionRealized Asserts () Occurs Realizes ∧
    OccurringThoughtIsRepresentedAsExisting Occurs ExistsIn represent ∧
    NoExperienceOccurs Occurs Experienced ∧
    ¬ AssertionRealizationsExperienced Asserts () Occurs Experienced Realizes

/-- A thought occurs but its candidate does not belong to the existence
extension. This models omission of the representation bridge. -/
def OccurrenceWithoutExistenceControl : Prop :=
  ∃ (Occurs ExistsIn : Unit → Prop) (represent : Unit → Unit),
    ThoughtOccurs Occurs ∧ NothingExistsIn ExistsIn ∧
    ¬ OccurringThoughtIsRepresentedAsExisting Occurs ExistsIn represent

/-- The five omission interpretations above. -/
def OmissionControls : Prop :=
  AssertionWithoutBeliefControl ∧ SpeechMarkerWithoutMeaningControl ∧
    AssertionWithoutThoughtControl ∧ UnexperiencedRealizationControl ∧
    OccurrenceWithoutExistenceControl

end TruthCore.Logic.AssertionRetorsion
