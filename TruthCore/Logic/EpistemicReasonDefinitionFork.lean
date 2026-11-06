module

public import TruthCore.Logic.EpistemicReasons
public import TruthCore.Logic.ExcludedMiddle

/-!
# Competing interpretations of epistemic reasons (#930)

The thin F6 relation stays unchanged. `Frame` separates a content's truth,
consideration-based reason attribution, epistemic favoring, belief production,
reward, and pro tanto force. Favoring and force are independently interpreted
framework inputs: the structure does not derive warrant from a psychological
cause, payoff, or accuracy measure. The count/reassurance controls below test
conditional accounts; they establish no actual instance or authority.

The four calibration propositions are candidate meanings, not a stipulated
exhaustive history of epistemology. Their named coverage is an explicit open
premise. The remainder means none of these calibrations describes the selected
reason attribution; it is not inferred from a failed source or proof search.
Preference changes vary only a supplied preference coordinate, with subject,
consideration, target, and circumstances fixed. They are not an assertion that
every psychological or metaphysical possibility has been enumerated.
-/

@[expose] public section

namespace TruthCore.Logic.EpistemicReasonDefinitionFork

open TruthCore.Logic.EpistemicReasons

structure Frame where
  Agent : Type
  Consideration : Type
  Content : Type
  Attitude : Type
  Preference : Type
  about : Attitude → Content
  believe : Content → Attitude
  beliefAbout : ∀ p, about (believe p) = p
  Reason : Agent → Content → Prop
  CountsAsReason : Agent → Consideration → Attitude → Prop
  assessable : Content → Prop
  applies : Agent → Consideration → Attitude → Prop
  favors : Agent → Consideration → Attitude → Prop
  Holds : Content → Prop
  produces : Agent → Consideration → Attitude → Prop
  rewards : Agent → Consideration → Attitude → Prop
  force : Agent → Consideration → Attitude → Preference → Prop
  actualPreference : Agent → Preference

/-- The consideration-based presentation of the original belief-reason relation.
It is explicit because thin F6 itself contains no consideration coordinate. -/
def ConsiderationPresentation (f : Frame) : Prop :=
  ∀ a p, f.Reason a p ↔ ∃ r, f.CountsAsReason a r (f.believe p)

/-- Favorable bearing under the independently interpreted epistemic standard.
No factivity, production, reward, or preference-independent force is added. -/
def EpistemicRole (f : Frame) (a : f.Agent) (r : f.Consideration) (t : f.Attitude) : Prop :=
  f.assessable (f.about t) ∧ f.applies a r t ∧ f.favors a r t

/-- An attributed reason that actually meets the proposed ordinary role. -/
def OrdinaryInstance (f : Frame) (a : f.Agent) (r : f.Consideration) (t : f.Attitude) : Prop :=
  f.CountsAsReason a r t ∧ EpistemicRole f a r t

def SomeOrdinaryReason (f : Frame) : Prop := ∃ a r t, OrdinaryInstance f a r t

/-- All supplied preference alternatives are evaluated with the other inputs
fixed. Since actualPreference is supplied, actual force is included. -/
def IndependentInstance (f : Frame) (a : f.Agent) (r : f.Consideration) (t : f.Attitude) : Prop :=
  OrdinaryInstance f a r t ∧ ∀ d, f.force a r t d

def SomePreferenceIndependentReason (f : Frame) : Prop :=
  ∃ a r t, IndependentInstance f a r t

/-- Ordinary-role analysis of attributed reasons. This is a proposition about
independent fields, not a definition replacing the original F6 relation. -/
def OrdinaryDefinition (f : Frame) : Prop :=
  ∀ a r t, f.CountsAsReason a r t ↔ EpistemicRole f a r t

/-- Strong authority analysis. Its coextension with attributed reasons need
not follow from the ordinary analysis. -/
def PreferenceIndependentDefinition (f : Frame) : Prop :=
  ∀ a r t, f.CountsAsReason a r t ↔
    (EpistemicRole f a r t ∧ ∀ d, f.force a r t d)

/-- Bare production analysis, tested rather than attributed to naturalism as a
whole. Naturalistic accounts may also represent favorable epistemic bearing. -/
def ProductionDefinition (f : Frame) : Prop :=
  ∀ a r t, f.CountsAsReason a r t ↔
    (f.assessable (f.about t) ∧ f.applies a r t ∧ f.produces a r t)

/-- Bare reward analysis. A reward can be informative in a richer account;
this analysis by itself supplies no epistemic-bearing bridge. -/
def RewardDefinition (f : Frame) : Prop :=
  ∀ a r t, f.CountsAsReason a r t ↔
    (f.assessable (f.about t) ∧ f.applies a r t ∧ f.rewards a r t)

def ProductionDefinitionFails (f : Frame) : Prop := ¬ ProductionDefinition f

def RewardDefinitionFails (f : Frame) : Prop := ¬ RewardDefinition f

/-- Coverage of the four stated calibrations, an openly additional assumption. -/
def NamedDefinitionCoverage (f : Frame) : Prop :=
  OrdinaryDefinition f ∨ PreferenceIndependentDefinition f ∨
    ProductionDefinition f ∨ RewardDefinition f

/-- A precise remaining interpretation in this fixed comparison profile. -/
def RemainingDefinition (f : Frame) : Prop :=
  ¬ OrdinaryDefinition f ∧ ¬ PreferenceIndependentDefinition f ∧
    ¬ ProductionDefinition f ∧ ¬ RewardDefinition f

/-- Structural coverage of named calibrations or their explicit remainder.
This does not prove the stronger named-coverage hypothesis. -/
def DefinitionFork : Prop :=
  ∀ f : Frame, NamedDefinitionCoverage f ∨ RemainingDefinition f

inductive Consideration | count | reassurance deriving DecidableEq
inductive Content | even | rain deriving DecidableEq
inductive Preference | accuracy | comfort deriving DecidableEq

/-- A toy count favors the even answer; reassurance produces/rewards that
answer without that favorable bearing. Truth is separate, permitting error. -/
def goalRelative : Frame where
  Agent := Unit
  Consideration := Consideration
  Content := Content
  Attitude := Content
  Preference := Preference
  about := fun t => t
  believe := fun p => p
  beliefAbout := fun _ => rfl
  Reason := fun _ p => p = .even
  CountsAsReason := fun _ r t => r = .count ∧ t = .even
  assessable := fun _ => True
  applies := fun _ _ _ => True
  favors := fun _ r t => r = .count ∧ t = .even
  Holds := fun p => p = .rain
  produces := fun _ r t => r = .reassurance ∧ t = .even
  rewards := fun _ r t => r = .reassurance ∧ t = .even
  force := fun _ r t d => r = .count ∧ t = .even ∧ d = .accuracy
  actualPreference := fun _ => .accuracy

/-- The empirical/support data of goalRelative with only force changed. -/
def independent : Frame :=
  { goalRelative with force := fun _ r t _ => r = .count ∧ t = .even }

/-- A bare production/reward analysis attributes reassurance rather than the
count as the reason. The support interpretation stays fixed. -/
def bareProduction : Frame :=
  { goalRelative with CountsAsReason := fun _ r t => r = .reassurance ∧ t = .even }

/-- Coextensive functional, production, reward and independent-force accounts
are compatible in this interpretation; no property identity follows. -/
def compatible : Frame :=
  { independent with
      produces := fun _ r t => r = .count ∧ t = .even
      rewards := fun _ r t => r = .count ∧ t = .even }

/-- A thin nonempty attribution with no favoring, production, reward or force:
it lies outside all four named calibrations. -/
def remaining : Frame :=
  { goalRelative with
      favors := fun _ _ _ => False
      produces := fun _ _ _ => False
      rewards := fun _ _ _ => False
      force := fun _ _ _ _ => False }

/-- Missing presentation, not failure of ordinary calibration: no attributed
consideration is supplied although the original thin relation is nonempty. -/
def unpresented : Frame :=
  { remaining with CountsAsReason := fun _ _ _ => False }

/-- Export the actual profiles whose properties are certified, retaining the
Force-only update and the differing consideration coordinates. These are
analyst finite interpretations, not actual epistemic/normative instances. -/
def BoundaryCertificate : Prop :=
  (ConsiderationPresentation goalRelative ∧ OrdinaryDefinition goalRelative ∧
    ThereAreEpistemicReasons goalRelative.Reason ∧ SomeOrdinaryReason goalRelative ∧
    ¬ SomePreferenceIndependentReason goalRelative ∧
    (∃ a r t, OrdinaryInstance goalRelative a r t ∧
      goalRelative.force a r t (goalRelative.actualPreference a)) ∧
    (∃ a r t, OrdinaryInstance goalRelative a r t ∧
      ¬ goalRelative.produces a r t ∧ ¬ goalRelative.Holds (goalRelative.about t))) ∧
  (SomePreferenceIndependentReason independent ∧ OrdinaryDefinition independent ∧
    PreferenceIndependentDefinition independent) ∧
  (ConsiderationPresentation bareProduction ∧ ProductionDefinition bareProduction ∧
    RewardDefinition bareProduction ∧ ThereAreEpistemicReasons bareProduction.Reason ∧
    ¬ SomeOrdinaryReason bareProduction) ∧
  (OrdinaryDefinition compatible ∧ PreferenceIndependentDefinition compatible ∧
    ProductionDefinition compatible ∧ RewardDefinition compatible) ∧
  (ConsiderationPresentation remaining ∧ ThereAreEpistemicReasons remaining.Reason ∧
    RemainingDefinition remaining ∧ ¬ NamedDefinitionCoverage remaining ∧
    ¬ SomeOrdinaryReason remaining) ∧
  (OrdinaryDefinition unpresented ∧ ThereAreEpistemicReasons unpresented.Reason ∧
    ¬ ConsiderationPresentation unpresented ∧ ¬ SomeOrdinaryReason unpresented)

end TruthCore.Logic.EpistemicReasonDefinitionFork
