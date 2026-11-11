module

public import TruthCore.Logic.EpistemicReasons

/-!
An analyst formulation of an internal reason to adopt a view. A reason
relation represents the reasons admitted by one interpretation. A kind selects
both the norm and the attitude at issue, for example a moral reason to adopt a
position in practice or an epistemic reason to believe it. The reason relation
is primitive: the model supplies no account of warrant, motivation or what
ultimately settles adoption.
-/

@[expose] public section

namespace TruthCore.Metaethics.AdoptionReasons
open TruthCore.Logic.EpistemicReasons

/-- No reason of the selected kind exists for any agent or target. -/
def NoReasonsOfKind {Kind Agent Target : Type}
    (reason : Kind → Agent → Target → Prop) (kind : Kind) : Prop :=
  ∀ agent target, ¬ reason kind agent target

/-- There are no normative reasons in any represented kind. A philosophically
global reading requires a domain covering all normative reasons. -/
def GlobalNormativeNihilism {Kind Agent Target : Type}
    (reason : Kind → Agent → Target → Prop) : Prop :=
  ∀ kind, NoReasonsOfKind reason kind

/-- The interpretation supplies nobody a reason of the selected kind to adopt
the selected view, in the sense of adoption appropriate to that kind. -/
def NoInternalAdoptionReason {Kind Agent Target : Type}
    (reason : Kind → Agent → Target → Prop) (kind : Kind) (view : Target) : Prop :=
  ∀ agent, ¬ reason kind agent view

/-- No represented reason kind supplies any agent a reason to adopt the view. -/
def NoInternalAdoptionReasonOfAnyKind {Kind Agent Target : Type}
    (reason : Kind → Agent → Target → Prop) (view : Target) : Prop :=
  ∀ kind, NoInternalAdoptionReason reason kind view

/-- An interpretation cannot satisfy the denial of reasons in all its kinds. -/
def GlobalNormativeNihilismExcluded {Kind Agent Target : Type}
    (reason : Kind → Agent → Target → Prop) : Prop :=
  ¬ GlobalNormativeNihilism reason

/-- In a two-kind profile with an agent and two targets, denying all moral
reasons can be true at the target that has an epistemic reason. -/
def MoralDenialEpistemicAdoptionControl : Prop :=
  ∃ (reason : Bool → Unit → Bool → Prop) (Holds : Bool → Prop),
    (Holds true ↔ NoReasonsOfKind reason false) ∧
    Holds true ∧
    NoInternalAdoptionReason reason false true ∧
    reason true () true ∧
    ThereAreEpistemicReasons (reason true)

end TruthCore.Metaethics.AdoptionReasons
