module

public import TruthCore.Causality.NamingVeracityBatch1

/-! Two alternative assertion-truth routes and their explicit lower warrant tree.
Analyst formulations; source discussion and semantic burdens are in
`docs/notes/divine-veracity-1410.md`. No attribute field is unfolded, and
`Knows` remains nonfactive. Every attitude concerns the same speaker and Prop;
all Prop is a negation-closed domain. No ability or permission-of-error claim. -/

@[expose] public section
namespace TruthCore.Causality.DivineVeracity1410
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Causality.NamingVeracityBatch1

/-- Primitive normative/cognitive interface, not automatic divine attributes.
Permitted: asserting this proposition is morally permissible in the fixed context.
Defect: this assent is a cognitive defect. Present: this content actually obtains
and is present to this intellect (not merely possible). Apprehends: actual
intellectual presentation of that content, with neither factivity nor assent built in.
Application, analogical divine use and representation are explicit OPEN burdens. -/
structure Grounds (σ : Signature) where
  Permitted : σ.Being → Prop → Prop
  Defect : σ.Being → Prop → Prop
  Present : σ.Being → Prop → Prop
  Apprehends : σ.Being → Prop → Prop

/-- Every genuine assertion on its own authority by a GOD_4 with classical attributes is true. -/
def GodAssertsOnlyTruth (σ : Signature) (V : Veracity σ) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ p, V.Asserts g p → p

/-- Such a GOD_4 actually assents to every proposition it genuinely asserts; suspension is excluded. -/
def GodSincere (σ : Signature) (V : Veracity σ) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ p, V.Asserts g p → V.Believes g p

/-- Every actual assent of such a GOD_4 is true; not factivity by definition. -/
def GodAssentAccurate (σ : Signature) (V : Veracity σ) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ p, V.Believes g p → p

/-- Such a GOD_4 actually assents to every true Prop, including contingent contents and negations; an unrestricted OPEN application. -/
def GodTruthComplete (σ : Signature) (V : Veracity σ) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ p, p → V.Believes g p

/-- Weakest completeness used by Route B: only the negations of actual asserted
contents, and only when those negations are true. No claims about other truths. -/
def GodCounterAssertionComplete (σ : Signature) (V : Veracity σ) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ p,
    V.Asserts g p → ¬ p → V.Believes g (¬ p)

/-- Such a GOD_4 never genuinely asserts p while assenting to not-p; does not exclude suspension. -/
def GodNoContraryAssertion (σ : Signature) (V : Veracity σ) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ p, V.Asserts g p → ¬ V.Believes g (¬ p)

/-- Such a GOD_4 has no opposed pair of assents for the same Prop; no factivity built in. -/
def GodAssentConsistent (σ : Signature) (V : Veracity σ) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ p, V.Believes g p → ¬ V.Believes g (¬ p)

/-- Such a GOD_4 holds every actual assent as known; separate OPEN bridge to the older nonfactive Knows route. -/
def GodAssentHeldKnown (σ : Signature) (V : Veracity σ) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ p, V.Believes g p → V.Knows g p

/-- Every actual genuine divine assertion is morally permissible in the fixed context; OPEN applicability, not causal goodness. -/
def GodAssertionsPermitted (σ : Signature) (V : Veracity σ) (G : Grounds σ) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ p, V.Asserts g p → G.Permitted g p

/-- OPEN positive endorsement norm: morally permitted assertion of p requires actual assent to p, ruling out unsupported assertion during suspension. -/
def PermittedAssertionEndorsed (σ : Signature) (V : Veracity σ) (G : Grounds σ) : Prop :=
  ∀ g p, G.Permitted g p → V.Believes g p

/-- OPEN act-object norm: assent to not-p makes genuine assertion of p impermissible, even for a beneficial further end. -/
def ContraryAssertionImpermissible (σ : Signature) (V : Veracity σ) (G : Grounds σ) : Prop :=
  ∀ g p, V.Believes g (¬ p) → ¬ G.Permitted g p

/-- OPEN cognitive-good norm: actual false assent is a cognitive defect; independent of the label knowledge. -/
def FalseAssentDefective (σ : Signature) (V : Veracity σ) (G : Grounds σ) : Prop :=
  ∀ g p, V.Believes g p → ¬ p → G.Defect g p

/-- OPEN applicability: no assent-content cognitive defect belongs to such a GOD_4. Primitive classical attributes alone do not prove this. -/
def GodDefectFree (σ : Signature) (V : Veracity σ) (G : Grounds σ) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ p, ¬ G.Defect g p

/-- OPEN actuality/presentiality bridge: every true Prop is actually present to this same GOD_4 intellect; possibility and generic causal power do not suffice. -/
def GodTruthPresent (σ : Signature) (V : Veracity σ) (G : Grounds σ) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ p, p → G.Present g p

/-- OPEN cognitive access: actually present content is intellectually apprehended by the same speaker; mere truth matching does not prove this. -/
def PresenceApprehended (σ : Signature) (V : Veracity σ) (G : Grounds σ) : Prop :=
  ∀ g p, G.Present g p → G.Apprehends g p

/-- OPEN representation-to-judgment bridge: actual apprehension of the selected propositional content yields assent to it, not merely entertaining an enunciation. -/
def ApprehensionAssented (σ : Signature) (V : Veracity σ) (G : Grounds σ) : Prop :=
  ∀ g p, G.Apprehends g p → V.Believes g p

namespace Control
open TruthCore.Causality.NamingVeracityBatch1.Control
abbrev σ : Signature := sig True True (fun p => p)
def v (a b : Prop → Prop) : Veracity σ := veracity True True (fun p => p) a b (fun p => p)
def grounds : Grounds σ where
  Permitted _ p := p
  Defect _ _ := False
  Present _ p := p
  Apprehends _ p := p
/-- Structural sample: a classified divine bearer genuinely asserts True; all
lower branches hold together. Truth matching is a satisfiability witness,
not an explanation or a historically possible divine cognition. -/
def Joint : Prop :=
  σ.IsGod true ∧ σ.HasClassicalAttributes true ∧ (v id id).Asserts true True ∧
  GodAssertionsPermitted σ (v id id) grounds ∧
  PermittedAssertionEndorsed σ (v id id) grounds ∧
  ContraryAssertionImpermissible σ (v id id) grounds ∧
  FalseAssentDefective σ (v id id) grounds ∧ GodDefectFree σ (v id id) grounds ∧
  GodTruthPresent σ (v id id) grounds ∧ PresenceApprehended σ (v id id) grounds ∧
  ApprehensionAssented σ (v id id) grounds ∧ GodAssentHeldKnown σ (v id id) ∧
  GodTruthComplete σ (v id id) ∧ GodAssentConsistent σ (v id id)
/-- Four omission models plus the suspension distinction. Each model retains
an existing GOD_4-classified bearer; these are interpretations of the skeleton,
not models of all independently proposed classical divine perfections. -/
def Omissions : Prop :=
  (∃ V : Veracity σ, GodAssentAccurate σ V ∧ ¬ GodAssertsOnlyTruth σ V) ∧
  (∃ V : Veracity σ, GodSincere σ V ∧ ¬ GodAssertsOnlyTruth σ V) ∧
  (∃ V : Veracity σ, GodNoContraryAssertion σ V ∧ ¬ GodAssertsOnlyTruth σ V) ∧
  (∃ V : Veracity σ, GodTruthComplete σ V ∧ GodAssentAccurate σ V ∧
    GodAssentConsistent σ V ∧ ¬ GodAssertsOnlyTruth σ V) ∧
  (∃ V : Veracity σ, GodNoContraryAssertion σ V ∧ ¬ GodSincere σ V)
/-- The strongest cognitive branch can coexist with permission for a false
assertion when the contrary-sign norm is absent. Benefit is not encoded: the
sample isolates the normative gap, not the warrant of a consequence ethic. -/
def PermissiveRival : Prop :=
  ∃ V : Veracity σ, ∃ G : Grounds σ,
    GodTruthComplete σ V ∧ GodAssentAccurate σ V ∧ GodAssentConsistent σ V ∧
    GodAssertionsPermitted σ V G ∧ ¬ ContraryAssertionImpermissible σ V G ∧
    ¬ GodAssertsOnlyTruth σ V

def Certificate : Prop := Joint ∧ Omissions ∧ PermissiveRival
end Control
end TruthCore.Causality.DivineVeracity1410
