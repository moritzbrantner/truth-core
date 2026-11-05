module

public import TruthCore.Logic.SelfApplication

/-!
# Reflective coherence and objective epistemic duties

A worldview is an extensional collection of claim-contents. `Semantics` evaluates
contents at worlds, with an interpreted negation. Internal consistency is
satisfiability. Compatibility with a specified duty-content is *joint*
satisfiability; it is not the same as consistency, and it does not assert that
the duty is true. A true duty-content at a designated actual world can make an
otherwise satisfiable worldview false there without making it contradictory.

`OughtAdopt` is an **uninterpreted normative policy** selecting worldviews.
Requiring its selections to be consistent does not entail that they respect any
true objective duty-content. The stronger `TruthDirected` bridge does yield
compatibility, including with necessary implications of the duty. This is a
conditional framework study, not a proof that an objective duty exists, that
truth-directedness is obligatory, or that God exists.
-/

@[expose] public section

namespace TruthCore.Logic.ReflectiveCoherence

open TruthCore.Logic.SelfApplication

/-- Interpret claim contents at worlds. Negation has its usual truth condition,
but the claim type and the worlds carry no further built-in assumptions. -/
structure Semantics (World Claim : Type) where
  trueAt : World → Claim → Prop
  neg : Claim → Claim
  neg_true_iff : ∀ w p, trueAt w (neg p) ↔ ¬ trueAt w p

/-- A worldview is the collection of contents it explicitly includes. -/
abbrev Worldview (Claim : Type) := Claim → Prop

variable {World Claim : Type}

/-- Every accepted worldview-content is true at the same world. -/
def Models (S : Semantics World Claim) (Γ : Worldview Claim) (w : World) : Prop :=
  ∀ p, Γ p → S.trueAt w p

/-- Internal semantic consistency: at least one common model exists. -/
def Consistent (S : Semantics World Claim) (Γ : Worldview Claim) : Prop :=
  ∃ w, Models S Γ w

/-- Necessary consequence relative to this *fixed* semantic profile. -/
def Entails (S : Semantics World Claim) (Γ : Worldview Claim) (p : Claim) : Prop :=
  ∀ w, Models S Γ w → S.trueAt w p

/-- The worldview and the specified content have a common model. -/
def Compatible (S : Semantics World Claim) (Γ : Worldview Claim) (p : Claim) : Prop :=
  ∃ w, Models S Γ w ∧ S.trueAt w p

/-- In every interpreted world, `p` implies `q`. -/
def Follows (S : Semantics World Claim) (p q : Claim) : Prop :=
  ∀ w, S.trueAt w p → S.trueAt w q

/-- The existing self-application norm schema, applied to the consistency of
normatively selected worldviews. -/
def consistencyNorm (S : Semantics World Claim) : Norm (Worldview Claim) :=
  ⟨fun _ => True, Consistent S⟩

/-- A distinct norm: selected worldviews must be jointly satisfiable with the
specified duty-content, which need not be a member of the worldview. -/
def dutyCompatibilityNorm (S : Semantics World Claim) (duty : Claim) :
    Norm (Worldview Claim) :=
  ⟨fun _ => True, fun Γ => Compatible S Γ duty⟩

/-- Explicit extra premise: every worldview that the policy says one ought to
adopt is true at the designated actual world. This is stronger than demanding
consistency alone; neither the premise nor its normative force is derived. -/
def TruthDirected (S : Semantics World Claim) (actual : World)
    (OughtAdopt : Worldview Claim → Prop) : Prop :=
  ∀ Γ, OughtAdopt Γ → Models S Γ actual

/-- The semantic boundary between rejecting an objective duty-content,
contradicting one's own accepted duty-content, and preserving its necessary
implications (`STMT-REFLECTIVE-COHERENCE-BOUNDARY`). -/
def CoherenceBoundary : Prop :=
  ∀ (World Claim : Type) (S : Semantics World Claim),
    (∀ (Γ : Worldview Claim) (duty : Claim),
      Entails S Γ (S.neg duty) → ¬ Compatible S Γ duty) ∧
    (∀ (Γ : Worldview Claim) (duty : Claim),
      Γ duty → Entails S Γ (S.neg duty) → ¬ Consistent S Γ) ∧
    (∀ (Γ : Worldview Claim) (actual : World) (duty : Claim),
      S.trueAt actual duty → Entails S Γ (S.neg duty) → ¬ Models S Γ actual) ∧
    (∀ (Γ : Worldview Claim) (p q : Claim),
      Compatible S Γ p → Follows S p q → Compatible S Γ q)

/-- A conditional, truth-directed version of the user's reflective obligation:
if the duty-content is true at `actual`, and every normatively selected worldview
is true at `actual`, every selected worldview is consistent, compatible with
that duty, and compatible with each of its necessary implications
(`STMT-TRUTH-DIRECTED-REFLECTIVE-DUTY`). -/
def TruthDirectedReflectiveDuty : Prop :=
  ∀ (World Claim : Type) (S : Semantics World Claim) (actual : World)
    (duty : Claim) (OughtAdopt : Worldview Claim → Prop),
    S.trueAt actual duty → TruthDirected S actual OughtAdopt →
      (consistencyNorm S).Holds OughtAdopt ∧
      (dutyCompatibilityNorm S duty).Holds OughtAdopt ∧
      (∀ (Γ : Worldview Claim) (q : Claim),
        OughtAdopt Γ → Follows S duty q → Compatible S Γ q)

/-! ## Finite countermodels to overstrong readings -/

/-- A two-world, two-content interpretation: each world makes exactly its
corresponding Boolean claim true. The designated objective duty-content in the
control below is `true`, and the actual world is also `true`. -/
def twoWorldSemantics : Semantics Bool Bool where
  trueAt w p := w = p
  neg p := !p
  neg_true_iff := by
    intro w p
    cases w <;> cases p <;> decide

/-- The contrary worldview: it explicitly accepts only the negation of the
duty-content, represented by `false`. -/
def deniesDuty : Worldview Bool := fun p => p = false

/-- This stipulated policy selects the contrary worldview and nothing else.
It is a logical control, not an endorsement of the policy. -/
def onlyDenier : Worldview Bool → Prop := fun Γ => Γ = deniesDuty

/-- A one-world interpretation with an empty worldview and an unendorsed
tautological content. It tests entailment versus explicit endorsement. -/
def oneWorldSemantics : Semantics Unit Bool where
  trueAt _ p := p = true
  neg p := !p
  neg_true_iff := by
    intro w p
    cases p <;> decide

/-- An empty worldview need not explicitly contain even what it entails. -/
def emptyWorldview : Worldview Bool := fun _ => False

/-- Together: a policy can select only internally consistent worldviews and
still select one incompatible with a duty true at the actual world; also,
semantic entailment does not force explicit belief in all consequences
(`STMT-REFLECTIVE-COHERENCE-LIMITS`). -/
def ReflectiveCoherenceLimits : Prop :=
  (twoWorldSemantics.trueAt true true ∧
    (consistencyNorm twoWorldSemantics).Holds onlyDenier ∧
    ¬ (dutyCompatibilityNorm twoWorldSemantics true).Holds onlyDenier) ∧
  (Consistent oneWorldSemantics emptyWorldview ∧
    Entails oneWorldSemantics emptyWorldview true ∧
    ¬ emptyWorldview true)

end TruthCore.Logic.ReflectiveCoherence
