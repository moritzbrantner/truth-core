module

/-! Analyst configuration for the historical/per-se distinction. Times date
original generation; response y x is x's present power after removing y AFTER
generation. It is not the result of preventing x's generation. This selected
removal response is a primitive supplied table, not a counterfactual semantics.
The clock imposes strict precedence only on historical edges. Neither relation
is assumed transitive, total, well-founded or exhaustive. No infinity follows.
The source per-accidens reading remains open and is not identified with this
configuration. Father/son motivates H; a sustaining instrument motivates E;
ordinary examples satisfy these tables only via an OPEN applicability bridge. -/
@[expose] public section
namespace TruthCore.Causality.HistoricalRemoval

structure Profile (B : Type) where
  generated : B → Nat
  historical : B → B → Prop
  essential : B → B → Prop
  power : B → Bool
  response : B → B → Bool

def Temporal {B : Type} (p : Profile B) : Prop :=
  ∀ y x, p.historical y x → p.generated y < p.generated x

def Independent {B : Type} (p : Profile B) : Prop :=
  ∀ y x, p.historical y x → p.power x = true ∧ p.response y x = true

def Loss {B : Type} (p : Profile B) : Prop :=
  ∀ y x, p.essential y x → p.power x = true ∧ p.response y x = false

def Dictionary {B : Type} (p : Profile B) : Prop :=
  ∀ y x, p.historical y x → p.essential y x

inductive Node where
  | past | present | sustainer
  deriving DecidableEq

instance (p : Node → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  match (inferInstance : Decidable (p Node.past)),
    (inferInstance : Decidable (p Node.present)),
    (inferInstance : Decidable (p Node.sustainer)) with
  | .isTrue h0, .isTrue h1, .isTrue h2 => .isTrue (fun x =>
      match x with
      | .past => h0
      | .present => h1
      | .sustainer => h2)
  | .isFalse h, _, _ => .isFalse (fun hall => h (hall .past))
  | _, .isFalse h, _ => .isFalse (fun hall => h (hall .present))
  | _, _, .isFalse h => .isFalse (fun hall => h (hall .sustainer))

open Node

/-- Finite supplied response tables: 0 generates 1; 2 sustains 1.
With conflation enabled 0 also sustains 1. Selecting the response at (0,1)
compares retaining independence with retaining essential loss. -/
def sample (conflate survive : Bool) : Profile Node where
  generated := fun x => match x with | .past => 0 | .present => 1 | .sustainer => 2
  historical := fun y x => y = past ∧ x = present
  essential := fun y x => (y = sustainer ∧ x = present) ∨ (conflate = true ∧ y = past ∧ x = present)
  power := fun _ => true
  response := fun y x => if y = past ∧ x = present then survive else false

/-- Universal incompatibility, a nonempty separated configuration, and two
omission controls. Temporal order alone never selects the removal response.
These are finite analyst tables, not possible histories or independent warrant. -/
def Comparison : Prop :=
  (∀ (B : Type) (p : Profile B), Independent p → Loss p → Dictionary p →
    ∀ y x, ¬ p.historical y x) ∧
  (Temporal (sample false true) ∧ Independent (sample false true) ∧
    Loss (sample false true) ∧ ¬ Dictionary (sample false true) ∧
    (sample false true).historical past present ∧ (sample false true).essential sustainer present) ∧
  (Temporal (sample true false) ∧ Loss (sample true false) ∧
    Dictionary (sample true false) ∧ ¬ Independent (sample true false) ∧
    (sample true false).historical past present) ∧
  (Temporal (sample true true) ∧ Independent (sample true true) ∧
    Dictionary (sample true true) ∧ ¬ Loss (sample true true) ∧
    (sample true true).historical past present)
end TruthCore.Causality.HistoricalRemoval
