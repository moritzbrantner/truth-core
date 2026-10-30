import TruthCore.Causality.NecessarilyUnderived
import Mathlib.Order.WellFounded
import Lean.Elab.Tactic.Omega

/-! Source-free countermodel for #603/#542. Bool is a finite world carrier,
Nat an infinite rigid being carrier. The union forgets world labels; its
infinite predecessor sequence is not a causal chain inside any one world.
No claim of metaphysical possibility or source attribution is made. -/
namespace TruthCore.Causality.ParityUnionRegress

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived

/-- Distinct, present endpoints; the parity of the target selects the world. -/
def support (w : Bool) (g n : Nat) : Prop :=
  g = n + 1 ∧ n % 2 = if w then 1 else 0

/-- Universal accessibility and presence. Causes is instantiated by support
only in this mathematical control, without identifying the notions generally. -/
def model : Ontic Bool Nat where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := support

/-- Exact parity model certificate. Acyclic means no nonempty finite union
path returns to its start. This is weaker than union well-foundedness. -/
def Certificate : Prop :=
  (∀ w n, model.ExistsAt w n ∧ NecessaryAt model false n) ∧
  NecessaryBeing model false ∧ ActualReflexive model false ∧
  NoContingentGroundOfNecessary model support false ∧
  (∀ w a b c, support w a b → support w b c → False) ∧
  (∀ w, WellFoundedPresentEsseSupport model support w) ∧
  (∀ g n, UnionNecessarySupport model support false g n ↔ g = n + 1) ∧
  (∀ n, ¬ Relation.TransGen (UnionNecessarySupport model support false) n n) ∧
  ¬ WellFoundedUnionNecessarySupport model support false ∧
  ¬ NecessarilyUnderived model support false

end TruthCore.Causality.ParityUnionRegress
