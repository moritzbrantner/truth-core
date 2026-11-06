module

public import TruthCore.Greek.Aristotle.Physics.Typed.Motion

/-! Analyst scope fork for the existing Physics VII.1 contact regress. The old
source reading generalizes to every injective touching chain. The inference
only uses chains of the same local moved-mover relation. Local-chain composition
is an explicit weaker framework input, not an attribution or a new mereology.
ComposedOf stays primitive: the controls test its stipulated scope, not physical
possibility, real aggregation or a theory of quantitative infinity. -/

@[expose] public section
namespace TruthCore.Greek.Aristotle.Physics.LocalContactComposition
open TruthCore.Greek.Aristotle.Physics.Typed

/-- Only an injective touching chain of the actual selected local links must
have a whole. All predicates/relata are the original VII.1 dictionary. -/
def LocalTouchingChainFormsOne {B R : Type}
    (IsLocal : R → Prop) (MovedIn : B → R → Prop)
    (MovesIn : B → B → R → Prop) (MovesPrimarily Touches : B → B → Prop)
    (ComposedOf : B → (Nat → B) → Prop) : Prop :=
  ∀ c : Nat → B, Function.Injective c →
    (∀ n, LocalMovedMoverLink IsLocal MovedIn MovesIn MovesPrimarily (c (n+1)) (c n)) →
    (∀ n, Touches (c (n+1)) (c n)) → ∃ w, ComposedOf w c

namespace Control
abbrev B := Nat × Bool
def isLocal (_ : Unit) : Prop := True
def moved (x : B) (_ : Unit) : Prop := x.2 = false
def moves (y x : B) (_ : Unit) : Prop := y.1 = x.1 + 1 ∧ y.2 = false ∧ x.2 = false
def primary (y x : B) : Prop := y.1 = x.1 + 1
def touches (_ _ : B) : Prop := True
def composed (_ : B) (c : Nat → B) : Prop := ∀ n, (c n).2 = false
def localChain (n : Nat) : B := (n,false)
def otherChain (n : Nat) : B := (n,true)
end Control

/-- The control exports a real infinite local chain and its whole, an unrelated
injective touching chain with no whole, local scope validity and global failure.
It does not assert the traversal and impossibility inputs of the regress proof. -/
def PopulatedStrictness : Prop :=
  LocalTouchingChainFormsOne Control.isLocal Control.moved Control.moves
    Control.primary Control.touches Control.composed ∧
  Function.Injective Control.localChain ∧
  (∀ n, LocalMovedMoverLink Control.isLocal Control.moved Control.moves Control.primary
    (Control.localChain (n+1)) (Control.localChain n)) ∧
  Control.composed (0,false) Control.localChain ∧
  Function.Injective Control.otherChain ∧
  (∀ n, Control.touches (Control.otherChain (n+1)) (Control.otherChain n)) ∧
  (¬ ∃ w, Control.composed w Control.otherChain) ∧
  ¬ TouchingChainFormsOneReading Control.touches Control.composed

end TruthCore.Greek.Aristotle.Physics.LocalContactComposition
