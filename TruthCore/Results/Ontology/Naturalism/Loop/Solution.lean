module

public import TruthCore.Ontology.NaturalismConsequences

@[expose] public section

namespace TruthCore.Results.Ontology.Naturalism.Loop
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Ontology.ConcreteAbstract
open TruthCore.Ontology.Spatiotemporal
open TruthCore.Ontology.NaturalismConsequences

/-- Candidates: the spacetime whole, two parts `a` and `b`, and the number two,
which does not exist. -/
inductive Cand where
  | whole
  | a
  | b
  | two

/-- `a` and `b` cause each other, and `a` causes the whole. -/
def causes (x y : Cand) : Prop :=
  (x = .a ∧ y = .b) ∨ (x = .b ∧ y = .a) ∨ (x = .a ∧ y = .whole)

def ontic : Ontic Unit Cand where
  frame := { access := fun _ _ => True }
  ExistsAt _ x := x ≠ .two
  Causes _ x y := causes x y

def frame : Frame Cand where
  Region := Unit
  locatedAt x _ := x ≠ .two
  related x y := x ≠ .two ∧ y ≠ .two
  partOf x y := y = .whole ∧ x ≠ .two
  whole := .whole

def inAct (x : Cand) (_ : Unit) : Prop := x ≠ .two

def power (_ : Unit) (x : Cand) : Prop := ∃ y, causes x y

theorem causer_ne_two {x y : Cand} (h : causes x y) : x ≠ .two := by
  rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact fun h => Cand.noConfusion h

def anchors : Anchors (esseClassification inAct ()) where
  reasoner := .a
  setOfTwo := .two
  reasonerConcrete := fun h => Cand.noConfusion h
  setOfTwoAbstract := fun h => h rfl

/-- The causal-loop escape: a model in which the spacetime whole has an existing
cause `a`, `a` and another proper part `b` cause each other, every naturalist
variant holds, and the whole-to-part bridge fails. -/
theorem causalLoopRejectsBridge : CausalLoopRejectsBridge := by
  refine ⟨Unit, Cand, Unit, ontic, frame, inAct, (), power, (), ⟨anchors⟩, fun _ h => h,
    fun _ h => ⟨rfl, h⟩, fun _ h _ => ⟨rfl, h⟩, fun _ ⟨_, h⟩ => ⟨rfl, causer_ne_two h⟩,
    fun _ _ h _ => ⟨rfl, causer_ne_two h⟩,
    ⟨fun _ ⟨_, h⟩ => causer_ne_two h, fun _ _ h => causer_ne_two h⟩,
    fun _ _ h => ⟨_, h⟩, ?_, fun _ h => h, ⟨rfl, fun h => Cand.noConfusion h⟩,
    ⟨.a, fun h => Cand.noConfusion h, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩, ?_,
    ⟨.a, .b, fun h => Cand.noConfusion h, Or.inr (Or.inr ⟨rfl, rfl⟩),
      ⟨rfl, fun h => Cand.noConfusion h⟩, fun h => Cand.noConfusion h,
      ⟨rfl, fun h => Cand.noConfusion h⟩, fun h => Cand.noConfusion h,
      fun h => Cand.noConfusion h, Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩⟩
  · intro x _ h
    rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> exact Cand.noConfusion h
  · intro hBridge
    have h := hBridge .a .a (Or.inr (Or.inr ⟨rfl, rfl⟩)) ⟨rfl, fun h => Cand.noConfusion h⟩
    rcases h with ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;> exact Cand.noConfusion h

end TruthCore.Results.Ontology.Naturalism.Loop
