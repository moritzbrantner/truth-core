module

public import TruthCore.Ontology.NaturalismConsequences

@[expose] public section

namespace TruthCore.Results.Ontology.Naturalism.Survivor
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Ontology.ConcreteAbstract
open TruthCore.Ontology.Spatiotemporal
open TruthCore.Ontology.NaturalismConsequences

/-- Candidates: the spacetime whole, its parts (stages) `part n`, and the
number two, which does not exist. -/
inductive Cand where
  | whole
  | part (n : Nat)
  | two

/-- Each stage `part (n+1)` causes the stage `part n`: an infinite regress with
no external cause. Nothing causes the whole. -/
def ontic : Ontic Unit Cand where
  frame := { access := fun _ _ => True }
  ExistsAt _ x := x ≠ .two
  Causes _ x y := ∃ n, x = .part (n + 1) ∧ y = .part n

/-- Every existent occupies the one region, is related to every existent, and is
a part of the whole (the whole an improper part of itself). -/
def frame : Frame Cand where
  Region := Unit
  locatedAt x _ := x ≠ .two
  related x y := x ≠ .two ∧ y ≠ .two
  partOf x y := y = .whole ∧ x ≠ .two
  whole := .whole

/-- Esse in re: every candidate except the number. -/
def inAct (x : Cand) (_ : Unit) : Prop := x ≠ .two

/-- Causal power: causing something. -/
def power (_ : Unit) (x : Cand) : Prop := ∃ y, ontic.Causes () x y

theorem part_ne_two (n : Nat) : Cand.part n ≠ .two := fun h => Cand.noConfusion h

/-- The anchors: the stage `part 0` is the reasoner, the number two the set of 2. -/
def anchors : Anchors (esseClassification inAct ()) where
  reasoner := .part 0
  setOfTwo := .two
  reasonerConcrete := part_ne_two 0
  setOfTwoAbstract := fun h => h rfl

/-- The brute-universe and regress escapes have a joint model with every
naturalist variant and the floor items listed in
`NaturalistUncausedUniverseSurvivor`. -/
theorem naturalistUncausedUniverseSurvivor : NaturalistUncausedUniverseSurvivor := by
  refine ⟨Unit, Cand, Unit, ontic, frame, inAct, (), power, (), ⟨anchors, part_ne_two 0, fun h => h rfl⟩,
    fun _ h => h, fun _ h => ⟨rfl, h⟩, fun _ h => ⟨(), h⟩, fun _ h => ⟨.part 0, h, part_ne_two 0⟩,
    fun _ _ h => ⟨rfl, h⟩, ?_, ?_, ⟨?_, ?_⟩, fun _ _ h => ⟨_, h⟩, ?_, ?_, ⟨rfl, fun h => Cand.noConfusion h⟩,
    fun h => Cand.noConfusion h, ⟨(), fun h => Cand.noConfusion h⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨_, n, rfl, _⟩; exact ⟨rfl, part_ne_two _⟩
  · rintro x _ ⟨n, rfl, _⟩ _; exact ⟨rfl, part_ne_two _⟩
  · rintro x ⟨_, n, rfl, _⟩; exact part_ne_two _
  · rintro x _ ⟨n, rfl, _⟩; exact part_ne_two _
  · rintro c y ⟨n, _, h⟩; exact Cand.noConfusion h
  · rintro x _ ⟨n, h1, h2⟩
    rw [h1] at h2
    exact Nat.succ_ne_self n (Cand.part.inj h2)
  · exact ⟨fun x => ∃ y, ontic.Causes () y x, ⟨.part 0, .part 1, 0, rfl, rfl⟩,
      fun x ⟨_, n, _, h⟩ => ⟨rfl, h ▸ part_ne_two n⟩⟩
  · exact ⟨fun x _ => ∃ y, ontic.Causes () y x, ⟨.part 0, (), .part 1, 0, rfl, rfl⟩,
      fun x _ ⟨_, n, _, h⟩ => ⟨rfl, h ▸ part_ne_two n⟩⟩
  · exact ⟨fun a p => a = .part 0 ∧ p = .part 0, ⟨.part 0, .part 0, rfl, rfl⟩,
      fun a _ ⟨h, _⟩ => ⟨rfl, h ▸ part_ne_two 0⟩⟩
  · rintro c ⟨n, _, h⟩; exact Cand.noConfusion h
  · rintro x ⟨_, hx⟩ hw
    cases x with
    | whole => exact absurd rfl hw
    | part n => exact ⟨.part (n + 1), n, rfl, rfl⟩
    | two => exact absurd rfl hx

end TruthCore.Results.Ontology.Naturalism.Survivor
