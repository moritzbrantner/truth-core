module

public import TruthCore.Ontology.Spatiotemporal

@[expose] public section

namespace TruthCore.Results.Ontology.Naturalism.Independence
open TruthCore.Ontology.ConcreteAbstract
open TruthCore.Ontology.Spatiotemporal

/-- Four candidates: the first coordinate says whether the candidate has esse in
re, the second whether it is in spacetime. The single region is occupied by the
candidates in spacetime, which stand in the spatiotemporal relation to each
other and are parts of the whole `(true, true)`. -/
def frame : Frame (Bool × Bool) where
  Region := Unit
  locatedAt x _ := x.2 = true
  related x y := x.2 = true ∧ y.2 = true
  partOf x y := x.2 = true ∧ y = (true, true)
  whole := (true, true)

/-- Esse in re in the model: the first coordinate. -/
def inAct (x : Bool × Bool) (_ : Unit) : Prop := x.1 = true

/-- The anchors: the reasoner `(true, true)` is concrete, the set of 2
`(false, false)` is abstract. -/
def anchors : Anchors (esseClassification inAct ()) where
  reasoner := (true, true)
  setOfTwo := (false, false)
  reasonerConcrete := rfl
  setOfTwoAbstract := Bool.false_ne_true

/-- Spatiotemporality is a separate property: for some anchored esse
classification and frame, each of the occupant, relational and part-of-spacetime
senses is independent of concreteness. -/
theorem spatiotemporalIndependentOfConcrete : SpatiotemporalIndependentOfConcrete := by
  refine ⟨Bool × Bool, Unit, inAct, (), frame, ⟨anchors⟩, ?_, ?_, ?_⟩
  · refine ⟨⟨(true, true), rfl, (), rfl⟩, ⟨(true, false), rfl, ?_⟩,
      ⟨(false, true), Bool.false_ne_true, (), rfl⟩, ⟨(false, false), Bool.false_ne_true, ?_⟩⟩
    · rintro ⟨_, h⟩; exact Bool.false_ne_true h
    · rintro ⟨_, h⟩; exact Bool.false_ne_true h
  · refine ⟨⟨(true, true), rfl, (true, true), rfl, rfl⟩, ⟨(true, false), rfl, ?_⟩,
      ⟨(false, true), Bool.false_ne_true, (true, true), rfl, rfl⟩,
      ⟨(false, false), Bool.false_ne_true, ?_⟩⟩
    · rintro ⟨_, h, _⟩; exact Bool.false_ne_true h
    · rintro ⟨_, h, _⟩; exact Bool.false_ne_true h
  · refine ⟨⟨(true, true), rfl, rfl, rfl⟩, ⟨(true, false), rfl, ?_⟩,
      ⟨(false, true), Bool.false_ne_true, rfl, rfl⟩, ⟨(false, false), Bool.false_ne_true, ?_⟩⟩
    · rintro ⟨h, _⟩; exact Bool.false_ne_true h
    · rintro ⟨h, _⟩; exact Bool.false_ne_true h

end TruthCore.Results.Ontology.Naturalism.Independence
