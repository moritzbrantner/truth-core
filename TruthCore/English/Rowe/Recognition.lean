module

public import TruthCore.English.Rowe.EvidentialEvil

@[expose] public section
namespace TruthCore.English.Rowe.Recognition
open TruthCore.English.Rowe

/-- A finite inventory of candidate outcomes for each hypothetical preventer
and suffering event. Recognition remains the fixed investigator's predicate in
Sig; this inventory is not stipulated to exhaust reality. -/
abbrev Survey (s : Sig) := s.Being → s.Event → List s.Outcome

/-- Only actual blocking outcomes in occurring intense suffering cases and
omniscient omnipotent preventers must be on the inventory. OPEN applicability. -/
def Covered (s : Sig) (survey : Survey s) : Prop :=
  ∀ b e o, s.Omniscient b → s.Omnipotent b → s.Occurs e → s.IntenseSuffering e →
    s.Cost b e o → (s.GreaterGood o e ∨ s.EqualOrWorseEvil o e) → o ∈ survey b e

/-- Every listed actual blocking outcome in the relevant cases is recognized.
No factivity assumption is needed: false recognition cannot defeat this proof. -/
def Complete (s : Sig) (survey : Survey s) : Prop :=
  ∀ b e o, s.Omniscient b → s.Omnipotent b → s.Occurs e → s.IntenseSuffering e →
    o ∈ survey b e → s.Cost b e o →
    (s.GreaterGood o e ∨ s.EqualOrWorseEvil o e) → s.RecognizesCost b e o

/-- Joint nonvacuity with a qualifying preventer and an actual suffering event. -/
def Nonvacuity : Prop := ∃ s : Sig, ∃ survey : Survey s,
  Covered s survey ∧ Complete s survey ∧ ApparentlyPointlessSuffering s ∧
    GratuitousSufferingReading s ∧ (∃ b, s.Omniscient b ∧ s.Omnipotent b)

/-- Hidden-cost models independently omit coverage or recognition completeness;
their permission constraint and narrow-theism witness are retained. -/
def OmissionControls : Prop :=
  (∃ s : Sig, ∃ survey : Survey s, Complete s survey ∧ ¬ Covered s survey ∧
    PermissionConstraintReading s ∧ ApparentlyPointlessSuffering s ∧ TheisticBeingExists s) ∧
  (∃ s : Sig, ∃ survey : Survey s, Covered s survey ∧ ¬ Complete s survey ∧
    PermissionConstraintReading s ∧ ApparentlyPointlessSuffering s ∧ TheisticBeingExists s)
end TruthCore.English.Rowe.Recognition
