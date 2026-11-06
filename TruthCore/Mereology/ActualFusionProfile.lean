module

public import TruthCore.Mereology.AtomlessFusionProfile
public import TruthCore.Causality.ActualFusionNecessaryBeing

/-! Analyst model for #1071, attribution deferred. Body represents possible
objects, not literal sets coming into existence. Worlds select principal ideals
of the SAME fixed parthood order. A global blueprint part x≤y need not be actual;
actual parthood at w additionally guards existence of the whole (and hence its
parts). No causal availability or metaphysical applicability is asserted. -/

@[expose] public section
namespace TruthCore.Mereology.ActualFusionProfile
open UniversalFusionBoundary AtomlessFusionProfile
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.ActualFusionNecessaryBeing

/-- Three worlds, all mutually accessible. At world w exactly the nonempty
parts of w exist. The empty cause relation fills Ontic without causal warrant. -/
def model : Ontic Body Body where
  frame := ⟨fun _ _ => True⟩
  ExistsAt w x := x ≤ w
  Causes _ _ _ := False

/-- One joint interpretation: inherited atomic full profile, universal S5
access, actual population and possibility of every candidate, downward
actuality, all-nonempty actual-family Sum2 closure, and no necessary candidate.
Each world has a greatest actual object, but none is actual at all worlds.
The final witness rejects the stronger any-actual-part-to-fixed-whole bridge. -/
def Certificate : Prop :=
  AtomicCertificate ∧
  (∀ w v, model.frame.access w v) ∧
  (∀ w, ∃ x, model.ExistsAt w x) ∧
  (∀ x, ∃ w, model.ExistsAt w x) ∧
  (∀ w, ActualPartsExistAt model w) ∧
  (∀ w (family : Set Body), family.Nonempty →
    (∀ x ∈ family, model.ExistsAt w x) →
    ∃ u, Fusion family u ∧ model.ExistsAt w u) ∧
  (∀ w x, ¬ NecessaryAt model w x) ∧
  (∀ w, ¬ NecessaryBeing model w) ∧
  (∀ w, ∃ u, model.ExistsAt w u ∧
    ∀ x, model.ExistsAt w x → x ≤ u) ∧
  (¬ ∃ u, ∀ w, model.ExistsAt w u) ∧
  (∃ w p, p ≤ whole ∧ model.ExistsAt w p ∧ ¬ model.ExistsAt w whole)

end TruthCore.Mereology.ActualFusionProfile
