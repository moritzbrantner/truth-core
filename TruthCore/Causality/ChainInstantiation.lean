import TruthCore.Causality.LocalTransmission
import TruthCore.German.Kant.CosmologicalInference

/-! Analyst controls for #704. `Nat` indexes candidate stages, not instantiation
in reality. `ExistsAt` carries the population extension; causal edges are
world-local and require both endpoints. No temporal or grounding interpretation
is established by these definitions. -/
namespace TruthCore.Causality.ChainInstantiation
open TruthCore.German.Kant.CosmologicalInference

/-- One complete candidate history with guarded upstream successor links.
The common candidate domain is not the actual population. -/
def chain (present : Nat → Prop) : Ontic Unit Nat where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ => present
  Causes := fun _ y x => y = x + 1 ∧ present y ∧ present x

/-- A finite actual population, including the selected observed stage zero. -/
def finite (bound : Nat) : Ontic Unit Nat := chain (fun n => n ≤ bound)

/-- All candidate stages populated, with no upstream endpoint. -/
def infinite : Ontic Unit Nat := chain (fun _ => True)

/-- No candidate stage populated, on the very same nonempty candidate type. -/
def empty : Ontic Unit Nat := chain (fun _ => False)

/-- Exact observations are presence and causal edges whose two endpoints lie
in the supplied finite window. Outside-window edges are not observed. -/
def SameWindow (a b : Ontic Unit Nat) (bound : Nat) : Prop :=
  (∀ x, x ≤ bound → (a.ExistsAt () x ↔ b.ExistsAt () x)) ∧
  (∀ y x, y ≤ bound → x ≤ bound →
    (a.Causes () y x ↔ b.Causes () y x))

/-- A bounded observational record is compatible with a populated finite
source chain and a populated infinite chain. The finite chain has a source at
its boundary; the infinite chain is not well-founded. Separately, the *same*
universal successor-presence equation holds in both empty and fully populated
interpretations. These are model controls, not actual histories or adequate
explanations, and not observational equivalence for arbitrary experiments. -/
def Controls : Prop :=
  (∀ bound, SameWindow (finite bound) infinite bound ∧
    (finite bound).ExistsAt () 0 ∧
    (∀ x, (finite bound).ExistsAt () x → x ≤ bound) ∧
    ¬ (finite bound).ExistsAt () (bound + 1) ∧
    (∀ y, ¬ (finite bound).Causes () y bound) ∧
    (∀ x, infinite.ExistsAt () x) ∧
    ¬ WellFounded (infinite.Causes ())) ∧
  (TruthCore.Causality.LocalTransmission (empty.ExistsAt ()) ∧
    TruthCore.Causality.LocalTransmission (infinite.ExistsAt ()) ∧
    (¬ ∃ x, empty.ExistsAt () x) ∧ (∃ x, infinite.ExistsAt () x))

end TruthCore.Causality.ChainInstantiation
