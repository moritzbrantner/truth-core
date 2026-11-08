module

public import TruthCore.Causality.NecessarySenseFork

/-! Analyst audit of the necessary-root consumer, attribution deferred.
RootFacts already demands an actual root. Consequently its outer domain
witness cannot be mistaken for the sole warrant for actual existence.
This is not a calibration of arbitrary Ontic predicates to act in esse.
The empty-extension fixture shows why candidate-domain inhabitation alone
supplies no actual existence, even when a de re box holds vacuously.
-/

@[expose] public section
namespace TruthCore.Causality.ExistenceSenseRoute
open TruthCore.Causality.NecessarySenseFork
open TruthCore.Logic.CogitoConcrete (unitOntic)

/-- A nonempty candidate domain with an empty existence extension and no
accessible worlds. This is a logical counterinterpretation, not a claim that
an empty world is metaphysically possible. -/
def emptyOntic : TruthCore.German.Kant.CosmologicalInference.Ontic Unit Unit where
  frame := ⟨fun _ _ => False⟩
  ExistsAt := fun _ _ => False
  Causes := fun _ _ _ => False

/-- Positive root-node compatibility and the strongest domain-only rival:
the same candidate type is inhabited, box-existence holds, but actuality fails.
No inference from existence to esse is certified. -/
def Controls : Prop :=
  NecessaryRootBoxK Control.unitSignature Control.unitProfile () (fun _ _ => False) ∧
  NecessaryRootActualistK Control.unitSignature Control.unitProfile () (fun _ _ => False) ∧
  ((∃ x : Unit, BoxExistsAt emptyOntic () x) ∧
    ¬ ∃ x : Unit, emptyOntic.ExistsAt () x)
end TruthCore.Causality.ExistenceSenseRoute
