module
public import TruthCore.Causality.NecessarySenseFork

/-! Analyst comparison, attribution deferred. Fixed rigid candidate type B,
existence valuation and accessibility throughout. Rotating existence says each
accessible world is populated but no candidate exists throughout; it says
nothing about causal support. Not an assertion about reality or God attributes.
The finite Sense enum's coverage of intended meanings remains OPEN; essence
necessity (including NECESSARY_7 FilteredNecessaryExistence) remains outside it.
NECESSARY_8 Box is not renumbered. -/
@[expose] public section
namespace TruthCore.Causality.RotatingBearerSenseComparison
open TruthCore.Causality.NecessarySenseFork
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.German.Kant.CosmologicalInference (Ontic)

def RotatingExistence {W B : Type} (o : Ontic W B) (w : W) : Prop :=
  (∀ v, o.frame.access w v → ∃ x, o.ExistsAt v x) ∧ ¬ ∃ x, BoxExistsAt o w x

/-- One fixed profile reuses the existing exact swap-existence control. -/
def rotatingProfile : Profile Bool Bool where
  ontic := Control.swapOntic
  concrete := fun _ => True
  grounds := fun _ _ _ => False

/-- Exact finite-enum classification, for arbitrary rigid candidates and CN.
Classical reasoning is explicit in the reverse diamond-duality step. -/
def Classification : Prop :=
  ∀ (W B : Type) (m : Profile W B) (w : W) (CN : B → B → Prop),
    TruthCore.Logic.ExcludedMiddle → RotatingExistence m.ontic w →
      ∀ s x, NecessaryIn s m w CN x ↔ s = Sense.deDictoK

/-- The root facts are separate: under the rival the only possible sense is
 de dicto, and a root still requires its independent identity/attribute facts. -/
def RootClassification : Prop :=
  ∀ (W : Type) (σ : TruthCore.Case.Catholicism.Signature)
    (m : Profile W σ.Being) (w : W) (CN : σ.Being → σ.Being → Prop),
    TruthCore.Logic.ExcludedMiddle → RotatingExistence m.ontic w → ∀ s,
      NecessaryRootInSense s σ m w CN ↔
        s = Sense.deDictoK ∧ ∃ n, RootFacts σ m w n

/-- Populated nonvacuity, and meaningful separation: strong modal frames
alone do not exchange box-exists and exists-box. -/
def Controls : Prop :=
  RotatingExistence rotatingProfile.ontic false ∧
  TruthCore.Modal.FrameSatisfies .S5 rotatingProfile.ontic.frame ∧
  (∀ x, NecessaryIn .deDictoK rotatingProfile false (fun _ _ => False) x) ∧
  (∃ x, rotatingProfile.ontic.ExistsAt false x) ∧
  ¬ RotatingExistence Control.unitProfile.ontic ()
end TruthCore.Causality.RotatingBearerSenseComparison
