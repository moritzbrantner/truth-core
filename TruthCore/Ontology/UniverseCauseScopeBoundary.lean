module

public import TruthCore.Ontology.NaturalismConsequences
public import TruthCore.Causality.ActualFusionNecessaryBeing
public import TruthCore.Logic.ExcludedMiddle

/-!
# No cause versus no existing cause of the spacetime whole

The original positive conclusion requires an existing causer; the brute-universe
rival denies every causal edge, even from nonactual candidate causers. Generic
Ontic does not impose endpoint actuality. Reuse the existing explicit endpoint
policy and restrict it to the whole's causers; do not silently add it to Ontic.
The absent-edge control is deliberately outside that policy, not a claim that
a nonactual individual can productively cause in reality. All original causal
meanings and frozen results remain unchanged.
-/

@[expose] public section
namespace TruthCore.Ontology.UniverseCauseScopeBoundary
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Ontology.Spatiotemporal
open TruthCore.Ontology.NaturalismConsequences

/-- Some supplied productive/dependence edge to the selected whole. The candidate
causer's actuality is not built into the old Ontic relation. -/
def HasSomeCause {W B : Type} (o : Ontic W B) (F : Frame B) (w : W) : Prop :=
  ∃ c, o.Causes w c F.whole

/-- Weak actuality interface actually needed by the positive argument. It does
not require every other cause/effect to exist or the whole to exist by itself. -/
def WholeCausersExist {W B : Type} (o : Ontic W B) (F : Frame B) (w : W) : Prop :=
  ∀ c, o.Causes w c F.whole → o.ExistsAt w c

def NoExistingCause {W B : Type} (o : Ontic W B) (F : Frame B) (w : W) : Prop :=
  ¬ UniverseHasExistingCause o F w

/-- Precise remaining generic-signature case: a causal edge exists but none has
an actual causer. Not an additional naturalist theory or an intended causal model. -/
def OnlyAbsentCausers {W B : Type} (o : Ontic W B) (F : Frame B) (w : W) : Prop :=
  HasSomeCause o F w ∧ NoExistingCause o F w

def WholeCauserActualityFails {W B : Type} (o : Ontic W B) (F : Frame B) (w : W) : Prop :=
  ¬ WholeCausersExist o F w

def CauseScopeTrilemma {W B : Type} (o : Ontic W B) (F : Frame B) (w : W) : Prop :=
  UniverseHasExistingCause o F w ∨ UniverseUncaused o F w ∨ OnlyAbsentCausers o F w

def ActualCauseOrUncaused {W B : Type} (o : Ontic W B) (F : Frame B) (w : W) : Prop :=
  UniverseHasExistingCause o F w ∨ UniverseUncaused o F w

def twoRoleFrame : Frame Bool where
  Region := Unit
  locatedAt := fun _ _ => False
  related := fun _ _ => False
  partOf := fun x y => x = y
  whole := false

def absent : Ontic Unit Bool where
  frame := { access := fun _ _ => True }
  ExistsAt := fun _ x => x = false
  Causes := fun _ c x => c = true ∧ x = false

def actual : Ontic Unit Bool := { absent with ExistsAt := fun _ _ => True }
def uncaused : Ontic Unit Bool := { actual with Causes := fun _ _ _ => False }

def Controls : Prop :=
  (OnlyAbsentCausers absent twoRoleFrame () ∧
    ¬ UniverseUncaused absent twoRoleFrame () ∧
    absent.ExistsAt () twoRoleFrame.whole ∧
    ¬ WholeCausersExist absent twoRoleFrame ()) ∧
  (UniverseHasExistingCause actual twoRoleFrame () ∧
    TruthCore.Causality.ActualFusionNecessaryBeing.CausesHaveActualEndpointsAt actual () ∧
    ∀ x, actual.ExistsAt () x) ∧
  (UniverseUncaused uncaused twoRoleFrame () ∧
    TruthCore.Causality.ActualFusionNecessaryBeing.CausesHaveActualEndpointsAt uncaused () ∧
    ¬ UniverseHasExistingCause uncaused twoRoleFrame () ∧
    ∀ x, uncaused.ExistsAt () x)

end TruthCore.Ontology.UniverseCauseScopeBoundary
