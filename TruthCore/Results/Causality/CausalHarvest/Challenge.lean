import Mathlib.Order.RelClasses
import TruthCore.Causality.NamedPotentialCauser
import TruthCore.Explanation.WellFoundedSource
import TruthCore.Logic.Configuration
namespace TruthCore.Results.Causality.CausalHarvest
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Modal.ExistenceDegrees
open TruthCore.Causality.NamedPotentialCauser
open TruthCore.Explanation.ExistencePSR
open TruthCore.Explanation.WellFoundedSource

/-- Operational adapter of the existing causal core, not a new discovery.
External causation is all-world; population and WF concern the selected world. -/
theorem localPSRCausalCore {World Being : Type} (m : Model World Being) (w : World)
    (hPop : PopulatedAt m w) (hWF : WellFoundedCausesAt m w)
    (hExternal : EveryExistentExternallyCaused m) :
    TruthCore.Logic.ConfigurationFalse := by
  sorry

/-- The named selected source, rather than merely some witness, is underived
in the explicitly selected ordinary-causal-support profile R := m.Causes. -/
theorem selectedCauserUnderived {World Being : Type} (m : Ontic World Being)
    (w : World) (n : Being) (hRef : ActualReflexive m w)
    (hNec : NecessaryAt m w n) (hPotential : OtherDirectedPotentialCause m w n)
    (hNoContingent : NoContingentGroundOfNecessary m m.Causes w)
    (hUnionWF : WellFoundedUnionNecessarySupport m m.Causes w) :
    NamedNecessarilyUnderived m m.Causes w n := by
  sorry

theorem varyingNamedControl : VaryingNamedControl := by
  sorry

theorem contingentPredecessorControl : ContingentPredecessorControl := by
  sorry
end TruthCore.Results.Causality.CausalHarvest
