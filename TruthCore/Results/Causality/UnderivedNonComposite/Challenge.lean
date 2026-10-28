import TruthCore.Causality.UnderivedNonComposite
import TruthCore.Results.Causality.UnderivedCommonSource.Solution
namespace TruthCore.Results.Causality.UnderivedNonComposite
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NamedPotentialCauser
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Causality.SourceForest
open TruthCore.Causality.UnderivedCommonSource
open TruthCore.Causality.UnderivedNonComposite
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Same-witness connection, retaining all eight #636 premises. Three explicit
additional premises are q.3's uniting-cause reading and the two open interfaces.
No maximality, first-being, or cause-comparison assumption is introduced. -/
theorem from_union {W B P : Type} (m : Ontic W B)
    (R : W → B → B → Prop) (w : W)
    (Composite : B → Prop) (CausesIn : B → B → P → Prop) (esse : P)
    (hNecessary : NecessaryBeing m w)
    (hReflexive : ActualReflexive m w)
    (hNoContingent : NoContingentGroundOfNecessary m R w)
    (hUnionWF : WellFoundedUnionNecessarySupport m R w)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hMap : ActualCauseSupportsEsse m R w)
    (hConnected : WeaklyConnected (actualGraph m w))
    (hConfluent : UpstreamConfluent (actualGraph m w))
    (hUniting : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hPresent : UnitingCausesPresent m CausesIn esse w)
    (hActual : UnitingCausesAreActual m CausesIn esse w) :
    CommonUnderivedNonComposite m R w Composite := by
  sorry

theorem omission_controls : InterfaceOmissionControls := by
  sorry
end TruthCore.Results.Causality.UnderivedNonComposite
