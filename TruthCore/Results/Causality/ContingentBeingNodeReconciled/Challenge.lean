import TruthCore.Results.Causality.ContingentBeingNode.Solution

/-! Revised analyst interfaces: consume closed modal certificates by theorem
application instead of requiring their multi-sense bundles as hypotheses.
The original ContingentBeingNode Challenge remains frozen. -/

namespace TruthCore.Results.Causality.ContingentBeingNodeReconciled
open TruthCore.Causality.ContingentBeingNode
open TruthCore.Causality.ModalSenseSupport
open TruthCore.Causality.BruteFoundationBoundary (Profile)

/-- Any-frame consequence of actual individual contingency. -/
theorem notCollapsedK {W B : Type} (m : Profile W B) (w : W)
    (h : SomeActualContingentAt m w) : RouteNotCollapsedAt m.ontic w := by
  sorry

/-- T schema is an open frame assumption; its correspondence is checked. -/
theorem notNecessarilyCollapsedT {W B : Type} (m : Profile W B) (w : W)
    (hT : OnticTSchemaValid m.ontic) (h : SomeActualContingentAt m w) :
    RouteNotNecessarilyCollapsedAt m.ontic w := by
  sorry

/-- B schema is an open frame assumption; its correspondence is checked. -/
theorem notPossiblyCollapsedKTB {W B : Type} (m : Profile W B) (w : W)
    (hB : OnticBSchemaValid m.ontic) (h : SomeActualContingentAt m w) :
    RouteNotPossiblyCollapsedAt m.ontic w := by
  sorry

/-- T and 5 remain explicit open assumptions. -/
theorem notPossiblyCollapsedS5 {W B : Type} (m : Profile W B) (w : W)
    (hT : OnticTSchemaValid m.ontic) (h5 : Ontic5SchemaValid m.ontic)
    (h : SomeActualContingentAt m w) : RouteNotPossiblyCollapsedAt m.ontic w := by
  sorry

/-- Strict efficacy plus the same necessary act is incompatible with the node. -/
theorem noNecessaryActYieldsAll {W B : Type} (m : Profile W B) (w : W)
    (h : SomeActualContingentAt m w) : NoNecessaryActStrictlyYieldsAllAt m w := by
  sorry

end TruthCore.Results.Causality.ContingentBeingNodeReconciled
