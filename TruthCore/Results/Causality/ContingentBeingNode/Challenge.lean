import TruthCore.Causality.ContingentBeingNode
import TruthCore.Results.Modal.StandardCorrespondenceCertificate.Solution
import TruthCore.Results.Modal.ConvergenceCertificate.Solution
import TruthCore.Results.Modal.K.Laws.Solution
import TruthCore.Results.Modal.T.Laws.Solution
import TruthCore.Results.Modal.B.Laws.Solution
import TruthCore.Results.Modal.S5.Laws.Solution
import TruthCore.Results.Modal.SimplicityCollapse.Solution
import TruthCore.Results.Causality.ModalSenseSupport.Solution

/-!
# The contingency node: connection to the route and refutations of collapse

`inhabits` derives the Cogito population node from the contingency node (sole
premise, a strength order). Each refutation takes a verified modal-library
conclusion as a premise and applies it: the K collapse laws (collapse iff every
accessible world is the actual one), the T laws (necessary collapse gives
actual collapse on reflexive frames), the B laws (possible collapse gives actual
collapse on symmetric frames), the S5 laws (possible collapse leaves no
contingent proposition), and the simplicity-collapse core (an act performed at
every accessible world yields no contingent effect strictly). Frame conditions
come from the route's modal principles (T, B, 5 schemas) through the
correspondence certificates, one argument per frame-class sense of NECESSARY_2.
-/

namespace TruthCore.Results.Causality.ContingentBeingNode

open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Causality.ContingentBeingNode
open TruthCore.Causality.ModalSenseSupport
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- The contingency node strengthens the Cogito population node. -/
theorem inhabits {W B : Type} (m : Profile W B) (w : W)
    (h : SomeActualContingentAt m w) : InhabitedConcreteAt m.ontic m.concrete w := by
  sorry

/-- Not every actual concrete being is NECESSARY_2: the node's witness is not. -/
theorem notEveryNecessary {W B : Type} (m : Profile W B) (w : W)
    (h : SomeActualContingentAt m w) : NotEveryActualConcreteNecessaryAt m w := by
  sorry

/-- K sense (any frame): by the K collapse law, full collapse at `w` means that
`w` accesses only itself; the node's accessible world lacking its witness then
is `w`, where the witness exists. -/
theorem notCollapsedK {W B : Type} (m : Profile W B) (w : W)
    (hK : TruthCore.Modal.KResearch.Laws) (h : SomeActualContingentAt m w) :
    RouteNotCollapsedAt m.ontic w := by
  sorry

/-- KT sense: the T schema gives reflexivity (T correspondence); by the T law,
necessary collapse then gives actual collapse, excluded by `notCollapsedK`. -/
theorem notNecessarilyCollapsedT {W B : Type} (m : Profile W B) (w : W)
    (hCorr : StandardCorrespondenceCertificate.{0})
    (hK : TruthCore.Modal.KResearch.Laws) (hTL : TruthCore.Modal.TResearch.Laws)
    (hT : OnticTSchemaValid m.ontic) (h : SomeActualContingentAt m w) :
    RouteNotNecessarilyCollapsedAt m.ontic w := by
  sorry

/-- KTB sense: the B schema gives symmetry (B correspondence); by the B law,
possible collapse then gives actual collapse, excluded by `notCollapsedK`. -/
theorem notPossiblyCollapsedKTB {W B : Type} (m : Profile W B) (w : W)
    (hConv : ConvergenceCertificate.{0, 0})
    (hK : TruthCore.Modal.KResearch.Laws) (hBL : TruthCore.Modal.BResearch.Laws)
    (hB : OnticBSchemaValid m.ontic) (h : SomeActualContingentAt m w) :
    RouteNotPossiblyCollapsedAt m.ontic w := by
  sorry

/-- S5 sense: the T and 5 schemas give an S5 frame (T and 5 correspondences); by
the S5 law, possible collapse leaves no contingent proposition at `w`, but the
existence of the node's witness is one (true at `w` by reflexivity, false at the
accessible world lacking it). -/
theorem notPossiblyCollapsedS5 {W B : Type} (m : Profile W B) (w : W)
    (hCorr : StandardCorrespondenceCertificate.{0}) (hConv : ConvergenceCertificate.{0, 0})
    (hS5L : TruthCore.Modal.S5Research.Laws)
    (hT : OnticTSchemaValid m.ontic) (h5 : Ontic5SchemaValid m.ontic)
    (h : SomeActualContingentAt m w) : RouteNotPossiblyCollapsedAt m.ontic w := by
  sorry

/-- No act token performed at every accessible world strictly yields every
actual concrete being: by the simplicity-collapse core it would yield the node's
witness strictly, so the witness would not be contingent. -/
theorem noNecessaryActYieldsAll {W B : Type} (m : Profile W B) (w : W)
    (hCore : TruthCore.Modal.SimplicityCollapse.Core) (h : SomeActualContingentAt m w) :
    NoNecessaryActStrictlyYieldsAllAt m w := by
  sorry

namespace Control
open TruthCore.Causality.ContingentBeingNode.Control
open TruthCore.Causality.BruteFoundationBoundary (EveryContingentGroundedAt)

end Control

/-- The batch controls: nonvacuity, omission models and the vacuity scope of the
grounding premise under concrete necessitarianism. -/
theorem controls : TruthCore.Causality.ContingentBeingNode.Control.Controls := by
  sorry

end TruthCore.Results.Causality.ContingentBeingNode
