import TruthCore.Causality.ModalSenseSupport
import TruthCore.Results.Modal.StandardCorrespondenceCertificate.Solution
import TruthCore.Results.Modal.ConvergenceCertificate.Solution

/-! Frame-class branches of the "necessary" sense fork from modal principles.
Each fork theorem takes the modal library's correspondence certificates
(`StandardCorrespondenceCertificate`: T schema iff reflexive;
`ConvergenceCertificate`: 4 iff transitive, B iff symmetric, 5 iff Euclidean)
as premises and APPLIES them to the route's frame: the schema premises are
modal principles about the route's necessity, and the frame condition of the
selected sense is derived, not assumed. The K node is the existing
`NecessaryRootBoxK` (25 route inputs, NECESSARY-ROOT-BOX-K). The controls
instantiate the certificates with their existing proofs. -/

namespace TruthCore.Results.Causality.ModalSenseSupport
open TruthCore.Modal
open TruthCore.Causality.NecessarySenseFork
open TruthCore.Causality.ModalSenseSupport
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Case.Catholicism (Signature)

/-- T branch (NECESSARY_2 in KT): the K node, the T schema on the route's frame
and the T reading give the fork node; reflexivity comes from the T
correspondence of the modal library. -/
theorem forkT {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) (Intended : Sense → Prop)
    (hCorr : StandardCorrespondenceCertificate.{0})
    (hK : NecessaryRootBoxK σ m w CN) (hT : OnticTSchemaValid m.ontic)
    (hSel : IntendedIsBoxT Intended) :
    NecessaryRootOnIntendedReading Intended σ m w CN := by
  sorry

/-- S4 branch (NECESSARY_2 in S4): reflexivity from the T correspondence,
transitivity from the 4 correspondence. -/
theorem forkS4 {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) (Intended : Sense → Prop)
    (hCorr : StandardCorrespondenceCertificate.{0})
    (hConv : ConvergenceCertificate.{0, 0})
    (hK : NecessaryRootBoxK σ m w CN) (hT : OnticTSchemaValid m.ontic)
    (h4 : Ontic4SchemaValid m.ontic) (hSel : IntendedIsBoxS4 Intended) :
    NecessaryRootOnIntendedReading Intended σ m w CN := by
  sorry

/-- KTB branch (NECESSARY_2 in KTB): reflexivity from the T correspondence,
symmetry from the B correspondence. -/
theorem forkKTB {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) (Intended : Sense → Prop)
    (hCorr : StandardCorrespondenceCertificate.{0})
    (hConv : ConvergenceCertificate.{0, 0})
    (hK : NecessaryRootBoxK σ m w CN) (hT : OnticTSchemaValid m.ontic)
    (hB : OnticBSchemaValid m.ontic) (hSel : IntendedIsBoxB Intended) :
    NecessaryRootOnIntendedReading Intended σ m w CN := by
  sorry

/-- S5 branch (NECESSARY_2 in S5): reflexivity from the T correspondence,
Euclideanness from the 5 correspondence. -/
theorem forkS5 {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) (Intended : Sense → Prop)
    (hCorr : StandardCorrespondenceCertificate.{0})
    (hConv : ConvergenceCertificate.{0, 0})
    (hK : NecessaryRootBoxK σ m w CN) (hT : OnticTSchemaValid m.ontic)
    (h5 : Ontic5SchemaValid m.ontic) (hSel : IntendedIsBoxS5 Intended) :
    NecessaryRootOnIntendedReading Intended σ m w CN := by
  sorry

namespace Control
open TruthCore.Causality.ModalSenseSupport.Control
open TruthCore.Causality.NecessarySenseFork.Control (unitSignature unitProfile chainFrame)

end Control

/-- The batch controls: nonvacuity, one omission model per load-bearing premise,
and the exact negations of the two recorded rivals. -/
theorem controls : TruthCore.Causality.ModalSenseSupport.Control.Controls := by
  sorry

end TruthCore.Results.Causality.ModalSenseSupport
