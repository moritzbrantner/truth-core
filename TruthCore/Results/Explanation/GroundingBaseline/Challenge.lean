import TruthCore.Explanation.GroundingBaseline
import TruthCore.Logic.Configuration
namespace TruthCore.Results.Explanation.GroundingBaseline
open TruthCore.Explanation.GroundingBaseline
open TruthCore.Explanation.PSRStrength
open TruthCore.Logic (ExcludedMiddle)
theorem modalIndependence : ModalIndependence := by sorry
theorem necessitationImpossible {W B F : Type} (A : Arena W B F) (a : W) (p q : F)
    (hc : Contingent A a p) (hn : NecessaryFact A a q)
    (hs : NecessaryImplication A a q p) : TruthCore.Logic.ConfigurationFalse := by sorry
theorem necessitationCore : NecessitationCore := by sorry
theorem contingentTerminus {W B F : Type} (A : Arena W B F) (a : W)
    (R : F → F → Prop) (G : FullGround F) (x : F)
    (hEM : ExcludedMiddle) (hc : Contingent A a x) (hf : WellFounded R)
    (ha : ActualMembers A a G) (hl : LinkedMembers R G)
    (hn : JointNecessitation A a G) : UngroundedContingent A a G := by sorry
theorem contingentTerminusMap : ContingentTerminus := by sorry
theorem enablingCycle : EnablingCycle := by sorry
end TruthCore.Results.Explanation.GroundingBaseline
