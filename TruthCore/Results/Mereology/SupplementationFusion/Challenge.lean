import TruthCore.Mereology.SupplementationFusion

namespace TruthCore.Results.Mereology.SupplementationFusion
open TruthCore.Mereology.UniversalFusionBoundary
open TruthCore.Mereology.NecessaryPartFusionDecomposition
open TruthCore.Mereology.SupplementationFusion

theorem strongFromWeakBinary (B : Type) [PartialOrder B]
    (hWeak : WeakSupplementation B) (hBinary : BinaryFusion B) :
    StrongSupplementation B := by sorry

theorem separationCharacterization (B : Type) [PartialOrder B] :
    SeparationCharacterization B := by sorry

theorem fusionComparison (B : Type) [PartialOrder B]
    (hStrong : StrongSupplementation B) : FusionComparison B := by sorry

theorem overlapGreatest (B : Type) [PartialOrder B] [Nonempty B]
    (hStrong : StrongSupplementation B) (hOverlap : UnrestrictedOverlap B) :
    GreatestEntity B := by sorry

theorem rivalChecks : RivalCertificate := by sorry

end TruthCore.Results.Mereology.SupplementationFusion
