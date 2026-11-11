import TruthCore.Logic.GlobalThesisBoundaries
import TruthCore.Results.Logic.ObjectiveTruthDefinitionFork.Controls.Solution

namespace TruthCore.Results.Logic.GlobalThesisBoundaries

open TruthCore.Logic.GlobalThesisBoundaries
open TruthCore.Logic.ObjectiveTruthDefinitionFork
open TruthCore.Logic.SelfApplication
open TruthCore.Logic.Verificationism

theorem strictVerificationDilemma (L : Language)
    (meaningful scope verifiable : L.Sentence → Prop) (self : L.Sentence) :
    @StrictFormulationInScope L scope self →
    @StrictFormulationNotVerifiable L verifiable self →
    @StrictVerificationDilemma L meaningful scope verifiable self := by
  sorry

theorem socialConstructionExcludesScopedObjectiveTruth (f : TruthCore.Logic.ObjectiveTruthDefinitionFork.Frame)
    (scope constructed : f.Sentence → Prop) :
    ScopedSocialConstruction f scope constructed →
    ConstructionVariesTruth f scope constructed →
    ActualStableDefinition f →
    NoObjectiveTruthInScope f scope := by
  sorry

theorem socialConstructionControls : SocialConstructionControls := by
  sorry

theorem acceptedPackageUndercutsBasis (f : ReliabilityFrame) (a : f.Agent)
    (package : f.Content) (basis : f.Basis) :
    AcceptedPackage f a package →
    PackageRaisesReliabilityConcern f a package basis →
    ReliabilityConcernUndercuts f a basis →
    BasisUndercut f a basis := by
  sorry

theorem undercutSoleBasisPrecludesWarrant (f : ReliabilityFrame) (a : f.Agent)
    (p : f.Content) (basis : f.Basis) :
    BasisUndercut f a basis →
    SoleSupportingBasis f a p basis →
    WarrantNeedsUndefeatedSupport f a p →
    LacksTargetWarrant f a p := by
  sorry

theorem acceptedPackageLacksOwnWarrant (f : ReliabilityFrame) (a : f.Agent)
    (package : f.Content) (basis : f.Basis) :
    AcceptedPackage f a package →
    PackageRaisesReliabilityConcern f a package basis →
    ReliabilityConcernUndercuts f a basis →
    SoleSupportingBasis f a package basis →
    WarrantNeedsUndefeatedSupport f a package →
    LacksTargetWarrant f a package := by
  sorry

theorem reliabilityControls : ReliabilityControls := by
  sorry

end TruthCore.Results.Logic.GlobalThesisBoundaries
