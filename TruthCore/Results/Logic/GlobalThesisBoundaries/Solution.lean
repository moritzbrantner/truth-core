module

public import TruthCore.Logic.GlobalThesisBoundaries
public import TruthCore.Results.Logic.ObjectiveTruthDefinitionFork.Controls.Solution

@[expose] public section

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
  intro hScope hFail
  let criterion : Norm L.Sentence := ⟨scope, verifiable⟩
  obtain ⟨hHolds, hCounterexample⟩ :=
    Norm.selfApplication (N := criterion) (Acceptable := meaningful) hScope hFail
  exact ⟨hHolds, fun hMeaning => Norm.not_holds_of_counterexample (hCounterexample hMeaning)⟩

theorem socialConstructionExcludesScopedObjectiveTruth (f : TruthCore.Logic.ObjectiveTruthDefinitionFork.Frame)
    (scope constructed : f.Sentence → Prop) :
    ScopedSocialConstruction f scope constructed →
    ConstructionVariesTruth f scope constructed →
    ActualStableDefinition f →
    NoObjectiveTruthInScope f scope := by
  intro hConstruction hVariation hCalibration s hScope hObjective
  obtain ⟨hActual, hStable⟩ := (hCalibration s).mp hObjective
  obtain ⟨p, hNotHeld⟩ := hVariation s hScope (hConstruction s hScope hActual) hActual
  exact hNotHeld ((hStable p).mpr hActual)

theorem socialConstructionControls : SocialConstructionControls := by
  have hCalibration : ActualStableDefinition actualStable :=
    TruthCore.Results.Logic.ObjectiveTruthDefinitionFork.Controls.strongCalibration
  have hStable : actualStable.objective .stableTrue := rfl
  have hLocal : ScopedSocialConstruction actualStable socialLocal socialLocal :=
    fun _ hScope _ => hScope
  have hLocalVariation : ConstructionVariesTruth actualStable socialLocal socialLocal := by
    intro s hScope _ _
    change s = .actualTrueVariable at hScope
    subst s
    exact ⟨true, fun h => h⟩
  have hGlobal : ScopedSocialConstruction actualStable (fun _ => True) (fun _ => True) :=
    fun _ _ _ => trivial
  have hNoGlobalVariation :
      ¬ ConstructionVariesTruth actualStable (fun _ => True) (fun _ => True) := by
    intro hVariation
    obtain ⟨p, hNotHeld⟩ := hVariation .stableTrue trivial trivial trivial
    cases p <;> exact hNotHeld trivial
  exact ⟨hCalibration,
    ⟨hLocal, hLocalVariation, rfl, trivial, (by intro h; cases h), hStable⟩,
    ⟨hGlobal, hNoGlobalVariation, fun hNone => hNone .stableTrue trivial hStable⟩⟩

theorem acceptedPackageUndercutsBasis (f : ReliabilityFrame) (a : f.Agent)
    (package : f.Content) (basis : f.Basis) :
    AcceptedPackage f a package →
    PackageRaisesReliabilityConcern f a package basis →
    ReliabilityConcernUndercuts f a basis →
    BasisUndercut f a basis := by
  intro hAccept hConcern hPolicy
  exact hPolicy (hConcern hAccept)

theorem undercutSoleBasisPrecludesWarrant (f : ReliabilityFrame) (a : f.Agent)
    (p : f.Content) (basis : f.Basis) :
    BasisUndercut f a basis →
    SoleSupportingBasis f a p basis →
    WarrantNeedsUndefeatedSupport f a p →
    LacksTargetWarrant f a p := by
  intro hUndercut hOnly hNeeds hWarrant
  obtain ⟨b, hSupport, hUndefeated⟩ := hNeeds hWarrant
  have hSame := hOnly b hSupport
  subst b
  exact hUndefeated hUndercut

theorem acceptedPackageLacksOwnWarrant (f : ReliabilityFrame) (a : f.Agent)
    (package : f.Content) (basis : f.Basis) :
    AcceptedPackage f a package →
    PackageRaisesReliabilityConcern f a package basis →
    ReliabilityConcernUndercuts f a basis →
    SoleSupportingBasis f a package basis →
    WarrantNeedsUndefeatedSupport f a package →
    LacksTargetWarrant f a package := by
  intro hAccept hConcern hPolicy hOnly hNeeds
  exact undercutSoleBasisPrecludesWarrant f a package basis
    (acceptedPackageUndercutsBasis f a package basis hAccept hConcern hPolicy) hOnly hNeeds

theorem reliabilityControls : ReliabilityControls := by
  have hSole (concern defeat : Bool) :
      SoleSupportingBasis (reliabilityControl concern defeat false) () true true := by
    intro b h
    rcases h with h | ⟨_, h | h⟩
    · exact h.1
    · cases h
    · cases h
  have hPrimary (concern : Bool) :
      UndefeatedSupport (reliabilityControl concern false false) () true :=
    ⟨true, Or.inl ⟨rfl, rfl⟩, fun h => Bool.noConfusion h.2⟩
  refine ⟨⟨rfl, fun _ => Or.inl ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩,
    hSole true true, ?_, ?_, trivial, ?_⟩,
    ⟨rfl, fun _ => Or.inl ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ?_, ?_, Or.inr (Or.inr rfl)⟩,
    ⟨rfl, ?_, ?_, hSole false false, fun _ => hPrimary false, Or.inr (Or.inl rfl)⟩,
    ⟨rfl, fun _ => Or.inl ⟨rfl, rfl⟩, ?_, hSole true false, fun _ => hPrimary true, Or.inr (Or.inl rfl)⟩⟩
  · intro h
    rcases h with h | h | h <;> cases h
  · intro h
    rcases h with h | h | h <;> cases h
  · exact ⟨(), false, false, Or.inr ⟨rfl, Or.inl rfl⟩, fun h => Bool.noConfusion h.1⟩
  · intro h
    exact Bool.noConfusion (h false (Or.inr ⟨rfl, Or.inr rfl⟩))
  · intro _
    exact ⟨false, Or.inr ⟨rfl, Or.inr rfl⟩, fun h => Bool.noConfusion h.1⟩
  · intro h
    rcases h rfl with h | h
    · exact Bool.noConfusion h.2
    · exact h
  · intro h
    rcases h with h | h
    · exact Bool.noConfusion h.2
    · exact False.elim h
  · intro h
    exact Bool.noConfusion (h (Or.inl ⟨rfl, rfl⟩)).2

end TruthCore.Results.Logic.GlobalThesisBoundaries
