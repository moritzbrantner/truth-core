import TruthCore.Case.Catholicism.Root
namespace TruthCore.Results.Case.Catholicism.Skeleton
open TruthCore.Case.Catholicism
theorem catholicismSkeleton (σ : Signature)
    (hGod : GodExists σ.IsGod)
    (hAttributes : GodHasClassicalAttributes σ)
    (hRevelation : RevelationPossibleAndRecognizable σ)
    (hJesus : JesusClaimedDivineAuthorityAndRose σ)
    (hFounded : ChristFoundedVisibleChurch σ)
    (hCatholic : ChristsChurchIsCatholicChurch σ)
    (hDivineFounding : BridgeChristsChurchFoundedByGod σ)
    (hOnlyTruth : BridgeGodFoundedAuthorityProposesOnlyTruth σ)
    (hProposes : CatholicChurchDefinitivelyProposesCreed σ) :
    CatholicismTrue σ := by
  -- INF-CATHOLICISM-SKELETON-CHRISTS-CHURCH-GOD-FOUNDED
  have hChrists : ChristsChurchIsGodFoundedTeachingAuthority σ := by
    obtain ⟨g, hg⟩ := hGod
    exact ⟨g, hg, hDivineFounding g hg (hAttributes g hg) (hRevelation g hg)
      hJesus.1 hJesus.2⟩
  -- INF-CATHOLICISM-SKELETON-CATHOLIC-CHURCH-GOD-FOUNDED
  have hA : CatholicChurchIsGodFoundedTeachingAuthority σ := by
    obtain ⟨g, hg, hFoundedByG⟩ := hChrists
    obtain ⟨c, hc, hVisible⟩ := hFounded
    have hEq : c = σ.catholicChurch := hCatholic c hc hVisible
    have hTeaching : σ.FoundedAsTeachingAuthority g c := hFoundedByG c hc hVisible
    rw [hEq] at hTeaching
    exact ⟨g, hg, hTeaching⟩
  -- INF-CATHOLICISM-SKELETON-CREED-ARTICLES-HOLD
  have hB : CreedArticlesHold σ := by
    obtain ⟨g, hg, hTeaching⟩ := hA
    intro p hp
    exact hOnlyTruth g σ.catholicChurch hg (hAttributes g hg) hTeaching p (hProposes p hp)
  -- INF-CATHOLICISM-SKELETON-ROOT
  exact ⟨hA, hB⟩
end TruthCore.Results.Case.Catholicism.Skeleton
