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
  have hChrists : ChristsChurchIsGodFoundedTeachingAuthority σ :=
    hDivineFounding hGod hAttributes hRevelation hJesus
  -- INF-CATHOLICISM-SKELETON-CATHOLIC-CHURCH-GOD-FOUNDED
  have hA : CatholicChurchIsGodFoundedTeachingAuthority σ := by
    obtain ⟨c, hc⟩ := hFounded
    have hEq : c = σ.catholicChurch := hCatholic c hc
    have hc' : σ.GodFoundedTeachingAuthority c := hChrists c hc
    unfold CatholicChurchIsGodFoundedTeachingAuthority
    rw [← hEq]
    exact hc'
  -- INF-CATHOLICISM-SKELETON-CREED-ARTICLES-HOLD
  have hB : CreedArticlesHold σ := fun p hp =>
    hOnlyTruth hAttributes σ.catholicChurch hA p (hProposes p hp)
  -- INF-CATHOLICISM-SKELETON-ROOT
  exact ⟨hA, hB⟩
end TruthCore.Results.Case.Catholicism.Skeleton
