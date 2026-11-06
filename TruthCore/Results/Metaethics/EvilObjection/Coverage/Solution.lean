module

public import TruthCore.Metaethics.EvilObjection

@[expose] public section

namespace TruthCore.Results.Metaethics.EvilObjection.Coverage

open TruthCore.Metaethics.EvilObjection TruthCore.English.Rowe TruthCore.Logic

/-- Excluded middle covers these diagnostic conditions only because the
explicit remainder is retained. No proof eliminates that remainder. -/
theorem useCoverageWithRemainder (c : Critic) (s : Sig) (hEM : ExcludedMiddle) :
    UseCoverageWithRemainder c s := by
  cases hEM (OwnTruePremise c) with
  | inl h => exact Or.inl h
  | inr hOwn =>
    cases hEM (InternalPermissionChallenge s) with
    | inl h => exact Or.inr (Or.inl h)
    | inr hInternal =>
      cases hEM (AffectiveProtest c) with
      | inl h => exact Or.inr (Or.inr (Or.inl h))
      | inr hAffective => exact Or.inr (Or.inr (Or.inr ⟨hOwn, hInternal, hAffective⟩))

end TruthCore.Results.Metaethics.EvilObjection.Coverage
