import TruthCore.History.ResurrectionCoverage
namespace TruthCore.Results.Comparison.Resurrection.AnswerMapsCorrect
open TruthCore.History.Resurrection
open TruthCore.Comparison.Resurrection
/-- Transcription/bookkeeping only; no historical conclusion or root closure. -/
theorem answerMapsCorrect : AnswerMapsCorrect := by
  constructor
  · intro t s h q hAvailable
    cases t with
    | catholic =>
      rcases h with ⟨h0, h1, h2, h3, h4, h5, hGod, hCause, hClaims,
        hAuthority, hRose, hAccount⟩
      cases q with
      | existence => exact hGod
      | causation => exact hCause
      | jesusClaims => exact hClaims
      | authorityVindicated => exact hAuthority
      | resurrection => exact hRose
      | e0 => exact h0
      | e1 => exact h1
      | e2 => exact h2
      | e3 => exact h3
      | e4 => exact h4
      | e5 => exact h5
      | tombAccount => exact hAccount
      | experienceAccount => exact hAccount
      | paulAccount => exact hAccount
      | jamesAccount => exact hAccount
    | legend =>
      rcases h with ⟨h0, h1, h2, h3, h4, h5, hAccount⟩
      cases q with
      | existence => exact Bool.noConfusion hAvailable
      | causation => exact Bool.noConfusion hAvailable
      | jesusClaims => exact Bool.noConfusion hAvailable
      | authorityVindicated => exact Bool.noConfusion hAvailable
      | resurrection => exact hAccount
      | e0 => exact h0
      | e1 => exact h1
      | e2 => exact h2
      | e3 => exact h3
      | e4 => exact h4
      | e5 => exact h5
      | tombAccount => exact Bool.noConfusion hAvailable
      | experienceAccount => exact hAccount
      | paulAccount => exact Bool.noConfusion hAvailable
      | jamesAccount => exact Bool.noConfusion hAvailable
    | hallucination =>
      rcases h with ⟨h0, h1, h2, h3, h4, h5, hAccount⟩
      cases q with
      | existence => exact Bool.noConfusion hAvailable
      | causation => exact Bool.noConfusion hAvailable
      | jesusClaims => exact Bool.noConfusion hAvailable
      | authorityVindicated => exact Bool.noConfusion hAvailable
      | resurrection => exact hAccount
      | e0 => exact h0
      | e1 => exact h1
      | e2 => exact h2
      | e3 => exact h3
      | e4 => exact h4
      | e5 => exact h5
      | tombAccount => exact Bool.noConfusion hAvailable
      | experienceAccount => exact hAccount
      | paulAccount => exact Bool.noConfusion hAvailable
      | jamesAccount => exact Bool.noConfusion hAvailable
    | groupHallucination =>
      rcases h with ⟨h0, h1, h2, h3, h4, h5, hAccount⟩
      cases q with
      | existence => exact Bool.noConfusion hAvailable
      | causation => exact Bool.noConfusion hAvailable
      | jesusClaims => exact Bool.noConfusion hAvailable
      | authorityVindicated => exact Bool.noConfusion hAvailable
      | resurrection => exact hAccount
      | e0 => exact h0
      | e1 => exact h1
      | e2 => exact h2
      | e3 => exact h3
      | e4 => exact h4
      | e5 => exact h5
      | tombAccount => exact Bool.noConfusion hAvailable
      | experienceAccount => exact hAccount
      | paulAccount => exact Bool.noConfusion hAvailable
      | jamesAccount => exact Bool.noConfusion hAvailable
    | stolenBody =>
      rcases h with ⟨h0, h1, h2, h3, h4, h5, hAccount⟩
      cases q with
      | existence => exact Bool.noConfusion hAvailable
      | causation => exact Bool.noConfusion hAvailable
      | jesusClaims => exact Bool.noConfusion hAvailable
      | authorityVindicated => exact Bool.noConfusion hAvailable
      | resurrection => exact hAccount
      | e0 => exact h0
      | e1 => exact h1
      | e2 => exact h2
      | e3 => exact h3
      | e4 => exact h4
      | e5 => exact h5
      | tombAccount => exact hAccount
      | experienceAccount => exact hAccount
      | paulAccount => exact Bool.noConfusion hAvailable
      | jamesAccount => exact Bool.noConfusion hAvailable
    | swoon =>
      rcases h with ⟨h0, h1, h2, h3, h4, h5, hAccount⟩
      cases q with
      | existence => exact Bool.noConfusion hAvailable
      | causation => exact Bool.noConfusion hAvailable
      | jesusClaims => exact Bool.noConfusion hAvailable
      | authorityVindicated => exact Bool.noConfusion hAvailable
      | resurrection => exact hAccount
      | e0 => exact h0
      | e1 => exact h1
      | e2 => exact h2
      | e3 => exact h3
      | e4 => exact h4
      | e5 => exact h5
      | tombAccount => exact hAccount
      | experienceAccount => exact hAccount
      | paulAccount => exact Bool.noConfusion hAvailable
      | jamesAccount => exact Bool.noConfusion hAvailable
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
end TruthCore.Results.Comparison.Resurrection.AnswerMapsCorrect
