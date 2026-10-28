import TruthCore.Modal.BearerExercise
namespace TruthCore.Results.Modal.BearerExercise
open TruthCore.Modal.BearerExercise
open TruthCore.Modal.NecessaryVariableEffects
open TruthCore.Modal.NecessaryContingentActivity
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Isabelle.AFP.GoedelGod (Box)

theorem checks : Comparison := by
  unfold Comparison
  refine ⟨TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.CausalPowers.checks,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨effectsSound, sourceNecessaryAt, alwaysCausesSomething, noFixedEffect,
    firstEffectContingent, ?_⟩, fun _ _ => necessaryExercise⟩
  all_goals
    dsimp only [SoundDistinctCauses, NecessaryAt, NecessarilyCausesSomething,
      ExercisesCausation, Box, responseOntic, directed, alternatingFrame,
      CausalPowers.Capacity, CausalPowers.existsAt, CausalPowers.response,
      alternatingEffects]
    decide
end TruthCore.Results.Modal.BearerExercise
