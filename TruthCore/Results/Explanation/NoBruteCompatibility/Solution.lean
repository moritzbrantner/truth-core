import TruthCore.Models.NoBruteExistenceCompatibility
namespace TruthCore.Results.Explanation.NoBruteCompatibility
/-- Relative explanatory coverage does not rule out the existing contingent,
well-founded grounding-brute rival or imply a necessary concrete individual. -/
theorem checks : TruthCore.Models.NoBruteExistenceCompatibility.JointWitness := by
  exact TruthCore.Models.NoBruteExistenceCompatibility.jointWitness
end TruthCore.Results.Explanation.NoBruteCompatibility
