import TruthCore.Results.Comparison.NaturalisticRealism.Model
namespace TruthCore.Results.Comparison.NaturalisticRealism.NaturalPredicateModusPonens
open TruthCore.Metaethics.NaturalisticRealism
open TruthCore.Comparison.NaturalisticRealism

theorem naturalPredicateModusPonens : NaturalPredicateModusPonens := by
  intro Act Natural p q
  dsimp only [TruthCore.Modal.Holds]
  intro hImp hP
  exact hImp hP

end TruthCore.Results.Comparison.NaturalisticRealism.NaturalPredicateModusPonens
