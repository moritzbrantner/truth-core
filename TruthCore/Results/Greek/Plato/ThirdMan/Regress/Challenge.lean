import TruthCore.Greek.Plato.ThirdMan
namespace TruthCore.Results.Greek.Plato.ThirdMan.Regress
open TruthCore.Greek.Plato.Forms TruthCore.Greek.Plato.ThirdMan
universe u v
variable {E : Type u} {Q : Type v}
/-- Conditional Third Man: finite induction constructs unbounded distinct Forms. -/
theorem regress (s : Vocabulary E Q) (eligible : List E → Prop)
    (hSeed : PropertyInstances s) (hScope : InitialScope s eligible)
    (hFormation : Formation s eligible) (hSelf : UniformSelfPredication s)
    (hNonid : ParticipantNonidentity s) (hIteration : Iteration s eligible) :
    UnboundedForms s := by
  sorry
end TruthCore.Results.Greek.Plato.ThirdMan.Regress
