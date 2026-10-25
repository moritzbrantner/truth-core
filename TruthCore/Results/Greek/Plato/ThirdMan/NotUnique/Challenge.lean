import TruthCore.Greek.Plato.ThirdMan.Sensitivity
namespace TruthCore.Results.Greek.Plato.ThirdMan.NotUnique
open TruthCore.Greek.Plato.Forms TruthCore.Greek.Plato.ThirdMan
universe u v
/-- The derived plurality is incompatible with numerical uniqueness. -/
theorem notUnique {E : Type u} {Q : Type v} (s : Vocabulary E Q)
    (h : UnboundedForms s) : NotUniqueForms s := by
  sorry
end TruthCore.Results.Greek.Plato.ThirdMan.NotUnique
