import TruthCore.Logic.PerformedDenial

namespace TruthCore.Results.Logic.PerformedDenial.NoAccurateDenial
open TruthCore.Logic.PerformedDenial

/-- Retorsion is conditional on a token's occurrence and the denial's being
true. Merely expressing the denial is compatible with its falsity. -/
theorem noAccurateDenial {Episode : Sort u} (Occurs DeniesAll : Episode → Prop) :
    AccurateDenialImpossible Occurs DeniesAll := by
  rintro ⟨e, hOccurs, _, hNo⟩
  exact hNo ⟨e, hOccurs⟩

end TruthCore.Results.Logic.PerformedDenial.NoAccurateDenial
