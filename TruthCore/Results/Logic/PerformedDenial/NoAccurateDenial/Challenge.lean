import TruthCore.Logic.PerformedDenial

namespace TruthCore.Results.Logic.PerformedDenial.NoAccurateDenial
open TruthCore.Logic.PerformedDenial

universe u

/-- No accurate *performed* assertion can deny the occurrence of all episodes
of the very type to which the assertion belongs. No actual token is assumed. -/
theorem noAccurateDenial {Episode : Sort u} (Occurs DeniesAll : Episode → Prop) :
    AccurateDenialImpossible Occurs DeniesAll := by
  sorry

end TruthCore.Results.Logic.PerformedDenial.NoAccurateDenial
