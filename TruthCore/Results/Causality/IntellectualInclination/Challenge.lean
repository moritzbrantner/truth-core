import TruthCore.Causality.IntellectualInclination

namespace TruthCore.Results.Causality.IntellectualInclination
open TruthCore.Causality.IntellectualInclination
open TruthCore.Latin.Aquinas.SummaTheologiae (WillFollowsIntellectReading)

/-- Whatever has intellect is in act through an intelligible form; an
inclination follows every form; an inclination following an intelligible form
is will. Conditional on three OPEN premises. -/
theorem willFromIntellectualInclination {B F : Type} (HasIntellect HasWill : B → Prop)
    (HasForm InclinedTo : B → F → Prop) (Intelligible : F → Prop)
    (hIntellect : IntellectHasIntelligibleForm HasIntellect HasForm Intelligible)
    (hInclination : EveryFormHasInclination HasForm InclinedTo)
    (hWill : IntelligibleInclinationIsWill Intelligible InclinedTo HasWill) :
    WillFollowsIntellectReading HasIntellect HasWill := by
  sorry

theorem controls : TruthCore.Causality.IntellectualInclination.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.IntellectualInclination
