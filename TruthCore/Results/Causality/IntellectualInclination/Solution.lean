module

public import TruthCore.Causality.IntellectualInclination

@[expose] public section

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
  intro x hx
  obtain ⟨f, hIntelligible, hForm⟩ := hIntellect x hx
  exact hWill x f hIntelligible (hInclination x f hForm)

section Controls
open TruthCore.Causality.IntellectualInclination.Control

theorem hasIntelligible : IntellectHasIntelligibleForm intellect intelligibleForm intelligible :=
  fun _ _ => ⟨true, rfl, rfl⟩

theorem noWill : ¬ WillFollowsIntellectReading intellect (fun (_ : Unit) => False) :=
  fun h => h () trivial

theorem controls : Certificate :=
  ⟨⟨fun h => h () true rfl, hasIntelligible, fun _ _ _ h => h, noWill⟩,
    ⟨fun _ _ h => h, fun h => (h () trivial).elim (fun _ ⟨hT, hF⟩ => Bool.noConfusion (hT.symm.trans hF)),
      fun _ _ hT hF => Bool.noConfusion (hT.symm.trans hF), noWill⟩,
    ⟨fun _ _ h => h, hasIntelligible, fun h => h () true rfl rfl, noWill⟩,
    ⟨fun _ _ h => h, hasIntelligible, fun _ _ _ _ => trivial, fun _ _ => trivial⟩⟩

end Controls

end TruthCore.Results.Causality.IntellectualInclination
