module

public import TruthCore.Metaethics.AdoptionReasons

@[expose] public section

namespace TruthCore.Results.Metaethics.AdoptionReasons
open TruthCore.Logic.EpistemicReasons
open TruthCore.Metaethics.AdoptionReasons

/-- A denial of all reasons of one kind applies to adoption of the view. -/
theorem kindDenialLeavesAdoptionGap {Kind Agent Target : Type}
    (reason : Kind → Agent → Target → Prop) (kind : Kind) (view : Target)
    (hDenial : NoReasonsOfKind reason kind) :
    NoInternalAdoptionReason reason kind view := by
  intro agent
  exact hDenial agent view

/-- A denial across all represented kinds leaves an adoption gap in every kind. -/
theorem globalDenialLeavesAdoptionGap {Kind Agent Target : Type}
    (reason : Kind → Agent → Target → Prop) (view : Target)
    (hDenial : GlobalNormativeNihilism reason) :
    NoInternalAdoptionReasonOfAnyKind reason view := by
  intro kind
  exact kindDenialLeavesAdoptionGap reason kind view (hDenial kind)

/-- The global denial is incompatible with a witness for the existing F6
proposition when its reason relation is the epistemic kind in this profile. -/
theorem epistemicReasonExcludesGlobalDenial {Kind Agent Target : Type}
    (reason : Kind → Agent → Target → Prop) (epistemic : Kind)
    (hEpistemic : ThereAreEpistemicReasons (reason epistemic)) :
    GlobalNormativeNihilismExcluded reason := by
  intro hDenial
  obtain ⟨agent, target, hReason⟩ := hEpistemic
  exact hDenial epistemic agent target hReason

/-- The restriction to one kind matters. In this profile the epistemic reason
for the selected target exists even though the moral relation is empty. -/
theorem moralDenialAllowsEpistemicAdoption :
    MoralDenialEpistemicAdoptionControl := by
  let reason : Bool → Unit → Bool → Prop := fun kind _ target =>
    kind = true ∧ target = true
  have hMoral : NoReasonsOfKind reason false := by
    intro _ _ hReason
    exact Bool.noConfusion hReason.1
  have hEpistemic : reason true () true := ⟨rfl, rfl⟩
  let Holds : Bool → Prop := fun target => target = true ∧ NoReasonsOfKind reason false
  have hExpresses : Holds true ↔ NoReasonsOfKind reason false :=
    ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
  exact ⟨reason, Holds, hExpresses, hExpresses.mpr hMoral,
    kindDenialLeavesAdoptionGap reason false true hMoral, hEpistemic, ⟨(), true, hEpistemic⟩⟩

end TruthCore.Results.Metaethics.AdoptionReasons
