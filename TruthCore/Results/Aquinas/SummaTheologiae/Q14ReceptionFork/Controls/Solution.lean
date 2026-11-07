module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question14.ReceptionDefinitionFork
public import TruthCore.Results.Aquinas.SummaTheologiae.Q14ReceptionFork.Strength.Solution

@[expose] public section
namespace TruthCore.Results.Aquinas.SummaTheologiae.Q14ReceptionFork
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.FormReception
open TruthCore.Latin.Aquinas.SummaTheologiae.Q14ReceptionFork

theorem controls : Controls := by
  have materialCapacity : ForeignFormCapacity materialRecipient () :=
    ⟨(), True.intro, .withMatter, rfl⟩
  have materialNotWithout : ¬ WithoutMatterCapacity materialRecipient () := by
    rintro ⟨_, _, h⟩
    exact Mode.noConfusion h
  have dormantWithout : WithoutMatterCapacity dormantRecipient () :=
    ⟨(), True.intro, rfl⟩
  have dormantCapacity : ForeignFormCapacity dormantRecipient () :=
    foreignCapacityOfWithoutMatter dormantRecipient () dormantWithout
  have dormantNoMaterial : NoMaterialReception dormantRecipient () := by
    intro _ h
    exact Mode.noConfusion h
  have dormantNoChange : ¬ ForeignFormChange dormantRecipient noChange () := by
    rintro ⟨_, h, _⟩
    exact h
  have dormantChange : ForeignFormChange dormantRecipient recordedChange () :=
    ⟨(), True.intro, rfl, True.intro, by intro h; cases h⟩
  have remainingNoCapacity : ¬ ForeignFormCapacity remainingRecipient false := by
    rintro ⟨_, _, _, h⟩
    exact h
  have remainingNoWithout : ¬ WithoutMatterCapacity remainingRecipient false := by
    rintro ⟨_, _, h⟩
    exact h
  have remainingNoChange : ¬ ForeignFormChange remainingRecipient remainingChange false := by
    rintro ⟨_, h, _⟩
    exact h
  have noCapacityCalibration : ¬ CapacityCalibration remainingRecipient (fun _ => True) := by
    intro h
    exact remainingNoCapacity ((h false True.intro).mp rfl)
  have noWithoutCalibration : ¬ WithoutMatterCalibration remainingRecipient (fun _ => True) := by
    intro h
    exact remainingNoWithout ((h false True.intro).mp rfl)
  have noChangeCalibration : ¬ ChangeProxyCalibration remainingRecipient remainingChange (fun _ => True) := by
    intro h
    exact remainingNoChange ((h false True.intro).mp rfl)
  refine ⟨availabilityOmission, intellectualGradeOmission, oldTargetOmission,
    ⟨materialCapacity, materialNotWithout, ?_, ?_⟩,
    ⟨True.intro, dormantWithout, dormantNoChange, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_⟩,
    ⟨⟨(), True.intro, rfl, True.intro, by intro h; cases h⟩,
      availabilityOmission.2.2.2⟩,
    ⟨⟨noCapacityCalibration, noWithoutCalibration, noChangeCalibration⟩, ?_, rfl⟩⟩
  · intro x _; cases x
    exact ⟨fun _ => materialCapacity, fun _ => True.intro⟩
  · intro h
    exact materialNotWithout ((h () True.intro).mp True.intro)
  · intro x _; cases x
    exact ⟨fun _ => dormantCapacity, fun _ => True.intro⟩
  · intro x _; cases x
    exact ⟨fun _ => dormantWithout, fun _ => True.intro⟩
  · intro h
    exact dormantNoChange ((h () True.intro).mp True.intro)
  · intro _ _ _; exact True.intro
  · intro x _ _; cases x; exact dormantCapacity
  · intro x _ _; cases x; exact dormantNoMaterial
  · intro _ _ _; exact True.intro
  · intro _ _ _; exact True.intro
  · intro x _ _; cases x; exact dormantChange
  · intro x _; cases x
    exact ⟨fun _ => dormantChange, fun _ => True.intro⟩
  · intro _ _ _; exact True.intro
  · intro h
    rcases h with h | h | h
    · exact noCapacityCalibration h
    · exact noWithoutCalibration h
    · exact noChangeCalibration h

end TruthCore.Results.Aquinas.SummaTheologiae.Q14ReceptionFork
