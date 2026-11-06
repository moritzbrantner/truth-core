module

public import TruthCore.Alternatives.NameApplicationTransfer

@[expose] public section

namespace TruthCore.Results.Alternatives.NameApplicationTransfer.Models

open TruthCore.Alternatives.FideismReference
open TruthCore.Alternatives.NameApplicationTransfer
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Exact semantic-scope obligation; no actual reference theory is adopted. -/
theorem transferModels  : TransferModels := by
  let empty : NamingPractice Unit :=
    { Move := Unit, Correct := fun _ => True, OwnStandard := fun _ => True,
      Defined := fun _ => True, AffirmsNaturalKnowability := fun _ => False,
      AnswersToSharedReason := fun _ => False, Name := Unit,
      RefersTo := fun _ _ => False, ConfessesReferent := fun _ _ => False }
  let full : NamingPractice Unit := { empty with RefersTo := fun _ _ => True }
  let excess : NamingPractice Bool :=
    { Move := Unit, Correct := fun _ => True, OwnStandard := fun _ => True,
      Defined := fun _ => True, AffirmsNaturalKnowability := fun _ => False,
      AnswersToSharedReason := fun _ => False, Name := Unit,
      RefersTo := fun _ _ => True, ConfessesReferent := fun _ _ => False }
  refine ⟨⟨empty, (), (fun _ => True), ⟨(), trivial⟩,
    (fun _ h => h), ⟨(), trivial, fun h => h⟩, ?_⟩,
    ⟨full, (), (fun _ => True), ⟨(), trivial⟩,
      (fun _ => Iff.rfl), (fun _ _ => trivial), ?_⟩,
    ⟨excess, (), (fun b => b = true), ⟨true, rfl⟩,
      (fun _ _ => trivial), ?_⟩⟩
  · intro hTransfer
    exact hTransfer () trivial
  · intro hNoBeing
    exact hNoBeing () trivial
  · intro hShared
    have h : false = true := (hShared false).2 trivial
    cases h

end TruthCore.Results.Alternatives.NameApplicationTransfer.Models
