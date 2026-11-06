module

public import TruthCore.Alternatives.NaturalReasonHorizon
public import TruthCore.Results.Alternatives.NaturalReasonHorizon.Mixed.Solution

@[expose] public section

namespace TruthCore.Results.Alternatives.NaturalReasonHorizon.Models

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.NaturalReasonHorizon

/-- Fixed practice predicates for a finite scope interpretation, not real
claims about religious users or an authority's actual endorsement. -/
def naturalPractice (shared natural : Bool → Prop) : Practice where
  Move := Bool
  Correct := fun _ => True
  OwnStandard := fun _ => True
  Defined := fun _ => True
  AffirmsNaturalKnowability := natural
  AnswersToSharedReason := shared

/-- Both formal agents are theistic; only one belongs to the practice. -/
def theisticAudience (P : Practice) : Audience P where
  Agent := Bool
  InPractice a := a = true
  Theistic := fun _ => True
  UsesMove := fun _ _ => True

/-- Four exact descriptive-horizon and scope controls. -/
theorem horizonModels : HorizonModels := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · let P := naturalPractice (fun _ => True) (fun _ => True)
    refine ⟨P, theisticAudience P, ⟨?_, ?_⟩, ?_, ⟨false, trivial⟩, ?_, ?_⟩
    · intro _ _ _ _; trivial
    · intro _ _; trivial
    · refine ⟨false, false, ?_, trivial, trivial⟩
      intro hMember; cases hMember
    · intro _ _; trivial
    · intro hNever; exact hNever false trivial trivial
  · let P := naturalPractice (fun _ => False) (fun _ => True)
    refine ⟨P, theisticAudience P, ⟨?_, ?_⟩, ?_, ⟨false, trivial⟩, ?_, ?_⟩
    · intro _ _ _ _; trivial
    · intro _ _; trivial
    · refine ⟨false, false, ?_, trivial, trivial⟩
      intro hMember; cases hMember
    · intro _ _ hShared; exact hShared
    · intro hShared; exact hShared false trivial
  · let P := naturalPractice (fun m => m = true) (fun _ => True)
    have hMixed : MixedNaturalReason P := by
      refine ⟨⟨true, trivial, rfl⟩, ⟨false, trivial, ?_⟩⟩
      intro h; cases h
    refine ⟨P, theisticAudience P, ⟨?_, ?_⟩, ?_, hMixed,
      TruthCore.Results.Alternatives.NaturalReasonHorizon.Mixed.mixedRejectsUniform P hMixed⟩
    · intro _ _ _ _; trivial
    · intro _ _; trivial
    · refine ⟨false, false, ?_, trivial, trivial⟩
      intro hMember; cases hMember
  · refine ⟨naturalPractice (fun _ => False) (fun _ => False), ?_, ?_, ?_⟩
    · intro hWitness; obtain ⟨_, hNatural⟩ := hWitness; exact hNatural
    · intro _ hNatural; exact False.elim hNatural
    · intro _ hNatural; exact False.elim hNatural

end TruthCore.Results.Alternatives.NaturalReasonHorizon.Models
