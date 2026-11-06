module

public import TruthCore.Alternatives.ConciliarGrammarDefinitions
public import TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Mixed.Solution

@[expose] public section

namespace TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Models

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.ConciliarGrammarDefinitions

/-- Four nonempty ordinary-life controls and the exact definition-scope boundary. -/
theorem roleModels : ConciliarGrammarModels := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · let P : Practice :=
      { Move := Unit, Correct := fun _ => True, OwnStandard := fun _ => True,
        Defined := fun _ => True, AffirmsNaturalKnowability := fun _ => True,
        AnswersToSharedReason := fun _ => True }
    let R : RoleProfile P := { Theological := fun _ => True, InReligiousLife := fun _ => True }
    refine ⟨P, R, ⟨(fun _ _ => trivial), (fun _ _ => trivial)⟩,
      ⟨(), trivial⟩, ⟨(), trivial, trivial⟩, (fun _ _ => trivial), ?_⟩
    intro hExclusion; exact hExclusion () trivial trivial
  · let P : Practice :=
      { Move := Bool, Correct := fun m => m = true, OwnStandard := fun m => m = true,
        Defined := fun m => m = false, AffirmsNaturalKnowability := fun m => m = false,
        AnswersToSharedReason := fun m => m = false }
    let R : RoleProfile P :=
      { Theological := fun m => m = false, InReligiousLife := fun m => m = true }
    have hNever : DefinitionsNeverOwn P := by
      intro m hDefined hOwn
      exact Bool.noConfusion (hDefined.symm.trans hOwn)
    refine ⟨P, R, ⟨(fun _ h => h), (fun _ h => h)⟩, ⟨false, rfl⟩,
      ⟨true, rfl, rfl⟩, ?_, hNever, ?_, ⟨false, rfl, rfl⟩,
      (fun _ h => h), (fun _ h => h), ?_⟩
    · exact hNever
    · intro hBridge; exact hNever false rfl (hBridge false rfl)
    · intro m hShared hCorrect
      exact Bool.noConfusion (hShared.symm.trans hCorrect)
  · let P : Practice :=
      { Move := Bool, Correct := fun _ => True, OwnStandard := fun m => m = true,
        Defined := fun _ => True, AffirmsNaturalKnowability := fun _ => True,
        AnswersToSharedReason := fun _ => True }
    let R : RoleProfile P := { Theological := fun _ => True, InReligiousLife := fun _ => True }
    have hMixed : MixedDefinitionStatus P := by
      refine ⟨⟨true, trivial, rfl⟩, ⟨false, trivial, ?_⟩⟩
      intro h; cases h
    exact ⟨P, R, ⟨(fun _ _ => trivial), (fun _ _ => trivial)⟩,
      ⟨false, trivial⟩, ⟨true, trivial, rfl⟩, hMixed,
      TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Mixed.mixedRejectsUniform P hMixed⟩
  · let P : Practice :=
      { Move := Unit, Correct := fun _ => True, OwnStandard := fun _ => True,
        Defined := fun _ => False, AffirmsNaturalKnowability := fun _ => False,
        AnswersToSharedReason := fun _ => True }
    let R : RoleProfile P := { Theological := fun _ => False, InReligiousLife := fun _ => True }
    refine ⟨P, R, ?_, ⟨(), trivial, trivial⟩, (fun _ h => False.elim h),
      (fun _ h => False.elim h), (fun _ h => False.elim h)⟩
    intro hWitness; obtain ⟨_, hDefined⟩ := hWitness; exact hDefined

end TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Models
