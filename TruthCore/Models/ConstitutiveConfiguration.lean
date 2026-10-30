import TruthCore.Results.Causality.ConstitutiveConfiguration.Solution
namespace TruthCore.Models.ConstitutiveConfiguration
open TruthCore.Case.Catholicism TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.ConstitutiveNatureUniqueness TruthCore.Causality.ConstitutiveConfiguration
open TruthCore.Causality.PartFreePlurality
open TruthCore.Results.Causality.ConstitutiveConfiguration
def constantNature : Being → Being := fun _ => .left
def changedAct (f : Being) (r : Respect) : Prop := Control.separatingContent (essence f) r
def identityPositive (individual : TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.B) := individual
/-- Each tuple binds the exact assignments named in its model record. -/
def modelIndividual := (moved, moves, inAct, constantNature, constantNature, Control.separatingContent)
def modelNature := (moved, moves, inAct, suppositum, constantNature, Control.separatingContent)
def modelPerfection := (moved, moves, changedAct, suppositum, essence, Control.separatingContent)
def modelIncomplete := (moved, moves, inAct, suppositum, essence, Control.actContent)
def modelMisaligned := (moved, moves, inAct, suppositum, essence, Control.separatingContent)
def modelPositive := (TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.movedIn,
  TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.movesIn,
  TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.inAct,
  identityPositive, identityPositive, Control.positiveContent)
theorem enumerateBeing : ∀ x : Being, x = .left ∨ x = .right ∨ x = .constituent ∨ x = .instrument ∨ x = .effect := by
  intro x
  cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr (Or.inl rfl)) | exact Or.inr (Or.inr (Or.inr (Or.inl rfl))) | exact Or.inr (Or.inr (Or.inr rfl)) | exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
theorem enumerateRespect : ∀ r : Respect, r = .esse ∨ r = .drive ∨ r = .heat := by
  intro r
  cases r <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
theorem enumeratePositiveBeing : ∀ individual : TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.B, individual = .g ∨ individual = .f ∨ individual = .x ∨ individual = .c := by
  intro individual
  cases individual <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr (Or.inl rfl)) | exact Or.inr (Or.inr (Or.inr (Or.inl rfl))) | exact Or.inr (Or.inr (Or.inr rfl)) | exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
theorem enumeratePositiveRespect : ∀ r : TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.R, r = .heat ∨ r = .other := by
  intro r
  cases r <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl
theorem individual0 : type_of% individuation_omission.2.2.2.2.2 := individuation_omission.2.2.2.2.2
theorem individual1 : type_of% individuation_omission.1 := individuation_omission.1
theorem individual2 : type_of% individuation_omission.2.1 := individuation_omission.2.1
theorem individual3 : type_of% individuation_omission.2.2.1 := individuation_omission.2.2.1
theorem individual4 : type_of% individuation_omission.2.2.2.1 := individuation_omission.2.2.2.1
theorem individual5 : type_of% individuation_omission.2.2.2.2.1 := individuation_omission.2.2.2.2.1
theorem nature0 : type_of% nature_omission.1 := nature_omission.1
theorem nature1 : type_of% nature_omission.2.2.2.2.2 := nature_omission.2.2.2.2.2
theorem nature2 : type_of% nature_omission.2.1 := nature_omission.2.1
theorem nature3 : type_of% nature_omission.2.2.1 := nature_omission.2.2.1
theorem nature4 : type_of% nature_omission.2.2.2.1 := nature_omission.2.2.2.1
theorem nature5 : type_of% nature_omission.2.2.2.2.1 := nature_omission.2.2.2.2.1
theorem perfection0 : type_of% perfection_omission.1 := perfection_omission.1
theorem perfection1 : type_of% perfection_omission.2.1 := perfection_omission.2.1
theorem perfection2 : type_of% perfection_omission.2.2.2.2.2 := perfection_omission.2.2.2.2.2
theorem perfection3 : type_of% perfection_omission.2.2.1 := perfection_omission.2.2.1
theorem perfection4 : type_of% perfection_omission.2.2.2.1 := perfection_omission.2.2.2.1
theorem perfection5 : type_of% perfection_omission.2.2.2.2.1 := perfection_omission.2.2.2.2.1
theorem incomplete0 : type_of% original_omissions.2.1 := original_omissions.2.1
theorem incomplete1 : type_of% original_omissions.2.2.1 := original_omissions.2.2.1
theorem incomplete2 : type_of% original_omissions.2.2.2.1 := original_omissions.2.2.2.1
theorem incomplete3 : type_of% original_omissions.2.2.2.2.1 := original_omissions.2.2.2.2.1
theorem incomplete4 : type_of% original_omissions.2.2.2.2.2.1.2 := original_omissions.2.2.2.2.2.1.2
theorem incomplete5 : type_of% original_omissions.2.2.2.2.2.1.1 := original_omissions.2.2.2.2.2.1.1
theorem misaligned0 : type_of% original_omissions.2.1 := original_omissions.2.1
theorem misaligned1 : type_of% original_omissions.2.2.1 := original_omissions.2.2.1
theorem misaligned2 : type_of% original_omissions.2.2.2.1 := original_omissions.2.2.2.1
theorem misaligned3 : type_of% original_omissions.2.2.2.2.1 := original_omissions.2.2.2.2.1
theorem misaligned4 : type_of% original_omissions.2.2.2.2.2.2.1 := original_omissions.2.2.2.2.2.2.1
theorem misaligned5 : type_of% original_omissions.2.2.2.2.2.2.2 := original_omissions.2.2.2.2.2.2.2
theorem positive0 : type_of% TruthCore.Results.Causality.ConstitutiveNatureUniqueness.positiveCertificate.1 := TruthCore.Results.Causality.ConstitutiveNatureUniqueness.positiveCertificate.1
theorem positive1 : type_of% TruthCore.Results.Causality.ConstitutiveNatureUniqueness.positiveCertificate.2.1 := TruthCore.Results.Causality.ConstitutiveNatureUniqueness.positiveCertificate.2.1
theorem positive2 : type_of% TruthCore.Results.Causality.ConstitutiveNatureUniqueness.positiveCertificate.2.2.1 := TruthCore.Results.Causality.ConstitutiveNatureUniqueness.positiveCertificate.2.2.1
theorem positive3 : type_of% TruthCore.Results.Causality.ConstitutiveNatureUniqueness.positiveCertificate.2.2.2.1 := TruthCore.Results.Causality.ConstitutiveNatureUniqueness.positiveCertificate.2.2.2.1
theorem positive4 : type_of% TruthCore.Results.Causality.ConstitutiveNatureUniqueness.positiveCertificate.2.2.2.2.1 := TruthCore.Results.Causality.ConstitutiveNatureUniqueness.positiveCertificate.2.2.2.2.1
theorem positivePlural : ¬ DistinctFirstMoversExist TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.movedIn TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.movesIn := by
  intro h
  exact incompatible _ _ _ _ _ Control.positiveContent positive0 positive1 positive2 h positive3 positive4
end TruthCore.Models.ConstitutiveConfiguration
