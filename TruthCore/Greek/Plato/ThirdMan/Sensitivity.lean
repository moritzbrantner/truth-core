import TruthCore.Greek.Plato.ThirdMan
namespace TruthCore.Greek.Plato.ThirdMan
open TruthCore.Greek.Plato.Forms
universe u v

/-- Three entities on the SAME type, not a type-level separation of Forms. -/
inductive Small where
  | form | a | b
  deriving DecidableEq

/-- One Form, two ordinary particulars; ordinary self-predication, directed
participation and essential characterization. Generic resemblance is absent. -/
def small : Vocabulary Small Unit where
  Particular x := x ≠ .form
  Admitted _ := True
  FormOf f _ := f = .form
  Exemplifies _ _ := True
  Participates x f := x ≠ .form ∧ f = .form
  Independent f := f = .form
  Intelligible f := f = .form
  Unchanging f := f = .form
  Explains f x _ := f = .form ∧ x ≠ .form
  ModelFor f x := f = .form ∧ x ≠ .form
  Imitates x f := x ≠ .form ∧ f = .form
  Like _ _ := False
  Essentially f _ := f = .form

def ordinaryOnly (xs : List Small) : Prop := ∀ x ∈ xs, x ≠ .form

def nonSelf : Vocabulary Small Unit :=
  { small with Exemplifies x _ := x ≠ .form }

def selfParticipating : Vocabulary Small Unit :=
  { small with Participates _ f := f = .form }

/-- Copy-to-model direction, deliberately not symmetric generic resemblance. -/
def directed : Vocabulary Small Unit :=
  { small with Like x y := x ≠ .form ∧ x ≠ y }

/-- Resemblance of the two particulars does not make participation resemblance. -/
def nonResemblance : Vocabulary Small Unit :=
  { small with Like x y := x ≠ .form ∧ y ≠ .form ∧ x ≠ y }

/-- First sensitivity: formation is absent; all other Third Man premises hold. -/
def WithoutFormation : Prop :=
  ∃ s : Vocabulary Small Unit, PropertyInstances s ∧ InitialScope s (fun _ => True) ∧
    UniformSelfPredication s ∧ ParticipantNonidentity s ∧ Iteration s (fun _ => True) ∧
    ¬ Formation s (fun _ => True) ∧ ¬ UnboundedForms s

def WithoutSelfPredication : Prop :=
  ∃ s : Vocabulary Small Unit, PropertyInstances s ∧ InitialScope s (fun _ => True) ∧
    Formation s (fun _ => True) ∧ ParticipantNonidentity s ∧ Iteration s (fun _ => True) ∧
    EssentialCharacterization s ∧ ¬ UniformSelfPredication s ∧ ¬ UnboundedForms s

def WithoutNonidentity : Prop :=
  ∃ s : Vocabulary Small Unit, PropertyInstances s ∧ InitialScope s (fun _ => True) ∧
    Formation s (fun _ => True) ∧ UniformSelfPredication s ∧ Iteration s (fun _ => True) ∧
    ¬ ParticipantNonidentity s ∧ ¬ UnboundedForms s

def WithoutIteration : Prop :=
  ∃ s : Vocabulary Small Unit, PropertyInstances s ∧ InitialScope s ordinaryOnly ∧
    Formation s ordinaryOnly ∧ UniformSelfPredication s ∧ ParticipantNonidentity s ∧
    OneOverMany s ∧ UniqueForms s ∧ ExplanatoryParticipation s ∧
    ExemplarParticipation s ∧ OntologicalSeparation s ∧
    ¬ Iteration s ordinaryOnly ∧ ¬ UnboundedForms s

/-- Mutual likeness formation, likeness seed and participation→directed likeness
hold, but symmetry fails. This isolates symmetry rather than denying all likeness. -/
def WithoutSymmetry : Prop :=
  ∃ s : Vocabulary Small Unit, LikenessSeed s (fun _ => True) () ∧
    LikenessFormation s (fun _ => True) () ∧ ParticipationLikeness s ∧
    ParticipantNonidentity s ∧ Iteration s (fun _ => True) ∧
    ¬ LikenessSymmetry s ∧ ¬ UnboundedForms s

/-- Symmetric resemblance/common Form remains; participation need not resemble. -/
def WithoutLikenessBridge : Prop :=
  ∃ s : Vocabulary Small Unit, LikenessSeed s (fun _ => True) () ∧
    LikenessFormation s (fun _ => True) () ∧ LikenessSymmetry s ∧
    ParticipantNonidentity s ∧ Iteration s (fun _ => True) ∧
    ¬ ParticipationLikeness s ∧ ¬ UnboundedForms s

/-- Concrete countermodels, not failures of proof search. Each negates the
regress while retaining the other named premises. -/
def SensitivityModels : Prop :=
  WithoutFormation ∧ WithoutSelfPredication ∧ WithoutNonidentity ∧
  WithoutIteration ∧ WithoutSymmetry ∧ WithoutLikenessBridge

def NotUniqueForms {E : Type u} {Q : Type v} (s : Vocabulary E Q) : Prop :=
  ¬ UniqueForms s
end TruthCore.Greek.Plato.ThirdMan
