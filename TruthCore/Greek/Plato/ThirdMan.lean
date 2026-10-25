import TruthCore.Greek.Plato.Forms

/-! Parmenides 132a–b and 132d–133a: independently challengeable reconstructions.
The shared Forms vocabulary is unchanged. Eligibility models the disputed domain
of the formation rule; it is not inferred from ordinary self-predication.
All strengthened schemata here are explicit research premises, not dialogue-wide
attributions. No temporal production, causal priority, or verdict on Platonism
is built into a list of numerically distinct Forms. -/
namespace TruthCore.Greek.Plato.ThirdMan
open TruthCore.Greek.Plato.Forms
universe u v
variable {E : Type u} {Q : Type v}

/-- Direct elimination of inductive membership, avoiding extensional simp lemmas. -/
theorem consCases {x a : E} {xs : List E} (h : x ∈ a :: xs) : x = a ∨ x ∈ xs := by
  cases h with
  | head => exact Or.inl rfl
  | tail _ h => exact Or.inr h

theorem pairCases {x a b : E} (h : x ∈ [a,b]) : x = a ∨ x = b := by
  rcases consCases h with h | h
  · exact Or.inl h
  · rcases consCases h with h | h
    · exact Or.inr h
    · cases h

/-- A genuine plurality, even if its list presentation contains repetitions. -/
def Plural (xs : List E) : Prop := ∃ a ∈ xs, ∃ b ∈ xs, a ≠ b

/-- The first ordinary pair is eligible. This is a scope commitment separate
from applying formation again to a list containing Forms (132a–b). -/
def InitialScope (s : Vocabulary E Q) (eligible : List E → Prop) : Prop :=
  ∀ a b, s.Particular a → s.Particular b → eligible [a,b]

/-- One over an eligible plurality of ordinary F-bearers. Unlike the foundational
OneOverMany, its domain may include Forms. It does not assert uniqueness. -/
def Formation (s : Vocabulary E Q) (eligible : List E → Prop) : Prop :=
  ∀ q, s.Admitted q → ∀ xs, eligible xs → Plural xs →
    (∀ x ∈ xs, s.Exemplifies x q) →
    ∃ f, s.FormOf f q ∧ ∀ x ∈ xs, s.Participates x f

/-- Participant-wide numerical nonidentity. Each Form differs from EVERY entity
participating in it, including other Forms, not merely ordinary particulars.
This is stronger than Forms.Nonidentity; ontological independence is unrelated. -/
def ParticipantNonidentity (s : Vocabulary E Q) : Prop :=
  ∀ q, s.Admitted q → ∀ f x, s.FormOf f q → s.Participates x f → f ≠ x

/-- Eligibility is closed under adjoining any Form of the same admitted quality.
Together with ordinary self-predication this permits repeated formation. This
universal closure is an explicit reconstruction of 'over all these again' (132b). -/
def Iteration (s : Vocabulary E Q) (eligible : List E → Prop) : Prop :=
  ∀ q, s.Admitted q → ∀ xs f, eligible xs → s.FormOf f q → eligible (f :: xs)

/-- Arbitrarily long finite lists of pairwise numerically distinct Forms, all of
ONE quality. No order of causal dependence or premise of infinity is asserted. -/
def UnboundedForms (s : Vocabulary E Q) : Prop :=
  ∃ q, s.Admitted q ∧ ∀ n : Nat, ∃ fs : List E,
    fs.length = n ∧ fs.Pairwise (· ≠ ·) ∧ ∀ f ∈ fs, s.FormOf f q

/-- Mutual resemblance in the selected respect; unlike directed imitation,
each distinct ordered pair must stand in Like. No transitivity is assumed. -/
def MutuallyLike (s : Vocabulary E Q) (xs : List E) : Prop :=
  ∀ x ∈ xs, ∀ y ∈ xs, x ≠ y → s.Like x y

/-- 132d–e reconstruction: mutually resembling entities participate in a common
Form (the designated likeness quality q). Not ordinary F-self-predication. -/
def LikenessFormation (s : Vocabulary E Q) (eligible : List E → Prop) (q : Q) : Prop :=
  ∀ xs, eligible xs → Plural xs → MutuallyLike s xs →
    ∃ f, s.FormOf f q ∧ ∀ x ∈ xs, s.Participates x f

/-- The resemblance involved in 132e is symmetric, unlike copying/modelhood. -/
def LikenessSymmetry (s : Vocabulary E Q) : Prop :=
  ∀ x y, s.Like x y → s.Like y x

/-- 132d / 133a: the contested account makes participation yield resemblance
to the participated Form. Neither Forms.ExemplarParticipation nor explanation
alone includes this bridge. -/
def ParticipationLikeness (s : Vocabulary E Q) : Prop :=
  ∀ x f, s.Participates x f → s.Like x f

/-- Initial distinct resembling pair in the admitted likeness domain. It may be
a copy and paradigm, not necessarily two ordinary particulars (132d–e). -/
def LikenessSeed (s : Vocabulary E Q) (eligible : List E → Prop) (q : Q) : Prop :=
  s.Admitted q ∧ ∃ a b, a ≠ b ∧ eligible [a,b] ∧ s.Like a b ∧ s.Like b a

end TruthCore.Greek.Plato.ThirdMan
