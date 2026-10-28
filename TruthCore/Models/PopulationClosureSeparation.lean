import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.PopulationClosure

/-! Finite separation for #607. Literal roster identity and a universal frame
are stipulated; no admissibility or metaphysical possibility claim follows. -/
namespace TruthCore.Models.PopulationClosureSeparation
open TruthCore.Modal
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual

/-- Three worlds, with populations abc, bcd and b respectively. -/
inductive World where | abc | bcd | b
  deriving DecidableEq
/-- Four fixed roster members. -/
inductive Individual where | a | b | c | d
  deriving DecidableEq

theorem enumerateWorld (w : World) : w = .abc ∨ w = .bcd ∨ w = .b := by
  cases w with
  | abc => exact Or.inl rfl
  | bcd => exact Or.inr (Or.inl rfl)
  | b => exact Or.inr (Or.inr rfl)

theorem enumerateIndividual (x : Individual) :
    x = .a ∨ x = .b ∨ x = .c ∨ x = .d := by
  cases x with
  | a => exact Or.inl rfl
  | b => exact Or.inr (Or.inl rfl)
  | c => exact Or.inr (Or.inr (Or.inl rfl))
  | d => exact Or.inr (Or.inr (Or.inr rfl))

def frame : Frame World := ⟨fun _ _ => True⟩

def present (x : Individual) (w : World) : Prop :=
  match x with
  | .a => match w with | .abc => True | .bcd => False | .b => False
  | .b => True
  | .c => match w with | .abc => True | .bcd => True | .b => False
  | .d => match w with | .abc => False | .bcd => True | .b => False

/-- The sole member b of the third population belongs to every population.
This supplies a witness for every ordered pair, including equal worlds. -/
theorem amalgamation : AbsenceAmalgamation frame present .abc := by
  intro u v _ _
  refine ⟨.b, trivial, ?_⟩
  intro x hx
  cases x with
  | a => exact False.elim hx
  | b => cases u <;> cases v <;> exact ⟨trivial, trivial⟩
  | c => exact False.elim hx
  | d => exact False.elim hx

/-- The first two populations intersect in bc. None of abc, bcd, b realizes
that exact extension: a, d, and missing c respectively obstruct equality. -/
theorem noExactMeet : ¬ ExactMeetClosure frame present .abc := by
  intro h
  obtain ⟨z, _, hz⟩ := h .abc .bcd trivial trivial
  cases z with
  | abc => exact (hz .a).mp trivial |>.2
  | bcd => exact (hz .d).mp trivial |>.1
  | b => exact (hz .c).mpr ⟨trivial, trivial⟩

/-- A closed finite witness of the weaker policy without exact intersection. -/
def Separation : Prop :=
  AbsenceAmalgamation frame present .abc ∧ ¬ ExactMeetClosure frame present .abc

/-- Universal conditional comparison; no closure premise is asserted true. -/
def ExactImpliesAmalgamation : Prop :=
  ∀ (W I : Type) (F : Frame W) (present : I → W → Prop) (w : W),
    ExactMeetClosure F present w → AbsenceAmalgamation F present w

end TruthCore.Models.PopulationClosureSeparation
