module

public import TruthCore.Modal.FiniteHitting.Vocabulary
public import TruthCore.Models.FiniteSupport
public import TruthCore.Results.Case.Catholicism.StageOne.FinitePopulationCoverLaws.Solution

/-! Zero-axiom finite registry evaluations of the supported components only.
The Mathlib finite-set/topological controls remain in the main certificate;
the registry is not extended to infinite carriers or proof-valued structures. -/

@[expose] public section
namespace TruthCore.Modal.FiniteHitting.FiniteControls
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual

/-- The issue's two-world {a}/empty control, with unused second roster member. -/
def mixed : Bool → Bool → Prop := fun x v => x = false ∧ v = false
/-- Both worlds have the singleton {a}. -/
def fixed : Bool → Bool → Prop := fun x _ => x = false

def frame : Frame Bool := component Bool

theorem universal : S5Research.Universal frame := fun _ _ => trivial

namespace Alternating

theorem population : DeDicto frame alternatingExists false := fun v _ => ⟨v, rfl⟩

theorem hitting : Hitting alternatingExists := by
  refine ⟨[false, true], fun v => ⟨v, ?_, rfl⟩⟩
  cases v
  · exact List.Mem.head _
  · exact List.Mem.tail _ (List.Mem.head _)

theorem noNecessary : NoNecessary frame alternatingExists false := by
  rintro ⟨x, hx⟩
  exact Bool.false_ne_true ((hx false trivial).symm.trans (hx true trivial))

theorem notAmalgamation : ¬ AbsenceAmalgamation frame alternatingExists false :=
  alternating_not_amalgamation
end Alternating

namespace Mixed

theorem noNecessary : NoNecessary frame mixed false := by
  rintro ⟨x, hx⟩
  exact Bool.noConfusion (hx true trivial).2

theorem notPopulation : ¬ DeDicto frame mixed false := by
  intro hp
  obtain ⟨x, hx⟩ := hp true trivial
  exact Bool.noConfusion hx.2

theorem notHitting : ¬ Hitting mixed := by
  rintro ⟨_, hh⟩
  obtain ⟨_, _, hx⟩ := hh true
  exact Bool.noConfusion hx.2

theorem amalgamation : AbsenceAmalgamation frame mixed false := by
  intro u v _ _
  exact ⟨true, trivial, fun _ hx => False.elim (Bool.noConfusion hx.2)⟩
end Mixed

namespace Fixed

theorem population : DeDicto frame fixed false := fun _ _ => ⟨false, rfl⟩

theorem hitting : Hitting fixed :=
  ⟨[false], fun _ => ⟨false, List.Mem.head _, rfl⟩⟩

theorem necessary : DeRe frame fixed false := ⟨false, fun _ _ => rfl⟩

theorem notNoNecessary : ¬ NoNecessary frame fixed false := fun h => h necessary

theorem amalgamation : AbsenceAmalgamation frame fixed false :=
  fun _ _ _ _ => ⟨false, trivial, fun _ hx => ⟨hx, hx⟩⟩
end Fixed
end TruthCore.Modal.FiniteHitting.FiniteControls
