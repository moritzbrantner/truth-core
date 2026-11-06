module

public import TruthCore.Causality.MaximumDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.MaximumDefinitions.Controls
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.MaximumDefinitionFork

/-- Frozen exact finite boundaries; no philosophical ontology is asserted. -/
theorem controls : Controls := by
  have noGreatest : ∀ m, ¬ GreatestDegreeBearer incomparable.InAct
      incomparable.selected incomparable.value m := by
    intro m h
    cases m with
    | false =>
      have hh := h.2.2 ⟨true, True.intro, rfl⟩
      exact (by decide : ¬ ((true : Bool) ≤ false)) hh.1
    | true =>
      have hh := h.2.2 ⟨false, True.intro, rfl⟩
      exact (by decide : ¬ ((true : Bool) ≤ false)) hh.2
  have maximalIncomparable : ∀ m,
      IsMaximumIn incomparable.InAct incomparable.MoreIn incomparable.selected m :=
    fun _ => ⟨True.intro, fun _ h => h⟩
  have maximalTied : ∀ m, IsMaximumIn tied.InAct tied.MoreIn tied.selected m :=
    fun _ => ⟨True.intro, fun _ h => h⟩
  have greatestTied : ∀ m, GreatestDegreeBearer tied.InAct tied.selected tied.value m := by
    intro m
    refine ⟨True.intro, ⟨⟨m, True.intro, rfl⟩, ?_⟩⟩
    intro d hd
    obtain ⟨x, _, hx⟩ := hd
    rw [← hx]
  have notStrictTied : ∀ m, ¬ StrictGreatest tied m := by
    intro m h
    cases m with
    | false => exact (lt_irrefl ()) (h.2 true True.intro Bool.noConfusion)
    | true => exact (lt_irrefl ()) (h.2 false True.intro Bool.noConfusion)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x y _ _
    constructor
    · intro h; exact False.elim h
    · intro h
      cases x <;> cases y
      · exact (lt_irrefl _) h
      · exact (by decide : ¬ ((true : Bool) ≤ false)) (le_of_lt h).1
      · exact (by decide : ¬ ((true : Bool) ≤ false)) (le_of_lt h).2
      · exact (lt_irrefl _) h
  · intro m; exact ⟨fun _ => maximalIncomparable m, fun _ => True.intro⟩
  · intro h; exact noGreatest false ((h false).mp True.intro)
  · intro h; exact noGreatest false (h false (maximalIncomparable false))
  · intro m h; exact False.elim (noGreatest m h)
  · intro h
    exact h false (maximalIncomparable false) true Bool.noConfusion True.intro
  · intro x y _ _; exact ⟨false, True.intro, le_rfl, le_rfl⟩
  · intro x y _ _
    exact ⟨fun h => False.elim h, fun h => False.elim ((lt_irrefl ()) h)⟩
  · intro m; exact ⟨fun _ => maximalTied m, fun _ => True.intro⟩
  · intro m; exact ⟨fun _ => greatestTied m, fun _ => True.intro⟩
  · intro h; exact notStrictTied false ((h false).mp True.intro)
  · exact ⟨false, true, Bool.noConfusion, greatestTied false, greatestTied true⟩
  · intro h; exact Bool.noConfusion ((h false).mpr (maximalTied false))
  · intro h; exact Bool.noConfusion ((h false).mpr (greatestTied false))
  · intro h; exact notStrictTied true ((h true).mp rfl)

end TruthCore.Results.Causality.MaximumDefinitions.Controls
