module
public import TruthCore.Causality.TemporalCoverageEternity
@[expose] public section
namespace TruthCore.Results.Causality.TemporalCoverageEternity
open TruthCore.Causality.TemporalCoverageEternity
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Modal.TemporalHistory

theorem transport : Transport := by
  classical
  intro B T inst l x s hi hs t hp
  induction hp with
  | refl => exact hs
  | @step t u hp edge ih =>
    have he : l x t ↔ l x u := by
      apply Classical.byContradiction
      intro hn
      rcases edge with ht | ht
      · exact hi ⟨t, u, ht, hn⟩
      · exact hi ⟨u, t, ht, fun hr => hn hr.symm⟩
    exact he.mp ih

theorem consumer : Consumer := by
  intro W B T inst h w l x s hc hi hs hb t
  exact hb t (transport B T l x s hi hs t (hc t))

local instance : LT Unit := ⟨fun _ _ => False⟩

theorem controls : Controls := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun _ t => t = true, rfl, ?_, by decide⟩
    rintro ⟨s, t, he, _⟩
    exact he
  · let h : History Unit Unit Unit :=
      { ontic := { frame := { access := fun _ _ => True }, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
        IsAt := fun _ _ _ => False, now := () }
    refine ⟨h, fun _ _ => True, trivial, ?_, ?_, ?_⟩
    · rintro ⟨s, t, he, hn⟩
      exact hn (iff_of_true trivial trivial)
    · intro t; cases t; exact .refl ()
    · intro he; exact he ()
  · let h : History Unit Unit Unit :=
      { ontic := { frame := { access := fun _ _ => True }, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
        IsAt := fun _ _ _ => True, now := () }
    refine ⟨h, fun _ _ => True, trivial, ?_, ?_, ?_, ?_⟩
    · intro t; cases t; exact .refl ()
    · rintro ⟨s, t, he, hn⟩
      exact hn (iff_of_true trivial trivial)
    · intro t ht; trivial
    · intro t; trivial
end TruthCore.Results.Causality.TemporalCoverageEternity
