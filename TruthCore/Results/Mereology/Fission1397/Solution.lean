module
public import TruthCore.Mereology.Fission1397
@[expose] public section
namespace TruthCore.Results.Mereology.Fission1397
open TruthCore.Mereology.Fission1397

theorem rivalControls : RivalControls := by
  refine ⟨?_, ?_, rfl, rfl, ?_, ?_⟩
  · intro w s t h
    have hs := h.1.1.1
    subst s
    cases w with
    | soloLeft =>
      cases t
      · rcases h.1.1.2 with he | he <;> cases he
      · rfl
      · exact False.elim (h.1.2.2 rfl)
    | soloRight =>
      cases t
      · rcases h.1.1.2 with he | he <;> cases he
      · exact False.elim (h.1.2.2 rfl)
      · rfl
    | split =>
      cases t
      · rcases h.1.1.2 with he | he <;> cases he
      · have bad := h.2 .right ⟨⟨rfl, Or.inr rfl⟩, trivial, trivial⟩; cases bad
      · have bad := h.2 .left ⟨⟨rfl, Or.inl rfl⟩, trivial, trivial⟩; cases bad
  · intro w; cases w <;> intro h <;> cases h
  · intro h
    have bad := h.1.mp rfl
    cases bad
  · exact ⟨rfl, (by intro h; cases h), (by
      intro h
      have bad := congrFun h true
      cases bad)⟩

theorem certificate : Certificate := by
  refine ⟨(fun _ c b => incompatible c b),
    (fun _ _ t s f d a b => no_choice t s f d a b),
    (fun _ b => solo_split_conflict b), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rivalControls, ?_⟩
  · refine ⟨⟨rfl, Or.inl rfl⟩, ⟨rfl, Or.inr rfl⟩, ?_, ?_⟩
    · intro h; cases h
    · intro h; have bad := h .earlier .left ⟨rfl, Or.inl rfl⟩; cases bad
  · exact ⟨fun _ _ h => False.elim h, by intro h; cases h⟩
  · exact ⟨fun _ _ _ => rfl, fun h => h rfl⟩
  · exact ⟨(by intro h; cases h), rfl, (by intro h; cases h)⟩
  · refine ⟨rfl, ?_⟩
    intro h; have bad := h (); cases bad
  · refine ⟨fun _ => rfl, ?_⟩
    intro h; rcases h with h | h <;> cases h
  · exact ⟨(by intro d; cases d <;> rfl), rfl, (by intro h; cases h)⟩
  · exact ⟨fun _ => rfl, rfl, (by intro h; cases h)⟩
  · exact ⟨fun _ => rfl, rfl, rfl⟩
  · exact ⟨(by intro s t h; rcases h with ⟨rfl, rfl⟩; rfl), (by intro h; cases h)⟩
  · exact ⟨(by intro s t h; rcases h with ⟨rfl, rfl⟩; rfl), (by intro h; cases h)⟩
  · exact ⟨(by intro s; cases s <;> rfl), rfl, rfl, rfl,
      (by intro s t; unfold branching; cases s <;> cases t <;> decide)⟩
end TruthCore.Results.Mereology.Fission1397
