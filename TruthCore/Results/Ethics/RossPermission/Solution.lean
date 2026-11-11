module
public import TruthCore.Ethics.RossPermission
public import Mathlib.Logic.Function.Basic
@[expose] public section
namespace TruthCore.Results.Ethics.RossPermission
open TruthCore.Modal TruthCore.Modal.DeonticFutureBoundary TruthCore.Ethics.RossPermission

theorem weakening (i : Frame W) w (p q : W → Prop) (h : Ought i w p) :
    Ought i w (fun a => p a ∨ q a) := fun a ha => Or.inl (h a ha)

theorem guarded (i : Frame W) w (p q : W → Prop)
    (h : Ought i w (fun a => p a ∨ q a)) (hn : ¬ Ought i w p) : Weak i w q := by
  classical
  apply Classical.byContradiction
  intro hh
  apply hn
  intro a ha
  rcases h a ha with hp | hq
  · exact hp
  · exact False.elim (hh ⟨a, ha, hq⟩)

theorem exclusive (i : Frame W) w (p q : W → Prop)
    (h : Ought i w (fun a => p a ∨ q a))
    (he : ∀ a, i.access w a → ¬ (p a ∧ q a)) : Weak i w q ↔ ¬ Ought i w p := by
  constructor
  · rintro ⟨a, ha, hq⟩ hp
    exact he a ha ⟨hp a ha, hq⟩
  · exact guarded i w p q h

theorem certificate : TruthCore.Ethics.RossPermission.Certificate := by
  refine ⟨fun _ => weakening, ?_, fun _ => guarded, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W i w p
    classical
    constructor
    · rintro ⟨a, ha, hp⟩ hn
      exact hn a ha hp
    · intro hn
      apply Classical.byContradiction
      intro hh
      apply hn
      intro a ha hp
      exact hh ⟨a, ha, hp⟩
  · intro W i w p q h hp hq
    exact ⟨guarded i w q p (fun a ha => (h a ha).symm) hq, guarded i w p q h hp⟩
  · intro W i w p q h he
    exact ⟨exclusive i w p q h he,
      exclusive i w q p (fun a ha => (h a ha).symm)
        (fun a ha hh => he a ha hh.symm)⟩
  · refine ⟨fun _ => ⟨.mail, rfl⟩, fun _ ha => ha,
      fun _ ha => Or.inl ha, ?_⟩
    rintro ⟨a, ha, hb⟩
    cases ha
    cases hb
  · refine ⟨fun _ => ⟨.mail, Or.inl rfl⟩, fun _ ha => ha, ?_, ?_,
      ⟨.mail, Or.inl rfl, rfl⟩, ⟨.burn, Or.inr rfl, rfl⟩, id, id⟩
    · intro h
      have hh := h .burn (Or.inr rfl)
      cases hh
    · intro h
      have hh := h .mail (Or.inl rfl)
      cases hh
  · exact ⟨⟨.mail, rfl, rfl⟩, fun _ ha => ha, fun _ ha => Or.inl ha⟩
  · refine ⟨fun _ => Iff.rfl, ?_⟩
    intro h
    have hh := (h .burn).mp (Or.inr rfl)
    cases hh
  · intro W i w p q n hp hq bridge
    exact ⟨bridge p hp, bridge q hq⟩
end TruthCore.Results.Ethics.RossPermission
