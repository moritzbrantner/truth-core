module
public import TruthCore.Logic.ForeknowledgeDiscrimination
@[expose] public section
namespace TruthCore.Results.Logic.ForeknowledgeDiscrimination
open TruthCore.Logic.ForeknowledgeDiscrimination
open TruthCore.Modal
open TruthCore.Logic.JustificationIntrospection
theorem core : Core := by
  have equiv : ∀ (W : Type) (E : Frame W) C w,
      Complete E C w ↔ ∀ v, E.access w v → TruthClass C w v := by
    intro W E C w
    constructor
    · intro h v hv p hp
      cases hw : p w with
      | false => exact (h p hp).2 hw v hv
      | true => exact (h p hp).1 hw v hv
    · intro h p hp
      constructor <;> intro hw v hv
      · exact (h v hv p hp).trans hw
      · exact (h v hv p hp).trans hw
  have discr : ∀ (W : Type) (E : Frame W) C u v,
      E.access u u → E.access v v → Complete E C u → Complete E C v →
      (∃ p, C p ∧ p u ≠ p v) → ¬ (∀ x, E.access u x ↔ E.access v x) := by
    intro W E C u v _ hv hu _ hd same
    obtain ⟨p, hp, hn⟩ := hd
    exact hn (((equiv W E C u).1 hu v ((same v).2 hv) p hp).symm)
  refine ⟨equiv, discr, ?_⟩
  intro W S E C I u v hs hi hu hv hcu hcv hd
  exact discr W E C u v hu hv hcu hcv hd (hs u v hi)
theorem controls : Controls := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w p hp
    subst p
    constructor <;> intro hw v hv <;> subst v <;> exact hw
  · intro h
    have bad := (h id rfl).2 rfl true trivial
    cases bad
  · intro w p hp
    constructor <;> intro _ v hv <;> cases hv
  · intro w p hp
    subst p
    exact ⟨fun _ _ _ => rfl, fun h => Bool.noConfusion h⟩
  · intro n
    have hn : n.val = 0 ∨ n.val = 1 ∨ n.val = 2 := by omega
    intro w
    rcases hn with h | h | h <;> rcases w with ⟨a,b⟩ <;> cases a <;> cases b <;> simp [classes, profile, h]
  · intro n u hu v hv
    have hn : n.val = 0 ∨ n.val = 1 ∨ n.val = 2 := by omega
    rcases hn with h | h | h <;> simp [classes, h] at hu hv <;> rcases u with ⟨a,b⟩ <;> rcases v with ⟨c,d⟩ <;> cases a <;> cases b <;> cases c <;> cases d <;> simp_all [profile]
  · decide
theorem canonicalCertificate : CanonicalCertificate := by
  intro W C
  have refl : Reflexive (canonical (W := W) C) := fun _ _ _ => rfl
  have symm : Symmetric (canonical (W := W) C) := fun _ _ h p hp => (h p hp).symm
  have trans : Transitive (canonical (W := W) C) :=
    fun _ _ _ h k p hp => (k p hp).trans (h p hp)
  refine ⟨refl, symm, trans, ?_, ?_⟩
  · intro w
    exact (core.1 W (canonical C) C w).2 (fun _ h => h)
  · intro u v
    constructor
    · intro h x
      exact ⟨fun k => trans _ _ _ (symm _ _ h) k,
        fun k => trans _ _ _ h k⟩
    · intro h
      exact (h v).2 (refl v)
theorem finiteProfiles : FiniteProfiles := by
  intro n u v
  have hn : n.val = 0 ∨ n.val = 1 ∨ n.val = 2 := by omega
  rcases u with ⟨a,b⟩
  rcases v with ⟨c,d⟩
  rcases hn with h | h | h <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp [TruthClass, family, profile, h]
end TruthCore.Results.Logic.ForeknowledgeDiscrimination
