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
  · intro n w
    rcases n with ⟨n, hn⟩
    have casesN : n = 0 ∨ n = 1 ∨ n = 2 := by
      match n with
      | 0 => exact Or.inl rfl
      | 1 => exact Or.inr (Or.inl rfl)
      | 2 => exact Or.inr (Or.inr rfl)
      | k + 3 => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 3 k) hn)
    rcases casesN with h | h | h <;> subst n
    · exact ⟨(false,false), by repeat first | apply List.Mem.head | apply List.Mem.tail, trivial⟩
    · rcases w with ⟨a,b⟩
      cases a
      · exact ⟨(false,false), by repeat first | apply List.Mem.head | apply List.Mem.tail, rfl⟩
      · exact ⟨(true,false), by repeat first | apply List.Mem.head | apply List.Mem.tail, rfl⟩
    · rcases w with ⟨a,b⟩
      cases a <;> cases b
      all_goals exact ⟨_, by repeat first | apply List.Mem.head | apply List.Mem.tail, rfl⟩
  · intro n u hu v hv hp
    rcases n with ⟨n, hn⟩
    have casesN : n = 0 ∨ n = 1 ∨ n = 2 := by
      match n with
      | 0 => exact Or.inl rfl
      | 1 => exact Or.inr (Or.inl rfl)
      | 2 => exact Or.inr (Or.inr rfl)
      | k + 3 => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 3 k) hn)
    rcases casesN with h | h | h <;> subst n
    all_goals
      rcases u with ⟨a,b⟩
      rcases v with ⟨c,d⟩
      cases a <;> cases b <;> cases c <;> cases d
      all_goals
        dsimp only at hu hv hp
        clear hn
        revert hp hv hu
        unfold profile
        dsimp only
        intro hu hv hp
        repeat first | exact rfl | cases hp | cases hu | cases hv | (rename_i h; cases h)
  · decide +kernel
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
  rcases n with ⟨n, hn⟩
  have casesN : n = 0 ∨ n = 1 ∨ n = 2 := by
      match n with
      | 0 => exact Or.inl rfl
      | 1 => exact Or.inr (Or.inl rfl)
      | 2 => exact Or.inr (Or.inr rfl)
      | k + 3 => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 3 k) hn)
  rcases casesN with h | h | h <;> subst n
  · constructor
    · exact fun _ => trivial
    · intro _ p hp
      change p = (fun _ => true) at hp
      subst p
      rfl
  · constructor
    · intro h
      exact (h Prod.fst rfl).symm
    · intro h p hp
      change p = Prod.fst at hp
      subst p
      exact h.symm
  · constructor
    · intro h
      exact Prod.ext (h Prod.fst (Or.inl rfl)).symm
        (h Prod.snd (Or.inr rfl)).symm
    · intro h p _
      change u = v at h
      cases h
      rfl
end TruthCore.Results.Logic.ForeknowledgeDiscrimination
