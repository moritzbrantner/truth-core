import TruthCore.Mereology.UniversalFusionBoundary

namespace TruthCore.Results.Mereology.UniversalFusionBoundary
open TruthCore.Mereology.UniversalFusionBoundary

private theorem unrestricted_greatest (B : Type) [PartialOrder B] [Nonempty B]
    (h : Unrestricted (B := B)) : ∃ u : B, ∀ x, x ≤ u := by
  obtain ⟨x⟩ := ‹Nonempty B›
  obtain ⟨u, hu⟩ := h Set.univ ⟨x, trivial⟩
  exact ⟨u, fun x => hu.1 x trivial⟩

private theorem outside_not_material (B : Type) [PartialOrder B]
    (material : B → Prop) (u : B) (h : Covers material u)
    (c : B) (hc : ¬ c ≤ u) : ¬ material c :=
  fun hm => hc (h c hm)

private theorem bodies_unrestricted : Unrestricted (B := Body) := by
  classical
  intro family hf
  let union : Set Bool := {b | ∃ x ∈ family, b ∈ x.val}
  have hn : union.Nonempty := by
    obtain ⟨x, hx⟩ := hf
    obtain ⟨b, hb⟩ := x.property
    exact ⟨b, x, hx, hb⟩
  refine ⟨⟨union, hn⟩, ?_, ?_⟩
  · intro x hx b hb
    exact ⟨x, hx, hb⟩
  · intro p hp
    obtain ⟨b, hb⟩ := p.property
    obtain ⟨x, hx, hbx⟩ := hp hb
    refine ⟨x, hx, atom b, ?_, ?_⟩
    · intro z hz
      exact (Set.mem_singleton_iff.mp hz) ▸ hb
    · intro z hz
      exact (Set.mem_singleton_iff.mp hz) ▸ hbx

private theorem atom_lt_whole : atom false < whole := by
  constructor
  · intro _ _
    trivial
  · intro h
    have bad : true ∈ (atom false).val := h (by trivial)
    exact Bool.noConfusion bad

private theorem whole_bound (x : Body) : x ≤ whole := by
  intro _ _
  trivial

/-- Concrete fusion model and two ground interpretations preserve exactly the
same Body carrier, partial order and Fusion predicate. -/
theorem checks : Boundary := by
  refine ⟨unrestricted_greatest, outside_not_material, bodies_unrestricted,
    ⟨atom false, atom_lt_whole⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨atom false, ne_of_lt atom_lt_whole, atom_lt_whole⟩
  · intro x ⟨p, hp⟩
    exact ⟨p, ne_of_lt hp, hp⟩
  · intro x hx
    exact lt_irrefl x hx
  · intro h
    obtain ⟨_, _, impossible⟩ := h whole ⟨atom false, atom_lt_whole⟩
    exact impossible
  · intro cause ⟨c, hc, _⟩
    exact hc (whole_bound c)
  · exact ⟨trivial, id⟩

end TruthCore.Results.Mereology.UniversalFusionBoundary
