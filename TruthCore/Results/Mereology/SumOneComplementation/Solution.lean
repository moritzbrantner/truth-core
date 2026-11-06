module

public import TruthCore.Mereology.SumOneComplementation
public import TruthCore.Results.Mereology.SupplementationFusion.Solution
public import Mathlib.Tactic.Tauto

/-! Conditional exact-remainder bridge and joint omission controls for #1054.
No premise is silently identified with ordinary physical parthood. -/

@[expose] public section

namespace TruthCore.Results.Mereology.SumOneComplementation
open TruthCore.Mereology.UniversalFusionBoundary
open TruthCore.Mereology.SupplementationFusion (StrongSupplementation)
open TruthCore.Mereology.SumOneComplementation

/-- A remainder's reflexive self-part supplies the weaker separating witness. -/
theorem strongOfComplementation (B : Type) [PartialOrder B]
    (hComplement : Complementation B) : StrongSupplementation B := by
  intro x y hNotPart
  obtain ⟨z, hz⟩ := hComplement y x hNotPart
  exact ⟨z, (hz z).mp le_rfl⟩

/-- Leastness excludes extra parts because their exact remainder would still
bound every member. The reverse imports the existing SS/extensionality result. -/
theorem sumOneComparison (B : Type) [PartialOrder B]
    (hComplement : Complementation B) : SumOneComparison B := by
  classical
  intro family hNonempty u
  constructor
  · intro hLUB
    refine ⟨hLUB.1, ?_⟩
    intro p hpu
    by_contra hNone
    have hDisjoint : ∀ x ∈ family, ¬ Overlap x p := by
      rintro x hx ⟨q, hqx, hqp⟩
      exact hNone ⟨x, hx, q, hqp, hqx⟩
    have hNotUp : ¬ u ≤ p := by
      intro hup
      obtain ⟨x, hx⟩ := hNonempty
      exact hDisjoint x hx ⟨x, le_rfl, le_trans (hLUB.1 hx) hup⟩
    obtain ⟨d, hd⟩ := hComplement p u hNotUp
    have hBound : d ∈ upperBounds family := by
      intro x hx
      exact (hd x).mpr ⟨hLUB.1 hx, hDisjoint x hx⟩
    have hpd : p ≤ d := le_trans hpu (hLUB.2 hBound)
    exact ((hd p).mp hpd).2 ⟨p, le_rfl, le_rfl⟩
  · intro hFusion
    refine ⟨hFusion.1, ?_⟩
    intro v hv
    apply ((SupplementationFusion.separationCharacterization B).mp
      (strongOfComplementation B hComplement) u v).mpr
    rintro p ⟨q, hqp, hqu⟩
    obtain ⟨x, hx, r, hrq, hrx⟩ := hFusion.2 q hqu
    exact ⟨r, le_trans hrq hqp, le_trans hrx (hv hx)⟩

/-- Convert actual supplied joins, rather than assuming new Sum2 witnesses. -/
theorem unrestrictedTransfer (B : Type) [PartialOrder B]
    (hComplement : Complementation B) (hSumOne : UnrestrictedSumOne B) :
    Unrestricted (B := B) := by
  intro family hNonempty
  obtain ⟨u, hu⟩ := hSumOne family hNonempty
  exact ⟨u, (sumOneComparison B hComplement family hNonempty u).mp hu⟩

private theorem joinRival_all (P : JoinRival → Prop) :
    (∀ x, P x) ↔ P .a ∧ P .b ∧ P .c ∧ P .top := by
  constructor
  · intro h; exact ⟨h .a, h .b, h .c, h .top⟩
  · rintro ⟨ha, hb, hc, ht⟩ x; cases x <;> assumption

private theorem joinRival_ex (P : JoinRival → Prop) :
    (∃ x, P x) ↔ P .a ∨ P .b ∨ P .c ∨ P .top := by
  constructor
  · rintro ⟨x, hx⟩; cases x <;> tauto
  · rintro (h | h | h | h)
    · exact ⟨.a, h⟩
    · exact ⟨.b, h⟩
    · exact ⟨.c, h⟩
    · exact ⟨.top, h⟩

private theorem joinRival_le (x y : JoinRival) : x ≤ y ↔ rivalPart x y := Iff.rfl

/-- Every nonempty Set is a singleton, whose join is its member, or its only
upper bound is top. This covers every family, not selected enumerated cases. -/
private theorem allJoins : UnrestrictedSumOne JoinRival := by
  classical
  intro family hNonempty
  by_cases hSingleton : ∃ x, family = {x}
  · obtain ⟨x, rfl⟩ := hSingleton
    exact ⟨x, isLUB_singleton⟩
  · refine ⟨.top, ?_, ?_⟩
    · intro x _; exact Or.inr rfl
    · intro v hv
      by_cases ht : v = .top
      · subst v; exact le_rfl
      · exfalso
        apply hSingleton
        refine ⟨v, Set.ext fun x => ?_⟩
        constructor
        · intro hx
          exact Set.mem_singleton_iff.mpr ((hv hx).resolve_right ht)
        · intro hx
          have hxv : x = v := Set.mem_singleton_iff.mp hx
          obtain ⟨y, hy⟩ := hNonempty
          have hyv : y = v := (hv hy).resolve_right ht
          simpa [hxv, hyv] using hy

private theorem atom_all (P : AtomPair → Prop) :
    (∀ x, P x) ↔ P .a ∧ P .b := by
  constructor
  · intro h; exact ⟨h .a, h .b⟩
  · rintro ⟨ha, hb⟩ x; cases x <;> assumption

private theorem atom_ex (P : AtomPair → Prop) :
    (∃ x, P x) ↔ P .a ∨ P .b := by
  constructor
  · rintro ⟨x, hx⟩; cases x <;> tauto
  · rintro (h | h)
    · exact ⟨.a, h⟩
    · exact ⟨.b, h⟩

private theorem atom_le (x y : AtomPair) : x ≤ y ↔ atomPart x y := Iff.rfl

/-- A single pair of fixed carriers witnesses the two independently omitted
assumptions; both orders are explicit and have no null object. -/
theorem rivalChecks : RivalCertificate := by
  classical
  refine ⟨?_, allJoins, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [StrongSupplementation, Overlap, joinRival_all, joinRival_ex,
      joinRival_le, rivalPart]
  · simp [IsLUB, IsLeast, upperBounds, lowerBounds, joinRival_all, joinRival_le, rivalPart]
  · simp [Fusion, Overlap, joinRival_all, joinRival_ex, joinRival_le, rivalPart]
  · simp [Complementation, Overlap, joinRival_all, joinRival_ex, joinRival_le, rivalPart]
  · simp [joinRival_all, joinRival_le, rivalPart]
  · simp [Complementation, Overlap, atom_all, atom_ex, atom_le, atomPart]
  · simp [IsLUB, IsLeast, upperBounds, lowerBounds, atom_le, atomPart]
  · simp [Fusion, Overlap, atom_ex, atom_le, atomPart]
  · simp [atom_all, atom_le, atomPart]

end TruthCore.Results.Mereology.SumOneComplementation
