module

public import TruthCore.Mereology.SupplementationFusion
public import TruthCore.Results.Mereology.UniversalFusionBoundary.Solution
public import Mathlib.Tactic.Tauto

/-! Conditional consequences of explicit mereological axioms, and a finite rival.
The binary bridge uses no unrestricted-family formation or atomism. -/

@[expose] public section

namespace TruthCore.Results.Mereology.SupplementationFusion
open TruthCore.Mereology.UniversalFusionBoundary
open TruthCore.Mereology.NecessaryPartFusionDecomposition
open TruthCore.Mereology.SupplementationFusion

private theorem overlap_mono {B : Type} [PartialOrder B] {p x y : B}
    (h : Overlap p x) (hxy : x ≤ y) : Overlap p y := by
  obtain ⟨q, hqp, hqx⟩ := h
  exact ⟨q, hqp, le_trans hqx hxy⟩

/-- Weak supplementation collapses a singleton Sum2 fusion to its member.
A strictly larger whole would have a part disjoint from that member. -/
private theorem singleton_eq {B : Type} [PartialOrder B]
    (hWeak : WeakSupplementation B) (x u : B)
    (hxu : x ≤ u) (hAll : ∀ p, p ≤ u → Overlap p x) : u = x := by
  by_contra hne
  obtain ⟨z, hzu, hDisjoint⟩ := hWeak x u (lt_of_le_of_ne hxu (Ne.symm hne))
  exact hDisjoint (hAll z hzu)

/-- A binary Sum2 upper bound and its no-extra-parts clause turn failure of
separation into containment. Only a two-member family is used. -/
theorem strongFromWeakBinary (B : Type) [PartialOrder B]
    (hWeak : WeakSupplementation B) (hBinary : BinaryFusion B) :
    StrongSupplementation B := by
  classical
  intro x y hNotPart
  by_contra hNoRemainder
  have hAll : ∀ p, p ≤ x → Overlap p y := by
    intro p hpx
    by_contra hDisjoint
    exact hNoRemainder ⟨p, hpx, hDisjoint⟩
  obtain ⟨u, hFusion⟩ := hBinary x y
  have hxu : x ≤ u := hFusion.1 x (by simp)
  have hyu : y ≤ u := hFusion.1 y (by simp)
  have hParts : ∀ p, p ≤ u → Overlap p y := by
    intro p hpu
    obtain ⟨z, hz, q, hqp, hqz⟩ := hFusion.2 p hpu
    rcases Set.mem_insert_iff.mp hz with hzx | hzy
    · subst z
      obtain ⟨r, hrq, hry⟩ := hAll q hqz
      exact ⟨r, le_trans hrq hqp, hry⟩
    · have hEq : z = y := Set.mem_singleton_iff.mp hzy
      exact ⟨q, hqp, hEq ▸ hqz⟩
  have hueq : u = y := singleton_eq hWeak y u hyu hParts
  exact hNotPart (hueq ▸ hxu)

/-- Exact existing overlap-extensional interface; no identity or modal notion
is substituted for it. Classical logic extracts a separating witness. -/
theorem separationCharacterization (B : Type) [PartialOrder B] :
    SeparationCharacterization B := by
  classical
  constructor
  · intro hStrong x y
    constructor
    · intro hxy z hzx
      exact overlap_mono hzx hxy
    · intro hAll
      by_contra hNotPart
      obtain ⟨z, hzx, hDisjoint⟩ := hStrong x y hNotPart
      exact hDisjoint (hAll z ⟨z, le_rfl, hzx⟩)
  · intro hExt x y hNotPart
    by_contra hNoRemainder
    apply hNotPart
    apply (hExt x y).mpr
    intro z hOverlap
    obtain ⟨p, hpz, hpx⟩ := hOverlap
    have hpy : Overlap p y := by
      by_contra hDisjoint
      exact hNoRemainder ⟨p, hpx, hDisjoint⟩
    obtain ⟨q, hqp, hqy⟩ := hpy
    exact ⟨q, le_trans hqp hpz, hqy⟩

/-- Sum2 implies Sum3 without any supplementation assumption. -/
theorem overlapOfFusion {B : Type} [PartialOrder B] (family : Set B) (u : B)
    (hFusion : Fusion family u) : OverlapFusion family u := by
  intro p
  constructor
  · rintro ⟨q, hqp, hqu⟩
    obtain ⟨x, hx, r, hrq, hrx⟩ := hFusion.2 q hqu
    exact ⟨x, hx, r, le_trans hrq hqp, hrx⟩
  · rintro ⟨x, hx, hpx⟩
    exact overlap_mono hpx (hFusion.1 x hx)

/-- Strong supplementation supplies precisely the missing member-containment
clause of Sum3. Both empty predicates are impossible by reflexive overlap. -/
theorem fusionComparison (B : Type) [PartialOrder B]
    (hStrong : StrongSupplementation B) : FusionComparison B := by
  intro family u
  constructor
  · exact overlapOfFusion family u
  · intro hOverlap
    constructor
    · intro x hx
      apply ((separationCharacterization B).mp hStrong x u).mpr
      intro p hpx
      exact (hOverlap p).mpr ⟨x, hx, hpx⟩
    · intro p hpu
      exact (hOverlap p).mp ⟨p, le_rfl, hpu⟩

/-- Reuse the earlier greatest-whole theorem only after converting nonempty
Sum3 formation to its actual Sum2 hypothesis. Inhabitation remains explicit. -/
theorem overlapGreatest (B : Type) [PartialOrder B] [Nonempty B]
    (hStrong : StrongSupplementation B) (hOverlap : UnrestrictedOverlap B) :
    GreatestEntity B := by
  have hSum2 : Unrestricted (B := B) := by
    intro family hNonempty
    obtain ⟨u, hu⟩ := hOverlap family hNonempty
    exact ⟨u, ((fusionComparison B hStrong) family u).mpr hu⟩
  exact UniversalFusionBoundary.checks.1 B hSum2

private theorem rival_forall (P : Rival → Prop) :
    (∀ x, P x) ↔ P .a ∧ P .b ∧ P .u ∧ P .v := by
  constructor
  · intro h; exact ⟨h .a, h .b, h .u, h .v⟩
  · rintro ⟨ha, hb, hu, hv⟩ x; cases x <;> assumption

private theorem rival_exists (P : Rival → Prop) :
    (∃ x, P x) ↔ P .a ∨ P .b ∨ P .u ∨ P .v := by
  constructor
  · rintro ⟨x, hx⟩; cases x <;> tauto
  · rintro (h | h | h | h)
    · exact ⟨.a, h⟩
    · exact ⟨.b, h⟩
    · exact ⟨.u, h⟩
    · exact ⟨.v, h⟩

private theorem rival_le (x y : Rival) : x ≤ y ↔ rivalPart x y := Iff.rfl

/-- Every nonempty family has a witness chosen from its atomic support. The
proof quantifies over all Sets, not a list of screened test families. -/
private theorem rivalOverlap : UnrestrictedOverlap Rival := by
  classical
  intro family hNonempty
  by_cases hA : ∃ x ∈ family, x = Rival.a ∨ x = Rival.u ∨ x = Rival.v
  · by_cases hB : ∃ x ∈ family, x = Rival.b ∨ x = Rival.u ∨ x = Rival.v
    · refine ⟨Rival.u, ?_⟩
      simp_all [OverlapFusion, Overlap, rival_exists, rival_forall, rival_le, rivalPart]
    · refine ⟨Rival.a, ?_⟩
      simp_all [OverlapFusion, Overlap, rival_exists, rival_forall, rival_le, rivalPart]
  · refine ⟨Rival.b, ?_⟩
    simp_all [Set.Nonempty, OverlapFusion, Overlap, rival_exists, rival_forall, rival_le, rivalPart]

/-- One fixed four-object interpretation jointly satisfies the weaker package
and all advertised failures; neither actual coincidence nor GEM is claimed. -/
theorem rivalChecks : RivalCertificate := by
  classical
  have hNoUpper : ¬ (∃ t : Rival, Rival.u ≤ t ∧ Rival.v ≤ t) := by decide
  refine ⟨?_, rivalOverlap, ?_, ?_, ?_, ?_, by decide, ?_, hNoUpper, ?_, ?_, ?_, ?_, by decide⟩
  · simp [WeakSupplementation, Overlap, lt_iff_le_not_ge,
      rival_forall, rival_exists, rival_le, rivalPart]
  · simp [StrongSupplementation, Overlap, rival_forall, rival_exists, rival_le, rivalPart]
  · simp [OverlapExtensionalParthood, Overlap, rival_forall, rival_exists, rival_le, rivalPart]
  · simp [Fusion, Overlap, rival_exists, rival_le, rivalPart]
  · simp [Fusion, Overlap, rival_exists, rival_le, rivalPart]
  · simp [lt_iff_le_not_ge, rival_forall, rival_le, rivalPart]
  · intro h
    obtain ⟨t, ht⟩ := h ({Rival.u, Rival.v} : Set Rival) ⟨Rival.u, by simp⟩
    exact hNoUpper ⟨t, ht.1 Rival.u (by simp), ht.1 Rival.v (by simp)⟩
  · simp [GreatestEntity, rival_forall, rival_le, rivalPart]
  · simp [rival_forall, rival_le, rivalPart]
  · simp [OverlapFusion, Overlap, rival_forall, rival_exists, rival_le, rivalPart]

end TruthCore.Results.Mereology.SupplementationFusion
