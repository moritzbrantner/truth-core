module

public import TruthCore.Mereology.AtomlessFusionProfile
public import TruthCore.Results.Mereology.SumOneComplementation.Solution
public import TruthCore.Results.Mereology.UniversalFusionBoundary.Solution

@[expose] public section

namespace TruthCore.Results.Mereology.AtomlessFusionProfile
open TruthCore.Mereology.UniversalFusionBoundary
open TruthCore.Mereology.SumOneComplementation
open TruthCore.Mereology.AtomlessFusionProfile

private theorem positive_overlap {A : Type} [BooleanAlgebra A]
    (x y : Positive A) : Overlap x y ↔ x.val ⊓ y.val ≠ ⊥ := by
  constructor
  · rintro ⟨p, hpx, hpy⟩ hz
    exact p.property (le_bot_iff.mp ((le_inf hpx hpy).trans_eq hz))
  · intro h
    exact ⟨⟨x.val ⊓ y.val, h⟩, inf_le_left, inf_le_right⟩

private theorem positive_complementation (A : Type) [BooleanAlgebra A] :
    Complementation (Positive A) := by
  classical
  intro x y hyx
  have hn : y.val \ x.val ≠ ⊥ := fun h => hyx (sdiff_eq_bot_iff.mp h)
  refine ⟨⟨y.val \ x.val, hn⟩, ?_⟩
  intro w
  constructor
  · intro h
    have hw := le_sdiff.mp h
    refine ⟨hw.1, ?_⟩
    intro ho
    exact ((positive_overlap w x).mp ho) (disjoint_iff.mp hw.2)
  · rintro ⟨hwy, hno⟩
    apply le_sdiff.mpr
    refine ⟨hwy, disjoint_iff.mpr ?_⟩
    by_contra h
    exact hno ((positive_overlap w x).mpr h)

private theorem positive_sumOne (A : Type) [CompleteBooleanAlgebra A] :
    UnrestrictedSumOne (Positive A) := by
  intro family hf
  let s : A := sSup (Subtype.val '' family)
  have hn : s ≠ ⊥ := by
    obtain ⟨x, hx⟩ := hf
    have hxs : x.val ≤ s := le_sSup ⟨x, hx, rfl⟩
    intro hs
    exact x.property (le_bot_iff.mp (hxs.trans_eq hs))
  refine ⟨⟨s, hn⟩, ?_, ?_⟩
  · intro x hx
    exact le_sSup ⟨x, hx, rfl⟩
  · intro z hz
    apply sSup_le
    rintro _ ⟨x, hx, rfl⟩
    exact hz hx

theorem positiveProfile (A : Type) [CompleteBooleanAlgebra A] :
    PositiveProfile A := by
  have hc := positive_complementation A
  have hs := positive_sumOne A
  exact ⟨hc, hs,
    TruthCore.Results.Mereology.SumOneComplementation.unrestrictedTransfer
      (Positive A) hc hs⟩

private def interval (a b : ℝ) : TopologicalSpace.Opens ℝ :=
  ⟨Set.Ioo a b, isOpen_Ioo⟩

private theorem interval_regular {a b : ℝ} (hab : a < b) :
    Heyting.IsRegular (interval a b) := by
  apply SetLike.coe_injective
  rw [TopologicalSpace.Opens.coe_compl_eq_interior_compl,
    TopologicalSpace.Opens.coe_compl_eq_interior_compl]
  change interior (interior (Set.Ioo a b)ᶜ)ᶜ = Set.Ioo a b
  rw [← closure_eq_compl_interior_compl, closure_Ioo hab.ne, interior_Icc]

private theorem region_composite (U : Region) : Composite U := by
  classical
  let O : TopologicalSpace.Opens ℝ := U.val
  have hnonempty : (O : Set ℝ).Nonempty := by
    by_contra h
    have ho : O = ⊥ := SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.mp h)
    exact U.property (Heyting.Regular.coe_injective ho)
  obtain ⟨a, b, hab, hsub⟩ := O.isOpen.exists_Ioo_subset hnonempty
  obtain ⟨x, hax, hxb⟩ := exists_between hab
  let V : RegionAlgebra := ⟨interval a x, interval_regular hax⟩
  have hv : V ≠ ⊥ := by
    intro h
    obtain ⟨y, hay, hyx⟩ := exists_between hax
    have hmem : y ∈ (V : TopologicalSpace.Opens ℝ) := ⟨hay, hyx⟩
    have ho : (V : TopologicalSpace.Opens ℝ) = ⊥ :=
      congrArg (fun r : RegionAlgebra => (r : TopologicalSpace.Opens ℝ)) h
    rw [ho] at hmem
    exact hmem
  refine ⟨⟨V, hv⟩, ?_, ?_⟩
  · intro t ht
    exact hsub ⟨ht.1, ht.2.trans hxb⟩
  · intro h
    have hx : x ∈ O := hsub ⟨hax, hxb⟩
    have bad : x ∈ (V : TopologicalSpace.Opens ℝ) := h hx
    exact lt_irrefl x bad.2

theorem gunkModel : GunkCertificate := by
  have hn : (⊤ : RegionAlgebra) ≠ ⊥ := by
    intro h
    have hs : (Set.univ : Set ℝ) = ∅ :=
      congrArg (fun r : RegionAlgebra => ((r : TopologicalSpace.Opens ℝ) : Set ℝ)) h
    exact Set.univ_nonempty.ne_empty hs
  let : Nonempty Region := ⟨⟨⊤, hn⟩⟩
  let : NoMinOrder Region := ⟨region_composite⟩
  refine ⟨inferInstance, positiveProfile RegionAlgebra, region_composite, ?_, inferInstance⟩
  rintro ⟨n, hleast⟩
  obtain ⟨p, hp⟩ := region_composite n
  exact hp.not_ge (hleast p)

private def bodyIso : Positive (Set Bool) ≃o Body where
  toFun s := ⟨s.val, Set.nonempty_iff_ne_empty.mpr s.property⟩
  invFun s := ⟨s.val, Set.nonempty_iff_ne_empty.mp s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

private theorem body_complementation : Complementation Body := by
  have h := (positiveProfile (Set Bool)).1
  intro x y hyx
  obtain ⟨z, hz⟩ := h (bodyIso.symm x) (bodyIso.symm y) hyx
  refine ⟨bodyIso z, ?_⟩
  intro w
  have ho : Overlap (bodyIso.symm w) (bodyIso.symm x) ↔ Overlap w x := by
    constructor
    · rintro ⟨p, hpw, hpx⟩
      exact ⟨bodyIso p, hpw, hpx⟩
    · rintro ⟨p, hpw, hpx⟩
      exact ⟨bodyIso.symm p, hpw, hpx⟩
  exact (hz (bodyIso.symm w)).trans (and_congr Iff.rfl (not_congr ho))

private theorem body_sumOne : UnrestrictedSumOne Body := by
  have h := (positiveProfile (Set Bool)).2.1
  intro family hf
  have hn : (bodyIso ⁻¹' family).Nonempty := by
    obtain ⟨x, hx⟩ := hf
    exact ⟨bodyIso.symm x, hx⟩
  obtain ⟨u, hu⟩ := h (bodyIso ⁻¹' family) hn
  refine ⟨bodyIso u, ?_, ?_⟩
  · intro x hx
    exact hu.1 (show bodyIso.symm x ∈ bodyIso ⁻¹' family from hx)
  · intro z hz
    exact hu.2 (show bodyIso.symm z ∈ upperBounds (bodyIso ⁻¹' family) from
      fun _ hx => hz hx)

theorem atomicModel : AtomicCertificate := by
  refine ⟨⟨atom false⟩, ⟨body_complementation, body_sumOne,
    TruthCore.Results.Mereology.UniversalFusionBoundary.checks.2.2.1⟩, ?_, ?_,
    inferInstance⟩
  · intro x
    obtain ⟨b, hb⟩ := x.property
    refine ⟨atom b, ?_, ?_⟩
    · intro c hc
      exact (Set.mem_singleton_iff.mp hc) ▸ hb
    · intro p hp
      obtain ⟨c, hc⟩ := p.property
      have hcb : c = b := hp hc
      have hbp : b ∈ p.val := hcb ▸ hc
      intro d hd
      exact (Set.mem_singleton_iff.mp hd) ▸ hbp
  · rintro ⟨n, hn⟩
    obtain ⟨b, hb⟩ := n.property
    have hbf : b = false := hn (atom false) hb
    have hbt : b = true := hn (atom true) hb
    exact Bool.noConfusion (hbf.symm.trans hbt)

theorem finiteBoundary : FiniteBoundary := by
  intro B _ _ _ hall
  let : NoMinOrder B := ⟨hall⟩
  have : Infinite B := inferInstance
  exact not_finite B

end TruthCore.Results.Mereology.AtomlessFusionProfile
