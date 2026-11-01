import TruthCore.Causality.ContingentAtomicity
import TruthCore.Logic.ExcludedMiddle
import TruthCore.Results.Causality.ScopedActualCausality.Solution

namespace TruthCore.Results.Causality.ContingentAtomicity
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Causality.AtomisticCausalSource
open TruthCore.Causality.ScopedActualCausality
open TruthCore.Causality.ContingentAtomicity
open TruthCore.Logic (ExcludedMiddle)

theorem allToContingent {W B : Type} (m : Ontic W B) (w : W)
    [PartialOrder (Actual m w)] (hAtomic : AtomicParts (Actual m w)) :
    ContingentAtomicParts m w := by
  exact fun x _ => hAtomic x

theorem necessaryBeing {W B : Type} (m : Ontic W B) (w : W)
    [PartialOrder (Actual m w)]
    (hPop : ObjectPopulation (Actual m w)) (hAtomic : ContingentAtomicParts m w)
    (hCover : ConditionalCausedSimpleCover (actualGraph m w))
    (hNoOverlap : CauseEffectNonoverlap (actualGraph m w))
    (hEM : ExcludedMiddle) (hCoverage : SelectedActualCausalCoverage m w) :
    NecessaryBeing m w := by
  rcases hEM (NecessaryBeing m w) with hNE | hNone
  · exact hNE
  · have allContingent : ∀ x : Actual m w, ContingentAt m w x.val := by
      intro x
      rcases hEM (∃ v, m.frame.access w v ∧ ¬ m.ExistsAt v x.val) with ha | hn
      · exact ⟨x.property, ha⟩
      · have hNecessary : NecessaryAt m w x.val := by
          intro v hv
          rcases hEM (m.ExistsAt v x.val) with he | he
          · exact he
          · exact (hn ⟨v, hv, he⟩).elim
        exact (hNone ⟨x.val, x.property, hNecessary⟩).elim
    have hAll : AtomicParts (Actual m w) := fun x => hAtomic x (allContingent x)
    exact TruthCore.Results.Causality.ScopedActualCausality.necessaryBeing
      m w hPop hAll hCover hNoOverlap hEM hCoverage

private theorem partOfPoint {m : Ontic Bool Controls.Carrier}
    (x : Actual m false) (h : x.val ≤ Controls.point) : x.val = Controls.point := by
  rcases x with ⟨x, hx⟩
  cases x with
  | inl u => cases u; rfl
  | inr n => exact (Sum.not_inr_le_inl h).elim

private theorem simpleIffPoint (m : Ontic Bool Controls.Carrier)
    (hAll : ∀ x, m.ExistsAt false x) (x : Actual m false) :
    IsMin x ↔ x.val = Controls.point := by
  constructor
  · intro h
    rcases x with ⟨x, hx⟩
    cases x with
    | inl u => cases u; rfl
    | inr n =>
      let p : Actual m false := ⟨Controls.gunk (OrderDual.ofDual n + 1), hAll _⟩
      have hp : p ≤ ⟨Sum.inr n, hx⟩ := by
        exact Sum.inr_le_inr_iff.mpr (Nat.le_succ (OrderDual.ofDual n))
      have bad := h hp
      have hb := Sum.inr_le_inr_iff.mp bad
      exact (Nat.not_succ_le_self (OrderDual.ofDual n) hb).elim
  · intro he y hy
    have hyPoint : y.val = Controls.point := partOfPoint y (he ▸ hy)
    have hyx : y = x := Subtype.ext (hyPoint.trans he.symm)
    subst y
    exact le_refl x

private theorem atomicFails (m : Ontic Bool Controls.Carrier)
    (hAll : ∀ x, m.ExistsAt false x) : ¬ AtomicParts (Actual m false) := by
  intro h
  obtain ⟨a, ha, hs⟩ := h ⟨Controls.gunk 0, hAll _⟩
  have he := (simpleIffPoint m hAll a).mp hs
  have hab : a.val ≤ Controls.gunk 0 := ha
  rw [he] at hab
  exact Sum.not_inl_le_inr hab

open Controls in
theorem control : Control := by
  have sAll : ∀ x, strict.ExistsAt false x := fun _ => Or.inl rfl
  have rAll : ∀ x, reverse.ExistsAt false x := fun _ => Or.inl rfl
  have sPointCont : ContingentAt strict false point := by
    refine ⟨sAll _, true, True.intro, ?_⟩
    rintro (h | h)
    · cases h
    · exact h
  have rGunkCont : ∀ n, ContingentAt reverse false (gunk n) := by
    intro n
    refine ⟨rAll _, true, True.intro, ?_⟩
    rintro (h | h)
    · cases h
    · exact h
  have sContPoint : ∀ x, ContingentAt strict false x → x = point := by
    intro x hx
    cases x with
    | inl u => cases u; rfl
    | inr n =>
      obtain ⟨v, _, ha⟩ := hx.2
      exact (ha (Or.inr True.intro)).elim
  have rContNotPoint : ∀ x, ContingentAt reverse false x → x ≠ point := by
    intro x hx he
    subst x
    obtain ⟨v, _, ha⟩ := hx.2
    exact ha (Or.inr True.intro)
  have sSimple := simpleIffPoint strict sAll
  have rSimple := simpleIffPoint reverse rAll
  have sFamily : ∀ a : Actual strict false,
      CausedSimples (actualGraph strict false) a ↔ a.val = point := by
    intro a
    constructor
    · exact fun h => sSimple a |>.mp h.1
    · intro he
      exact ⟨(sSimple a).mpr he, strictNode (gunk 0), rfl, rfl, he⟩
  have rEmpty : ∀ a : Actual reverse false,
      ¬ CausedSimples (actualGraph reverse false) a := by
    rintro a ⟨hs, c, hc⟩
    exact hc.2.2 ((rSimple a).mp hs)
  have sCover : ConditionalCausedSimpleCover (actualGraph strict false) := by
    intro _
    refine ⟨strictNode point, ?_⟩
    intro a ha
    have he : a = strictNode point := Subtype.ext ((sFamily a).mp ha)
    exact he ▸ le_refl _
  have rCover : ConditionalCausedSimpleCover (actualGraph reverse false) := by
    rintro ⟨a, ha⟩
    exact (rEmpty a ha).elim
  have sNo : CauseEffectNonoverlap (actualGraph strict false) := by
    intro c e hc ⟨p, hpc, hpe⟩
    have hp : p.val = point := partOfPoint p (hc.2.2 ▸ hpe)
    have hpg : p.val ≤ gunk 0 := hc.2.1 ▸ hpc
    rw [hp] at hpg
    exact Sum.not_inl_le_inr hpg
  have rNo : CauseEffectNonoverlap (actualGraph reverse false) := by
    intro c e hc ⟨p, hpc, hpe⟩
    have hp : p.val = point := partOfPoint p (hc.2.1 ▸ hpc)
    have hpe' : point ≤ e.val := hp ▸ hpe
    cases he : e.val with
    | inl u => cases u; exact hc.2.2 he
    | inr n => rw [he] at hpe'; exact Sum.not_inl_le_inr hpe'
  have sCoverage : SelectedActualCausalCoverage strict false := by
    intro x hx
    exact ⟨gunk 0, sAll _, rfl, rfl, sContPoint x hx⟩
  have rCoverage : SelectedActualCausalCoverage reverse false := by
    intro x hx
    exact ⟨point, rAll _, rfl, rfl, rContNotPoint x hx⟩
  have sAtomic : ContingentAtomicParts strict false := by
    intro x hx
    have he := sContPoint x.val hx
    exact ⟨x, le_refl x, (sSimple x).mpr he⟩
  have rNotAtomic : ¬ ContingentAtomicParts reverse false := by
    intro h
    obtain ⟨a, ha, hs⟩ := h (reverseNode (gunk 0)) (rGunkCont 0)
    have he := (rSimple a).mp hs
    have hab : a.val ≤ gunk 0 := ha
    rw [he] at hab
    exact Sum.not_inl_le_inr hab
  exact ⟨⟨strictNode point⟩, sCover, sNo, sCoverage, sAtomic,
    atomicFails strict sAll, sPointCont,
    ⟨gunk 0, sAll _, fun _ _ => Or.inr True.intro⟩, sFamily,
    ⟨reverseNode point⟩, rCover, rNo, rCoverage, rNotAtomic, rGunkCont 0,
    ⟨point, rAll _, fun _ _ => Or.inr True.intro⟩, rEmpty⟩

end TruthCore.Results.Causality.ContingentAtomicity
