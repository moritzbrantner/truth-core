import Mathlib.Order.WellFounded
import TruthCore.Modern.Fine.PureLogicOfGround

namespace TruthCore.Results.Modern.Fine.InfiniteDescent
open TruthCore.Modern.Fine.PureLogicOfGround
open Sequent

/-- The level reading of a sequent under a rank assignment: weak ground never
moves up in rank and strict ground always moves strictly down. It follows
Fine's informal gloss (p. 3) that strict grounds move "down in the explanatory
hierarchy" while weak grounds may move "sideways"; it is a stipulated
interpretation for consistency proofs, not Fine's fact semantics (§3). -/
def HoldsAtRank {Atom β : Type} [Preorder β] (rank : Atom → β) :
    Sequent Atom → Prop
  | weakFull Δ C => ∀ A ∈ Δ, rank A ≤ rank C
  | weakPartial A C => rank A ≤ rank C
  | strictFull Δ C => ∀ A ∈ Δ, rank A < rank C
  | strictPartial A C => rank A < rank C

/-- Every PLG rule preserves the level reading, for every rank assignment into
a preorder: whatever is derivable from sequents that hold at a rank holds at
that rank. -/
theorem holdsAtRank_of_derivable {Atom β : Type} [Preorder β] (rank : Atom → β)
    {S : Set (Sequent Atom)} (hS : ∀ s ∈ S, HoldsAtRank rank s) {s : Sequent Atom}
    (h : Derivable S s) : HoldsAtRank rank s := by
  induction h with
  | assumption hs => exact hS _ hs
  | subsumptionStrictFull _ ih => exact fun A hA => le_of_lt (ih A hA)
  | subsumptionStrictPartial _ ih => exact le_of_lt ih
  | subsumptionStrictFullPartial _ hA ih => exact ih _ hA
  | subsumptionWeakFullPartial _ hA ih => exact ih _ hA
  | cut A Δ _ _ ihPrem ihCut =>
      intro B hB
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hB
      exact le_trans (ihPrem i B hi) (ihCut (A i) ⟨i, rfl⟩)
  | transWeakWeak _ _ ih₁ ih₂ => exact le_trans ih₁ ih₂
  | transWeakStrict _ _ ih₁ ih₂ => exact lt_of_le_of_lt ih₁ ih₂
  | transStrictWeak _ _ ih₁ ih₂ => exact lt_of_lt_of_le ih₁ ih₂
  | identity A =>
      intro B hB
      rw [Set.mem_singleton_iff.mp hB]
  | nonCircularity _ _ ih => exact absurd ih (lt_irrefl _)
  | reverseSubsumption _ _ _ ihStrict => exact fun A hA => ihStrict A hA

/-- The assumed sequents: `n + 1 ≺ n` for every natural number `n`. -/
def descendingSequents : Set (Sequent Nat) :=
  {s | ∃ n, s = strictPartial (n + 1) n}

/-- PLG's Non-Circularity does not exclude an infinite descending chain of
derivable strict ground. Countermodel: assume `n + 1 ≺ n` for every `n`. With
rank `n ↦ -n` every assumption holds at its rank and `0 ≼ 1` does not, so the
weak partial ground `0 ≼ 1` is not derivable and the set is consistent; the
chain `0, 1, 2, …` descends forever. -/
theorem nonCircularityAllowsInfiniteDescent : NonCircularityAllowsInfiniteDescent := by
  have hStep : ∀ n, StrictlyGrounds descendingSequents (n + 1) n :=
    fun n => Derivable.assumption ⟨n, rfl⟩
  refine ⟨descendingSequents, ⟨weakPartial 0 1, fun h => ?_⟩, hStep, fun hWF => ?_⟩
  · have hRank : ∀ s ∈ descendingSequents,
        HoldsAtRank (fun n : Nat => -(n : Int)) s := by
      rintro s ⟨n, rfl⟩
      show -((n + 1 : Nat) : Int) < -(n : Int)
      omega
    have h01 := holdsAtRank_of_derivable (fun n : Nat => -(n : Int)) hRank h
    change -((0 : Nat) : Int) ≤ -((1 : Nat) : Int) at h01
    omega
  · have hAcc : ∀ n, ¬ Acc (StrictlyGrounds descendingSequents) n := by
      intro n hn
      induction hn with
      | intro m _ ih => exact ih (m + 1) (hStep m)
    exact hAcc 0 (hWF.apply 0)

end TruthCore.Results.Modern.Fine.InfiniteDescent
