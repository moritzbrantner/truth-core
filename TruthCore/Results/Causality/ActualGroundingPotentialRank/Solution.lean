module

public import TruthCore.Causality.ActualGroundingPotentialRank
public import TruthCore.Results.Causality.Round3CogitoBase.Solution
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace TruthCore.Results.Causality.ActualGroundingPotentialRank
open TruthCore.Causality.ActualGroundingPotentialRank
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualGroundingWF)
open TruthCore.Causality.Round3CogitoBase (ActualGroundingFiniteRank)

/-- Explicit floor construction; no Nat rank or foundation hypothesis occurs
in the three inputs. The bound normalizes actual nodes to nonnegative values,
and the uniform gap makes the natural floor strictly increase toward effects. -/
theorem finiteRankFromPotential {W B : Type} (m : Profile W B) (w : W)
    (S : B → ℝ) (L ε : ℝ)
    (hLower : PotentialLowerBound m w S L) (hPositive : PositiveGap ε)
    (hGap : UniformGroundGap m w S ε) : ActualGroundingFiniteRank m w := by
  refine ⟨fun x => ⌊(S x - L) / ε⌋₊, ?_⟩
  intro x y hx hy hEdge
  have hp : 0 < ε := hPositive
  have hnonneg : 0 ≤ (S y - L) / ε := div_nonneg (sub_nonneg.mpr (hLower y hy)) hp.le
  have hstep : (S y - L) / ε + 1 ≤ (S x - L) / ε := by
    apply (le_div_iff₀ hp).2
    have h := hGap x y hx ⟨hy.1, hy.2, hEdge⟩
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hp), one_mul]
    linarith
  have hfloor : (⌊(S y - L) / ε⌋₊ + 1 : ℕ) ≤ ⌊(S x - L) / ε⌋₊ := by
    apply Nat.le_floor
    push_cast
    have hf := Nat.floor_le hnonneg
    linarith
  exact hfloor

/-- Assembly reuses the existing root-route interface; the mathematical work
is finiteRankFromPotential, not this composition. -/
theorem wellFoundedFromPotential {W B : Type} (m : Profile W B) (w : W)
    (S : B → ℝ) (L ε : ℝ)
    (hLower : PotentialLowerBound m w S L) (hPositive : PositiveGap ε)
    (hGap : UniformGroundGap m w S ε) : ActualGroundingWF m w :=
  TruthCore.Results.Causality.Round3CogitoBase.actualGroundingWFFromFiniteRank m w
    (finiteRankFromPotential m w S L ε hLower hPositive hGap)

/-- An infinite reverse-successor graph retains each pair of assumptions but
fails the third; an infinite ascending graph jointly witnesses the full bundle. -/
theorem controls : Control.Certificate := by
  have hNotWF : ¬ ActualGroundingWF Control.descending () := by
    intro h
    have noAcc : ∀ x : {n // ActualConcrete Control.descending () n},
        Acc (fun a b : {n // ActualConcrete Control.descending () n} =>
          Control.descending.grounds () a.1 b.1) x → False := by
      intro x hx
      induction hx with
      | intro x _ ih => exact ih ⟨x.1 + 1, trivial, trivial⟩ rfl
    exact noAcc ⟨0, trivial, trivial⟩ (h.apply _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun _ _ => le_refl _, (by intro x y hx hy; norm_num), by norm_num [PositiveGap]⟩
  · refine ⟨by norm_num [PositiveGap], ?_, ?_⟩
    · intro x y _ hy
      have he : y = x + 1 := hy.2.2
      subst y
      simp only [Nat.cast_add, Nat.cast_one]
      linarith
    · rintro ⟨L, hL⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (-L)
      have hl := hL n ⟨trivial, trivial⟩
      linarith
  · refine ⟨by norm_num [PositiveGap], fun _ _ => le_refl _, ?_⟩
    intro h
    have hf := h 0 1 ⟨trivial, trivial⟩ ⟨trivial, trivial, rfl⟩
    norm_num at hf
  · exact ⟨fun h => hNotWF
      (TruthCore.Results.Causality.Round3CogitoBase.actualGroundingWFFromFiniteRank _ _ h), hNotWF⟩
  · have hl : PotentialLowerBound Control.descending () Control.varying 0 := by
      intro n _
      unfold Control.varying
      positivity
    refine ⟨hl, ?_, ?_⟩
    · intro x y _ hy
      have he : y = x + 1 := hy.2.2
      subst y
      unfold Control.varying
      apply one_div_lt_one_div_of_lt (by positivity)
      push_cast
      linarith
    · intro ε hp hg
      exact hNotWF (wellFoundedFromPotential Control.descending () Control.varying 0 ε hl hp hg)
  · have hl : PotentialLowerBound Control.ascending () (fun n => (n : ℝ)) 0 :=
      fun n _ => Nat.cast_nonneg n
    have hg : UniformGroundGap Control.ascending () (fun n => (n : ℝ)) 1 := by
      intro x y _ hy
      have he : x = y + 1 := hy.2.2
      subst x
      simp
    have hp : PositiveGap 1 := by norm_num [PositiveGap]
    exact ⟨hp, hl, hg, ⟨trivial, trivial, rfl⟩,
      finiteRankFromPotential Control.ascending () _ 0 1 hl hp hg⟩

end TruthCore.Results.Causality.ActualGroundingPotentialRank
