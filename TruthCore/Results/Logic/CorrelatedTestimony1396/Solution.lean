module
public import TruthCore.Logic.CorrelatedTestimony1396
public import TruthCore.Results.Logic.ContrastiveWorldview.Solution
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
@[expose] public section
namespace TruthCore.Results.Logic.CorrelatedTestimony1396
open TruthCore.Logic.CorrelatedTestimony1396
open TruthCore.Logic.ContrastiveWorldview

private theorem cross (r : Reports) (e f : Event) :
    posterior r e < posterior r f ↔
    r.h.likelihood e * r.v.likelihood f < r.h.likelihood f * r.v.likelihood e := by
  have hp := r.prior_pos
  have hq := sub_pos.mpr r.prior_lt
  have he := (TruthCore.Results.Logic.ContrastiveWorldview.updateConstraints (comparison r e)).1
  have hf := (TruthCore.Results.Logic.ContrastiveWorldview.updateConstraints (comparison r f)).1
  unfold posterior posteriorW
  rw [div_lt_div_iff₀ he hf]
  change r.prior * r.h.likelihood e *
    (r.prior * r.h.likelihood f + (1-r.prior)*r.v.likelihood f) <
    r.prior * r.h.likelihood f *
    (r.prior * r.h.likelihood e + (1-r.prior)*r.v.likelihood e) ↔ _
  have key : ∀ x y z w : ℚ,
      r.prior*x*(r.prior*z+(1-r.prior)*w) -
      r.prior*z*(r.prior*x+(1-r.prior)*y) =
      (r.prior*(1-r.prior))*(x*w-z*y) := by intros; ring
  rw [← sub_neg, key, ← mul_zero (r.prior*(1-r.prior)),
    mul_lt_mul_iff_right₀ (mul_pos hp hq), sub_neg]

private theorem one (r : Reports) :
    posterior r .b < posterior r .both ↔ conditionalV r < conditionalH r := by
  rw [cross]
  unfold conditionalV conditionalH
  have vh : 0 < r.v.b := (r.v.bounds .b).1
  have hh : 0 < r.h.b := (r.h.bounds .b).1
  rw [div_lt_div_iff₀ vh hh]
  dsimp [Row.likelihood]
  constructor <;> intro h <;> nlinarith

private theorem pooled (r : Reports) :
    conditionalV r < conditionalH r ↔ pooledConditional r < conditionalH r := by
  have hb : 0 < r.h.b := (r.h.bounds .b).1
  have vb : 0 < r.v.b := (r.v.bounds .b).1
  have hp := r.prior_pos
  have hq := sub_pos.mpr r.prior_lt
  have hz : 0 < r.prior*r.h.b+(1-r.prior)*r.v.b :=
    add_pos (mul_pos hp hb) (mul_pos hq vb)
  unfold conditionalV conditionalH pooledConditional
  rw [div_lt_div_iff₀ vb hb, div_lt_div_iff₀ hz hb]
  have key : (r.prior*r.h.both+(1-r.prior)*r.v.both)*r.h.b -
    r.h.both*(r.prior*r.h.b+(1-r.prior)*r.v.b) =
    (1-r.prior)*(r.v.both*r.h.b-r.h.both*r.v.b) := by ring
  conv_lhs => rw [← sub_neg]
  conv_rhs => rw [← sub_neg, key, ← mul_zero (1-r.prior), mul_lt_mul_iff_right₀ hq]

/-- Both conditions are required; positivity prevents undefined conditioning. -/
theorem criterion : Criterion := by
  intro r
  refine ⟨one r, pooled r, ?_, ?_⟩
  · have swapped := one r.swap
    change (posterior r .a < posterior r .both ↔
      conditionalV r.swap < conditionalH r.swap) at swapped
    exact ⟨fun h => ⟨(one r).mp h.2, swapped.mp h.1⟩,
      fun h => ⟨swapped.mpr h.2, (one r).mpr h.1⟩⟩
  · have vb : r.v.b ≠ 0 := ne_of_gt (r.v.bounds .b).1
    have hb : r.h.b ≠ 0 := ne_of_gt (r.h.bounds .b).1
    have vj := ne_of_gt r.v.pos.1
    dsimp [factor, conditionalH, conditionalV, Row.likelihood]
    field_simp

/-- Independence is an extra pair of hypotheses, not a default process fact. -/
theorem independenceSuffices : IndependenceSuffices := by
  intro r hi ha hb
  have ga := (TruthCore.Results.Logic.ContrastiveWorldview.updateConstraints (comparison r .a)).2.2.2.2.1.mp ha
  have gb := (TruthCore.Results.Logic.ContrastiveWorldview.updateConstraints (comparison r .b)).2.2.2.2.1.mp hb
  change r.v.a < r.h.a at ga
  change r.v.b < r.h.b at gb
  apply (criterion r).2.2.1.mpr
  rcases hi with ⟨hh, hv⟩
  have ph : r.h.b ≠ 0 := ne_of_gt (r.h.bounds .b).1
  have pv : r.v.b ≠ 0 := ne_of_gt (r.v.bounds .b).1
  have ah : r.h.a ≠ 0 := ne_of_gt (r.h.bounds .a).1
  have av : r.v.a ≠ 0 := ne_of_gt (r.v.bounds .a).1
  constructor
  · dsimp [conditionalH, conditionalV]
    rw [hh, hv, mul_div_cancel_right₀ _ ph, mul_div_cancel_right₀ _ pv]
    exact ga
  · change r.v.both / r.v.a < r.h.both / r.h.a
    rw [hh, hv, mul_div_cancel_left₀ _ ah, mul_div_cancel_left₀ _ av]
    exact gb

theorem controls : Controls := by
  norm_num [Controls, posterior, comparison, posteriorW, normalizer, factor,
    Row.likelihood, Row.a, Row.b, reversal, oneSided, unconditional, dependentGrowth,
    pooledConditional, conditionalH, conditionalV, Reports.swap, Row.swap,
    UnconditionalIndependent, ConditionalIndependent]
end TruthCore.Results.Logic.CorrelatedTestimony1396
