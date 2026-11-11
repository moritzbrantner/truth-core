module
public import TruthCore.Logic.ContrastiveWorldview
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Analyst finite probability model, not empirical testimony calibration.
Four strictly positive cells partition reports within EACH hypothesis.
No historical stages 4–6 application or root-facing epistemic bridge. -/
@[expose] public section
namespace TruthCore.Logic.CorrelatedTestimony1396
open ContrastiveWorldview

structure Row where
  both : ℚ
  onlyA : ℚ
  onlyB : ℚ
  neither : ℚ
  pos : 0 < both ∧ 0 < onlyA ∧ 0 < onlyB ∧ 0 < neither
  total : both + onlyA + onlyB + neither = 1

def Row.a (r : Row) := r.both + r.onlyA
def Row.b (r : Row) := r.both + r.onlyB

def Row.swap (r : Row) : Row :=
  ⟨r.both, r.onlyB, r.onlyA, r.neither,
   ⟨r.pos.1, r.pos.2.2.1, r.pos.2.1, r.pos.2.2.2⟩, by linarith [r.total]⟩

structure Reports where
  prior : ℚ
  prior_pos : 0 < prior
  prior_lt : prior < 1
  h : Row
  v : Row

inductive Event | a | b | both

def Row.likelihood (r : Row) : Event → ℚ
  | .a => r.a
  | .b => r.b
  | .both => r.both

theorem Row.bounds (r : Row) (e : Event) :
    0 < r.likelihood e ∧ r.likelihood e ≤ 1 := by
  rcases r.pos with ⟨hj, ha, hb, hn⟩
  cases e <;> dsimp [likelihood, a, b] <;> constructor <;> linarith [r.total]

def comparison (r : Reports) (e : Event) : Comparison :=
  ⟨r.prior, r.h.likelihood e, r.v.likelihood e, r.prior_pos, r.prior_lt,
    (r.h.bounds e).1, (r.h.bounds e).2, (r.v.bounds e).1, (r.v.bounds e).2⟩
def posterior (r : Reports) (e : Event) := posteriorW (comparison r e)
def factor (r : Reports) (e : Event) := r.h.likelihood e / r.v.likelihood e

def Reports.swap (r : Reports) : Reports :=
  ⟨r.prior, r.prior_pos, r.prior_lt, r.h.swap, r.v.swap⟩

/-- Conditional probabilities A|B under each hypothesis. -/
def conditionalH (r : Reports) := r.h.both / r.h.b
def conditionalV (r : Reports) := r.v.both / r.v.b
/-- P(A|B), with H mixed out using the same prior. -/
def pooledConditional (r : Reports) :=
  (r.prior * r.h.both + (1-r.prior)*r.v.both) /
  (r.prior * r.h.b + (1-r.prior)*r.v.b)

def ConditionalIndependent (r : Reports) : Prop :=
  r.h.both = r.h.a * r.h.b ∧ r.v.both = r.v.a * r.v.b
/-- Independence in the prior mixture; distinct from independence within H/V. -/
def UnconditionalIndependent (r : Reports) : Prop :=
  r.prior*r.h.both+(1-r.prior)*r.v.both =
   (r.prior*r.h.a+(1-r.prior)*r.v.a)*
   (r.prior*r.h.b+(1-r.prior)*r.v.b)

def Criterion : Prop := ∀ r : Reports,
  (posterior r .b < posterior r .both ↔ conditionalV r < conditionalH r) ∧
  (conditionalV r < conditionalH r ↔ pooledConditional r < conditionalH r) ∧
  ((posterior r .a < posterior r .both ∧ posterior r .b < posterior r .both) ↔
    (conditionalV r < conditionalH r ∧ conditionalV r.swap < conditionalH r.swap)) ∧
  factor r .both = factor r .b * (conditionalH r / conditionalV r)

def IndependenceSuffices : Prop := ∀ r : Reports, ConditionalIndependent r →
  r.prior < posterior r .a → r.prior < posterior r .b →
  posterior r .a < posterior r .both ∧ posterior r .b < posterior r .both

/-- Integer weights /20 from issue #1396, all cells positive. -/
def reversal : Reports := ⟨1/2, by norm_num, by norm_num,
  ⟨5/20,7/20,7/20,1/20,by norm_num,by norm_num⟩,
  ⟨7/20,1/20,1/20,11/20,by norm_num,by norm_num⟩⟩
def oneSided : Reports := ⟨1/2, by norm_num, by norm_num,
  ⟨9/20,7/20,1/20,3/20,by norm_num,by norm_num⟩,
  ⟨3/20,1/20,5/20,11/20,by norm_num,by norm_num⟩⟩
def unconditional : Reports := ⟨1/2, by norm_num, by norm_num,
  ⟨1/20,2/20,8/20,9/20,by norm_num,by norm_num⟩,
  ⟨1/20,1/20,6/20,12/20,by norm_num,by norm_num⟩⟩

/-- Dependent within each hypothesis, yet both reports corroborate. -/
def dependentGrowth : Reports := ⟨1/2, by norm_num, by norm_num,
  ⟨8/20,4/20,4/20,4/20,by norm_num,by norm_num⟩,
  ⟨2/20,4/20,4/20,10/20,by norm_num,by norm_num⟩⟩

def Controls : Prop :=
  posterior reversal .a = 3/5 ∧ posterior reversal .b = 3/5 ∧
  posterior reversal .both = 5/12 ∧ posterior reversal .both < reversal.prior ∧
  factor reversal .a = 3/2 ∧ factor reversal .b = 3/2 ∧ factor reversal .both = 5/7 ∧
  posterior oneSided .a = 4/5 ∧ posterior oneSided .b = 5/9 ∧
  posterior oneSided .both = 3/4 ∧
  pooledConditional oneSided < conditionalH oneSided ∧
  conditionalH oneSided.swap < pooledConditional oneSided.swap ∧
  posterior oneSided .both < posterior oneSided .a ∧
  UnconditionalIndependent unconditional ∧
  unconditional.prior < posterior unconditional .a ∧
  unconditional.prior < posterior unconditional .b ∧
  posterior unconditional .both < posterior unconditional .a ∧
  posterior unconditional .both < posterior unconditional .b ∧
  ¬ ConditionalIndependent unconditional ∧
  ¬ ConditionalIndependent dependentGrowth ∧
  dependentGrowth.prior < posterior dependentGrowth .a ∧
  dependentGrowth.prior < posterior dependentGrowth .b ∧
  posterior dependentGrowth .a < posterior dependentGrowth .both ∧
  posterior dependentGrowth .b < posterior dependentGrowth .both

end TruthCore.Logic.CorrelatedTestimony1396
