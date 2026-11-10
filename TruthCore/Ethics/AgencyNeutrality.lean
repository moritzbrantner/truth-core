module
public import TruthCore.Ethics.HardCaseTyped
/-! Analyst structural test, attribution deferred. R p q is an independently
supplied pro-tanto reason of p to protect q's agency in the stipulated case.
It is not instrumental advantage, obligation, decisive priority or recognition.
The case application of this primitive is OPEN. No rationality predicate is
identified with moral agreement. Joint relabeling preserves indexical reasons;
agent neutrality holds the beneficiary fixed and changes the reason holder.
Neither property is adopted as a definition of moral adequacy or rationality. -/
@[expose] public section
namespace TruthCore.Ethics.AgencyNeutrality
open TruthCore.Ethics.HardCaseTyped
/-- A finite structural surrogate: self-reasons and joint relabeling do not
supply agent neutrality. Under self-reasons, the proposed neutrality premise
is equivalent to universal reasons. Full/diagonal/empty witnesses isolate
joint satisfiability and both omissions. The numeric comparison fixes private
and equal-sum outcomes, not their moral truth or actual human rationality. -/
def Controls : Prop :=
  ((∀ p : Person, p = p) ∧
   (∀ (s : Person → Person) p q, p = q → s p = s q) ∧
   ¬ ((Person.offender : Person) = Person.victim)) ∧
  (∀ (R : Person → Person → Prop), (∀ p, R p p) →
    ((∀ p q, R q q → R p q) ↔ (∀ p q, R p q))) ∧
  (∃ R : Person → Person → Prop,
    (∀ p, R p p) ∧ (∀ p q, R q q → R p q) ∧ R .offender .victim) ∧
  (∃ R : Person → Person → Prop,
    (∀ p, R p p) ∧ ¬ R .offender .victim) ∧
  (∃ R : Person → Person → Prop,
    (∀ p q, R q q → R p q) ∧ ¬ R .offender .victim) ∧
  ((3 : Int) > 1 ∧ (3 + (-10 : Int)) < (1 + 0 : Int))
end TruthCore.Ethics.AgencyNeutrality
