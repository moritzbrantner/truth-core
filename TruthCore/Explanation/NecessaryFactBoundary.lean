import TruthCore.Explanation.ExplanatoryAdequacy
import TruthCore.Logic.ExcludedMiddle

/-! An unattributed fact-level composition for #786/#545. This reuses #750's
reason-closed account and contingent-reason foundedness, without identifying
facts with concrete bearers or admitted reasons with efficient causes. -/
namespace TruthCore.Explanation.NecessaryFactBoundary

open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.ExplanatoryAdequacy
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Logic (ExcludedMiddle)

/-- A member of the account is actually true and true at every accessible world,
and is an admitted reason for some contingent member of the same account. The
contingent member need not be the original explanandum; no ancestral path,
autonomy, ungroundedness or efficient production is asserted. -/
def NecessaryReasonForMember (A : Arena W B F) (a : W) (S : F → Prop) : Prop :=
  ∃ r, S r ∧ A.holds a r ∧ (∀ v, Access A a v → A.holds v r) ∧
    ∃ c, S c ∧ Contingent A a c ∧ A.explains a r c

/-- Conditional positive extraction, its nonnecessitation cost, and a single
existing law interpretation satisfying the explanatory backgrounds and the
positive fact conclusion while having no necessary individual. The universal
clause retains excluded middle as a premise, not an axiom or proved fact. -/
def Certificate : Prop :=
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (S : F → Prop) (x : F),
    ExcludedMiddle → ReasonClosed A a S x → Contingent A a x → Founded A a S →
      NecessaryReasonForMember A a S ∧ ¬ AllReasonsNecessitate A a S) ∧
  (ReasonClosed law 0 OneSource .target ∧ Contingent law 0 .target ∧
    Founded law 0 OneSource ∧ NecessaryReasonForMember law 0 OneSource ∧
    ∀ b, ¬ NecessaryAt law.ontic 0 b)

end TruthCore.Explanation.NecessaryFactBoundary
