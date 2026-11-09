module

public import TruthCore.Explanation.TruthmakerTheories

/-!
# Truthmaker conditions without rigid proposition availability

These bodies expose only the quantifier conditions in the existing definitions.
They do not define substantive truthmaking as material implication. `M` retains
its primitive grounding interpretation and open relevance/aboutness obligations.
The supplied carriers need not be finite; completeness for reality remains open.
-/

@[expose] public section
namespace TruthCore.Explanation.TruthmakerSourceScopes
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.DisjunctionGround
open TruthCore.Explanation.TruthmakerTheories

/-- The partial necessary condition at the selected world. Proposition existence
is a separate primitive predicate: unlike MakerNecessitation, rigid availability
is not assumed. No self-access, truth soundness, or world immanence is added.
This condition is not sufficient for grounding and gives no necessary bearer. -/
def GuardedNecessitationAt {W B F : Type} (A : Arena W B F)
    (M : Making W B F) (propositionExists : W → F → Prop) (a : W) : Prop :=
  ∀ b f, M a b f → ∀ v, Access A a v →
    A.ontic.ExistsAt v b → propositionExists v f → A.holds v f

/-- Coverage at a selected world, with a possibly different bearer per truth.
No all-world policy, exclusion, soundness, existence-label restriction or
uniform witness is added. Instantiating this at an actual world is explicit. -/
def EveryTruthHasMakerAt {W B F : Type} (A : Arena W B F)
    (M : Making W B F) (a : W) : Prop :=
  ∀ f, A.holds a f → ∃ b, M a b f

end TruthCore.Explanation.TruthmakerSourceScopes
