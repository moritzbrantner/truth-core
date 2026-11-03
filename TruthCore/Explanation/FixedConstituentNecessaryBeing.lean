import TruthCore.Explanation.NecessaryFactBoundary
import TruthCore.Explanation.StoppingPoints

/-!
Analyst fact-to-bearer consumer on a genuine PSRStrength.Arena. K assigns a
fixed candidate set to each fact; assignment alone proves no real constitution.
Nonempty assigned sets and realization wherever a fact holds are separate OPEN
premises, restricted to the supplied account. No fact/bearer identification,
positive-label constructor, phantom Ontic or modal frame law is introduced.
-/
namespace TruthCore.Explanation.FixedConstituentNecessaryBeing
open TruthCore.Explanation.PSRStrength

/-- Each fact in THIS account has a nonempty assigned candidate set. The
world-independent assignment K is ordinary data, not a proof of constitution. -/
def AccountConstituentsNonempty {B F : Type} (S : F → Prop)
    (K : F → Set B) : Prop :=
  ∀ f, S f → (K f).Nonempty

/-- Every assigned candidate of an account fact exists wherever THAT SAME
fact holds, including the actual world. Constitution/realization applicability
is independently OPEN; no necessity is built into this policy's consequent. -/
def AccountConstituentsRealized {W B F : Type} (A : Arena W B F)
    (S : F → Prop) (K : F → Set B) : Prop :=
  ∀ f, S f → ∀ v, A.holds v f → ∀ b ∈ K f, A.ontic.ExistsAt v b

end TruthCore.Explanation.FixedConstituentNecessaryBeing
