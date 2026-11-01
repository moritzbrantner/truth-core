import TruthCore.Explanation.FixedConstituentNecessaryBeing
import TruthCore.Results.Explanation.NecessaryFactBoundary.Solution

namespace TruthCore.Results.Explanation.FixedConstituentNecessaryBeing
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.ExplanatoryAdequacy
open TruthCore.Explanation.FixedConstituentNecessaryBeing
open TruthCore.Explanation.StoppingPoints (NecessaryFact)
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Logic (ExcludedMiddle)

/-- Preserve EVERY assigned candidate of this particular fact. Actual truth
and boxed truth are distinct; no reflexive frame or fact=being axiom is used. -/
theorem sameBearer {W B F : Type} (A : Arena W B F) (w : W) (f : F)
    (K : F → Set B) (b : B) (hMember : b ∈ K f)
    (hActual : A.holds w f) (hNecessary : NecessaryFact A w f)
    (hRealized : ∀ v, A.holds v f → ∀ c ∈ K f, A.ontic.ExistsAt v c) :
    A.ontic.ExistsAt w b ∧ NecessaryAt A.ontic w b := by
  exact ⟨hRealized w hActual b hMember,
    fun v hv => hRealized v (hNecessary v hv) b hMember⟩

/-- Unregistered selected-fact consumer. Choose once from the SAME fixed set;
no world-relative choice of bearers, positive fact label or model is introduced. -/
theorem necessaryBeingOfFact {W B F : Type} (A : Arena W B F) (w : W) (f : F)
    (K : F → Set B) (hActual : A.holds w f) (hNecessary : NecessaryFact A w f)
    (hNonempty : (K f).Nonempty)
    (hRealized : ∀ v, A.holds v f → ∀ c ∈ K f, A.ontic.ExistsAt v c) :
    NecessaryBeing A.ontic w := by
  obtain ⟨b, hb⟩ := hNonempty
  have hSame := sameBearer A w f K b hb hActual hNecessary hRealized
  exact ⟨b, hSame.1, hSame.2⟩

/-- Import necessary-reason extraction, then realize a SAME fixed assigned
candidate. Six explicit inputs give bare NE, not a necessary cause or God. -/
theorem necessaryBeing {W B F : Type} (A : Arena W B F) (w : W)
    (S : F → Prop) (x : F) (K : F → Set B)
    (hEM : ExcludedMiddle)
    (hAccount : ReasonClosed A w S x)
    (hContingent : Contingent A w x)
    (hFounded : Founded A w S)
    (hNonempty : AccountConstituentsNonempty S K)
    (hRealized : AccountConstituentsRealized A S K) : NecessaryBeing A.ontic w := by
  obtain ⟨r, hr, hActual, hNecessary, _hReasonRole⟩ :=
    TruthCore.Results.Explanation.NecessaryFactBoundary.necessaryReason
      A w S x hEM hAccount hContingent hFounded
  exact necessaryBeingOfFact A w r K hActual hNecessary
    (hNonempty r hr) (hRealized r hr)

end TruthCore.Results.Explanation.FixedConstituentNecessaryBeing
