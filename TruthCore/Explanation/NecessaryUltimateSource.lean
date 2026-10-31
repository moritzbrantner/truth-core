import TruthCore.Explanation.AnselmUltimateSource
import TruthCore.Causality.SelectedAncestry

/-! Source-free same-witness composition interface. The original concrete
predicate, modal ontology and rigid candidate identity are preserved. Only
distinct through-sources count as selected grounds; through-self is not
productive self-grounding. The local ancestry and source-closure assumptions
are OPEN applications to this explicitly derived relation, not consequences
of naming it grounding. See docs/notes/necessary-simple-plurality.md. -/
namespace TruthCore.Explanation.NecessaryUltimateSource
open TruthCore.Explanation.AnselmUltimateSource
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)

/-- Reverse target/source orientation, excluding self-links. No adequacy or
foundation law is installed in this data adapter. Concrete is supplied, never
silently assigned to every bearer. -/
def distinctGroundProfile (m : Context W B) (concrete : B → Prop) : Profile W B where
  ontic := m.reality.ontic
  concrete := concrete
  grounds w source target := m.through w target source ∧ source ≠ target

/-- An actual concrete target's through-sources stay in the concrete domain.
Source actuality is a separate existing premise. Without this closure, absence
of concrete grounds does not exclude abstract through-sources. -/
def ConcreteSourcesAt (m : Context W B) (concrete : B → Prop) (w : W) : Prop :=
  ∀ x, concrete x → m.reality.ontic.ExistsAt w x →
    ∀ y, m.through w x y → concrete y

/-- One SAME actual ultimate source is necessary and every actual ultimate
source equals it. This excludes other ultimate sources, not other necessary
individuals that have distinct sources. -/
def NecessaryUniqueUltimateSourceAt (m : Context W B) (w : W) : Prop :=
  ∃ x, NecessaryAt m.reality.ontic w x ∧ UltimateSourceAt m w x ∧
    ∀ y, UltimateSourceAt m w y → y = x

end TruthCore.Explanation.NecessaryUltimateSource
