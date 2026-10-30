import TruthCore.Causality.NamedPotentialCauser
import TruthCore.Causality.SourceForest

/-! Analyst-defined integration for #319. R stays an explicit existential-support
relation. The one-way actual causal-edge interface below is OPEN, not sourced,
and is not an equation between causal power, explanation or esse. -/
namespace TruthCore.Causality.UnderivedCommonSource
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Causality.NamedPotentialCauser

/-- The existing actual-node carrier with R-support edges at one fixed world.
This is a graph view of the explicit R parameter, not an identification with Causes. -/
def actualSupportGraph {World Being : Type} (m : Ontic World Being)
    (R : World → Being → Being → Prop) (w : World) :
    TruthCore.Logic.Regress.Graph (Actual m w) := ⟨fun y x => R w y.val x.val⟩

/-- Same named individual is the unique source of the actual SUPPORT graph.
No ordinary causal relation or cross-world uniqueness is asserted. -/
def UniqueActualSupportSourceAt {World Being : Type} (m : Ontic World Being)
    (R : World → Being → Being → Prop) (w : World) (n : Being) : Prop :=
  ∃ hn : m.ExistsAt w n,
    (actualSupportGraph m R w).Source ⟨n, hn⟩ ∧
    ∀ s : Actual m w, (actualSupportGraph m R w).Source s → s.val = n

def CommonUnderivedSupportSource {World Being : Type} (m : Ontic World Being)
    (R : World → Being → Being → Prop) (w : World) : Prop :=
  ∃ n, NamedNecessarilyUnderived m R w n ∧ UniqueActualSupportSourceAt m R w n

/-- Every causal edge whose endpoints exist at the selected world is also an
R-support edge there. This disputed one-way interface does not constrain absent
endpoints or other worlds, nor identify the two relations. -/
def ActualCauseSupportsEsse {World Being : Type} (m : Ontic World Being)
    (R : World → Being → Being → Prop) (w : World) : Prop :=
  ∀ source target, m.ExistsAt w source → m.ExistsAt w target →
    m.Causes w source target → R w source target

/-- The given same n is an actual source and equals every actual source in the
selected world. No path from every node, cross-world uniqueness or attribute
beyond this causal-source property is asserted. -/
def UniqueActualSourceAt {World Being : Type} (m : Ontic World Being)
    (w : World) (n : Being) : Prop :=
  ∃ hn : m.ExistsAt w n,
    (actualGraph m w).Source ⟨n, hn⟩ ∧
    ∀ s : Actual m w, (actualGraph m w).Source s → s.val = n

/-- An existential #495 witness is retained as the SAME named underived
individual which uniquely identifies all actual causal sources at base w. -/
def CommonUnderivedActualSource {World Being : Type} (m : Ontic World Being)
    (R : World → Being → Being → Prop) (w : World) : Prop :=
  ∃ n, NamedNecessarilyUnderived m R w n ∧ UniqueActualSourceAt m w n
end TruthCore.Causality.UnderivedCommonSource
