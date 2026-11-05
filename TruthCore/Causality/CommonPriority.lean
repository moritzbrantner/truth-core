module

public import TruthCore.Logic.Regress
public import TruthCore.Results.Causality.NecessarilyUnderived.PositiveUnion.Solution
public import TruthCore.Results.Causality.ParityUnionRegress.Solution
public import TruthCore.Models.NecessarilyUnderived

/-! Analyst configurations for #950. A fixed rank orders POSSIBLE existential-support
edges among rigid necessary bearers, not the time/order of actual events. Arbitrary
well-founded codomains are admitted: identity makes this an equivalent presentation
of union well-foundedness, not a weaker principle or an independent defense.

Existence-fact necessitation is only a modal consequence of the selected support
relation. It does not define full grounding, identify support with causal production,
or impose a source author's grounding account. See the linked source/type audit.
-/

@[expose] public section
namespace TruthCore.Causality.CommonPriority
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.German.Kant.CosmologicalInference
namespace OldModels
export TruthCore.Models.NecessarilyUnderived (rotating rotatingSupport varying varyingSupport)
end OldModels

/-- One world-independent map into an arbitrary well-founded priority relation.
Only edges in the existing necessary-support union must decrease that relation.
A Nat-valued rank is NOT assumed; such ranks can exclude transfinite heights. -/
def CommonRank {W B : Type} (m : Ontic W B) (R : W → B → B → Prop) (a : W) : Prop :=
  ∃ Rank : Type, ∃ priority : Rank → Rank → Prop,
    WellFounded priority ∧ ∃ rank : B → Rank,
      ∀ g n, UnionNecessarySupport m R a g n → priority (rank g) (rank n)

/-- Analyst bearer/existence-fact view of target-truth necessitation. The actual
edge may fail elsewhere; this condition only says that wherever its source's
existence fact holds in a world accessible FROM THAT EDGE'S WORLD, its target's
existence fact holds. No completeness or essence of the support is inferred. -/
def TruthNecessitation {W B : Type} (m : Ontic W B) (R : W → B → B → Prop) : Prop :=
  ∀ w g n, m.ExistsAt w g → R w g n →
    ∀ v, m.frame.access w v → m.ExistsAt v g → m.ExistsAt v n

/-- A stronger relation-persistence policy restricted to the fixed necessary
carrier: an edge persists wherever its two endpoints exist. This is an analyst
existential-support specialization, not Leuenberger's plural-fact Internality. -/
def NecessarySupportStable {W B : Type} (m : Ontic W B)
    (R : W → B → B → Prop) (a : W) : Prop :=
  ∀ w v g n, NecessaryAt m a g → NecessaryAt m a n →
    m.ExistsAt w g → R w g n → m.ExistsAt v g → m.ExistsAt v n → R v g n

/-- Closed comparison schema, with named independent controls rather than a
single fictitious joint model assembled from incidental properties. -/
def Comparison : Prop :=
  (∀ {W B : Type} (m : Ontic W B) R a,
    ActualReflexive m a → NecessarySupportStable m R a →
    WellFoundedPresentEsseSupport m R a → CommonRank m R a) ∧
  (∀ w, WellFoundedPresentEsseSupport OldModels.rotating OldModels.rotatingSupport w) ∧
  TruthNecessitation OldModels.rotating OldModels.rotatingSupport ∧
  NecessaryBeing OldModels.rotating false ∧ ActualReflexive OldModels.rotating false ∧
  NoContingentGroundOfNecessary OldModels.rotating OldModels.rotatingSupport false ∧
  ¬ CommonRank OldModels.rotating OldModels.rotatingSupport false ∧
  ¬ NecessarilyUnderived OldModels.rotating OldModels.rotatingSupport false ∧
  TruthCore.Causality.ParityUnionRegress.Certificate ∧
  TruthNecessitation TruthCore.Causality.ParityUnionRegress.model
    TruthCore.Causality.ParityUnionRegress.support ∧
  ¬ CommonRank TruthCore.Causality.ParityUnionRegress.model
    TruthCore.Causality.ParityUnionRegress.support false ∧
  CommonRank OldModels.varying OldModels.varyingSupport false ∧
  ¬ NecessarySupportStable OldModels.varying OldModels.varyingSupport false

/-- The necessary-target fragment of a truth-implication policy cannot constrain
its source. This is explicitly evaluated at a fixed world; it is not the full
all-target `TruthNecessitation` policy on the switching model. -/
def NoContingentBoundary : Prop :=
  (∀ g n, NecessaryAt TruthCore.Models.NecessarilyUnderived.switching false n →
    ∀ v, TruthCore.Models.NecessarilyUnderived.switching.frame.access false v →
    TruthCore.Models.NecessarilyUnderived.switching.ExistsAt v g →
    TruthCore.Models.NecessarilyUnderived.switching.ExistsAt v n) ∧
  CommonRank TruthCore.Models.NecessarilyUnderived.switching
    TruthCore.Models.NecessarilyUnderived.switchingSupport false ∧
  ¬ NoContingentGroundOfNecessary TruthCore.Models.NecessarilyUnderived.switching
    TruthCore.Models.NecessarilyUnderived.switchingSupport false ∧
  ¬ NecessarilyUnderived TruthCore.Models.NecessarilyUnderived.switching
    TruthCore.Models.NecessarilyUnderived.switchingSupport false

end TruthCore.Causality.CommonPriority
