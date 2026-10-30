import TruthCore.German.Kant.CosmologicalInference

/-! One-way actuality interfaces for the #319 foundation investigation.
The ontic existence assignment, supplied act-in-esse predicate and represented
cause/support relations retain independent meanings. These declarations assert
neither interface nor a metaphysical analysis of existence. -/
namespace TruthCore.Causality.ExistenceActuality

open TruthCore.German.Kant.CosmologicalInference

/-- Every represented existent at this selected world is in act in the chosen
esse respect. This OPEN interface is only one direction: it supplies neither
existence from act, actual presence of causes, causal correspondence, modal
necessity, nor identity of essence and esse. The interpretation of `InAct` and
`esse` remains that of the supplied source profile. -/
def ExistingInActAt {World Being Respect : Type} (m : Ontic World Being)
    (InAct : Being → Respect → Prop) (esse : Respect) (w : World) : Prop :=
  ∀ x, m.ExistsAt w x → InAct x esse

/-- A numerically distinct cause in the chosen esse respect, with both endpoints
already present at this world, gives an R-support edge there. This OPEN direct
interface does not map all ordinary `m.Causes` edges to R. It supplies neither
endpoint presence nor target actuality; ordinary event causation, conservation
and explanatory sufficiency are not identified with R by this definition. -/
def ActualEsseCausesSupportAt {World Being Respect : Type} (m : Ontic World Being)
    (R : World → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) (w : World) : Prop :=
  ∀ c x, m.ExistsAt w c → m.ExistsAt w x → c ≠ x →
    CausesIn c x esse → R w c x

end TruthCore.Causality.ExistenceActuality
