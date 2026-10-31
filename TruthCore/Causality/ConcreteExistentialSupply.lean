import TruthCore.Causality.NecessaryRootFork
import TruthCore.Causality.DerivativeJointPower
import TruthCore.Causality.NecessaryConcreteUnderived

/-! Apply the existing joint-supply standard to one selected existential-grounding
profile. This is an explicit APPLICATION premise, not a source attribution or a
proof that actual existence obeys that standard. No event/bearer identification is
made: nodes here are the existing actual-concrete subtype itself. -/
namespace TruthCore.Causality.ConcreteExistentialSupply
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.JointGroups
open TruthCore.Causality.DerivativeJointPower
open TruthCore.Logic.Regress

variable {W B : Type}

/-- Same selected grounding relation, with both ends actual and concrete.
No temporal order or efficient-cause identification is added. -/
def graph (m : Profile W B) (w : W) : Graph {b // ActualConcrete m w b} :=
  ⟨fun a b => m.grounds w a.val b.val⟩

/-- At least one actual concrete candidate has joint Supply in the existing
recorded graph, with independently supplied contributions taken to be sources of
THIS existential-grounding relation. Each record lists all immediate actual
concrete grounds of a non-source target; its contributor set is nonempty by the
record's subtype. Applying this inductive supply standard to existence is the
explicit open commitment. No necessary source is built into it. -/
def ActualConcreteSupply (m : Profile W B) (w : W) : Prop :=
  ∃ target, Supply (recorded (graph m w)) (graph m w).Source target

/-- Reuse the earlier necessary-root/contingent-dependent model. The supply and
dependence requirements coexist with actual contingency, so this route does not
require necessitation of every effect by its necessary source. -/
def JointWitness : Prop :=
  let m := TruthCore.Causality.NecessaryConcreteUnderived.witnessProfile
  ActualConcreteSupply m false ∧ EveryContingentGroundedAt m false ∧
    ∃ b, m.concrete b ∧
      TruthCore.German.Kant.CosmologicalInference.ContingentAt m.ontic false b

end TruthCore.Causality.ConcreteExistentialSupply
