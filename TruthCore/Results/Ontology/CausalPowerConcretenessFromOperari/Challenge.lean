import TruthCore.Causality.CausalPowerConcreteness
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.OperationFollowsBeing
import TruthCore.Ontology.ConcreteAbstract
namespace TruthCore.Results.Ontology.CausalPowerConcretenessFromOperari
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Causality.CausalPowerConcreteness
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.OperationFollowsBeing
open TruthCore.Ontology.ConcreteAbstract
/-- The owner principle (weak version), derived from operari sequitur esse and
the esse sense of concrete: at w, every bearer of causal power and every cause
has esse in re. Causing, and having active power, require being in act in some
respect (ST I q.75 a.2; q.25 a.1); whatever is in act in some respect has being
(ST I q.4 a.1 ad 3). Concreteness is `HasEsseInRe`, defined from `InAct`/`esse`
and not from causation or power, so no premise contains the conclusion. The
derivation is conditional on these three open readings. It does not decide which
candidates cause; that `InAct x esse` is being in re is the adopted definition. -/
theorem causalPowerConcretenessOfOperariSequiturEsse {W B R : Type} (o : Ontic W B)
    (InAct : B → R → Prop) (esse : R) (hasCausalPower : W → B → Prop) (w : W)
    (hOperation : OperationOnlyOfBeingInActReading o InAct w)
    (hActivePower : ActivePowerOnlyInsofarAsInActReading hasCausalPower InAct w)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse) :
    OwnerCommitmentAt o (HasEsseInRe InAct esse) hasCausalPower w := by
  sorry
end TruthCore.Results.Ontology.CausalPowerConcretenessFromOperari
