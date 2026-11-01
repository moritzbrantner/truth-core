import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaGreatestDegree

/-! Attainment in the selected BEING respect for the greatest-degree root route.
This preserves the separate greatest-degree source interpretation; it does not
strengthen the old weak-maximality premises or modify their proof interfaces. -/
namespace TruthCore.Causality.GreatestDegreeRootRoute
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Some bearer attains a greatest represented degree of the supplied esse
respect. ST I q.2 a.3 co., quarta via, explicitly asserts something most being
(`Est igitur aliquid ... et per consequens maxime ens`), in the complete pinned
passage AQUINAS-ST-I-Q2-A3. This is an OPEN reading of that asserted attainment,
not a proof from grades, old weak H or the MostTrue bridge. The value map and
its application to analogical being remain explicit interpretation burdens.
No greatestness at unrelated perfections, actual-world presence, strict
supremacy, injective grading, uniqueness or linearity is built in. -/
def GreatestBeingDegreeAttained {B R Degree : Type} [Preorder Degree]
    (InAct : B → R → Prop) (esse : R) (value : B → Degree) : Prop :=
  ∃ g, GreatestDegreeBearer InAct esse value g

end TruthCore.Causality.GreatestDegreeRootRoute
