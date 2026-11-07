module

public import TruthCore.Causality.PerfectionOfBeing
public import TruthCore.Alternatives.ActPotencyRegress

/-! The Meinongian rival to "actuality only insofar as being" against q.4 a.2
and q.5 a.1

`STMT-ACTUALITY-WITHOUT-BEING` (something is in act in some respect without
being: the golden mountain would be golden but not be) is the recorded rival of
`STMT-ACTUALITY-ONLY-INSOFAR-AS-BEING`. Under q.5 a.1 (perfect in a respect
exactly when in act in it) and q.4 a.2 (perfect only insofar as having being),
the rival is contradictory. So a Meinongian must deny one of the two: either
that being golden in act is being perfect in that respect, or that being
perfect in any respect requires being. Conditional refutation only. -/

@[expose] public section

namespace TruthCore.Causality.MeinongianActuality
open TruthCore.Alternatives.ActPotencyRegress (ActualityWithoutBeingReading)

/-- The Meinongian rival fails. -/
def NoActualityWithoutBeing {B R : Type} (InAct : B → R → Prop) (esse : R) : Prop :=
  ¬ ActualityWithoutBeingReading InAct esse

namespace Control
open TruthCore.Causality.PerfectionOfBeing (PerfectOnlyInsofarAsBeing)
open TruthCore.Causality.PerfectionOfBeing.Control (actTrue perfectTrue perfectNone)
open TruthCore.Latin.Aquinas.SummaTheologiae (PerfectInsofarAsInActReading)

/-- The golden mountain: one being in act in a respect (`true`) but not in being
(`false`). Keeping q.5 a.1 and dropping q.4 a.2, or keeping q.4 a.2 and dropping
q.5 a.1, the rival holds; so each refutation premise is needed. -/
def Certificate : Prop :=
  (PerfectInsofarAsInActReading perfectTrue actTrue ∧
    ¬ PerfectOnlyInsofarAsBeing perfectTrue actTrue false ∧
    ActualityWithoutBeingReading actTrue false) ∧
  (¬ PerfectInsofarAsInActReading perfectNone actTrue ∧
    PerfectOnlyInsofarAsBeing perfectNone actTrue false ∧
    ActualityWithoutBeingReading actTrue false)

end Control
end TruthCore.Causality.MeinongianActuality
