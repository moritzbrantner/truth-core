module

public import TruthCore.Causality.NecessaryClassicalGodRootControl

/-!
Concrete #1119 boundary on the EXISTING full25 God/attributes fixture. No
signature field, respect domain or earlier positive interpretation is changed.
The entire old Control, including the old18 control, inputs and same source,
is retained. Revelation and the phase-1 root fail on this exact dictionary.

The two negative facts have DIFFERENT reasons: recognizable revelation is
assigned False, and divine foundation as teaching authority is assigned False.
Revelation is not a conjunct of the root definition, so its failure alone is
not used to infer failure of the root. This is a populated formal interpretation,
not a possible theology, complete root-premise model, or joint-route settlement.
-/

@[expose] public section

namespace TruthCore.Causality.ClassicalGodRevelationBoundary
open TruthCore.Case.Catholicism
open TruthCore.Causality.NecessaryClassicalGodRootControl (signature)

/-- The positive full25 configuration survives together with explicit stage1
and stage2 conclusions, while the shared stage3 obligation and phase1 root fail.
All predicates refer to the SAME existing signature. The old interface list is
not every premise or floor of any current Catholicism route. -/
def Control : Prop :=
  TruthCore.Causality.NecessaryClassicalGodRootControl.Control ∧
  GodExists signature.IsGod ∧ GodHasClassicalAttributes signature ∧
  ¬ RevelationPossibleAndRecognizable signature ∧ ¬ CatholicismTrue signature

end TruthCore.Causality.ClassicalGodRevelationBoundary
