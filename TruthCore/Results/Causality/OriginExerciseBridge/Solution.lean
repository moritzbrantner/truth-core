module

public import TruthCore.Causality.OriginExerciseBridge
public import TruthCore.Causality.ExistentialSelfActualization
public import TruthCore.Results.Causality.ExistentialSelfActualization.Solution

@[expose] public section

namespace TruthCore.Results.Causality.OriginExerciseBridge

open TruthCore.Causality.TermSenseForks
open TruthCore.Causality.OriginExerciseBridge
open TruthCore.Causality.ExistentialSelfActualization

/-- If every origin-cause edge has an exercise of its source producing the
target's existence, an existing prohibition on productive self-actualization
excludes self-origin. This result has TWO explicit premises: the new bridge
and the independently recorded NoSelfProduction statement. That latter
statement already has a certified route from four open priority premises.
Nothing defines CausesOrigin as irreflexive. -/
theorem noSelfOriginFromNoSelfProduction {Being Respect Exercise : Type}
    (F : CauseFrame Being Respect)
    (Occurs : Exercise → Prop) (bearer : Exercise → Being)
    (produces : Exercise → Being → Prop)
    (hOrigin : OriginHasProductiveExercise F Occurs bearer produces)
    (hNoSelf : NoSelfProduction Occurs bearer produces) :
    NothingOriginatesItself F := by
  intro x hCausesOrigin
  obtain ⟨a, hOccurs, hBearerEq, hProduces⟩ := hOrigin x x hCausesOrigin
  have hProducesBearer : produces a (bearer a) := by
    simpa [hBearerEq] using hProduces
  exact hNoSelf a hOccurs hProducesBearer

/-- Fully composed Lean witness: use the previously verified productive
self-actualization theorem to obtain NoSelfProduction from the four separately
open mixed-priority premises, then apply the new two-premise theorem. The
corpus records this as two linked arguments, not a new independent floor. -/
theorem noSelfOriginFromExercise {Being Respect Exercise : Type}
    (F : CauseFrame Being Respect)
    (Occurs : Exercise → Prop) (bearer : Exercise → Being)
    (produces : Exercise → Being → Prop)
    (Prior : Sum Being Exercise → Sum Being Exercise → Prop)
    (hOrigin : OriginHasProductiveExercise F Occurs bearer produces)
    (hBearer : BearerPrior Occurs bearer Prior)
    (hProduct : ProductPrior Occurs produces Prior)
    (hIrreflexive : IrreflexivePriority Prior)
    (hTransitive : TransitivePriority Prior) :
    NothingOriginatesItself F := by
  have hNoSelf := TruthCore.Results.Causality.ExistentialSelfActualization.noSelf
    Occurs bearer produces Prior hBearer hProduct hIrreflexive hTransitive
  exact noSelfOriginFromNoSelfProduction F Occurs bearer produces hOrigin hNoSelf

end TruthCore.Results.Causality.OriginExerciseBridge
