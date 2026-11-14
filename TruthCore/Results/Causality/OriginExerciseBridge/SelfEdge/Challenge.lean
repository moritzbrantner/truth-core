import TruthCore.Causality.OriginExerciseBridge
import TruthCore.Causality.ExistentialSelfActualization
import TruthCore.Results.Causality.OriginExerciseBridge.Solution

/-! ## Self-edge sibling of the origin-to-exercise bridge (#1610)

The no-self-origination route uses only self-edges, so this sibling route
consumes `OriginHasProductiveSelfExercise`. The universal bridge strengthens it,
and the difference is certified as the clause for origin edges between distinct
beings. The frozen universal-premise Challenge of
`TruthCore.Results.Causality.OriginExerciseBridge` is unchanged.
-/

namespace TruthCore.Results.Causality.OriginExerciseBridge.SelfEdge

open TruthCore.Causality.TermSenseForks
open TruthCore.Causality.OriginExerciseBridge
open TruthCore.Causality.ExistentialSelfActualization

/-- If every self-origin edge has an exercise of that very being producing its
own existence, an existing prohibition on productive self-actualization
excludes self-origin. This result has TWO explicit premises: the self-edge
bridge and the independently recorded NoSelfProduction statement. That latter
statement already has a certified route from four open priority premises.
Nothing defines CausesOrigin as irreflexive, and no premise concerns origin
edges between distinct beings. -/
theorem noSelfOriginFromSelfExercise {Being Respect Exercise : Type}
    (F : CauseFrame Being Respect)
    (Occurs : Exercise → Prop) (bearer : Exercise → Being)
    (produces : Exercise → Being → Prop)
    (hOrigin : OriginHasProductiveSelfExercise F Occurs bearer produces)
    (hNoSelf : NoSelfProduction Occurs bearer produces) :
    NothingOriginatesItself F := by
  sorry

/-- The universal origin-to-exercise bridge entails its self-edge sibling:
instantiate the universal clause at the edge `CausesOrigin x x`. This backs
the `strengthens` registration (universal → self-edge). -/
theorem selfExerciseOfExercise {Being Respect Exercise : Type}
    (F : CauseFrame Being Respect)
    (Occurs : Exercise → Prop) (bearer : Exercise → Being)
    (produces : Exercise → Being → Prop)
    (hOrigin : OriginHasProductiveExercise F Occurs bearer produces) :
    OriginHasProductiveSelfExercise F Occurs bearer produces := by
  sorry

/-- Certified difference (#1598): the universal bridge is exactly its
self-edge sibling together with the clause for edges that are not self-edges.
Premise-free comparison of the two encodings. -/
theorem universalOverSelfExact : UniversalOverSelfExact := by
  sorry

/-- Strictness: in the other-only setting the self-edge sibling holds and the
universal bridge fails. A formal interpretation only. -/
theorem otherOnlySeparates : OtherOnlySeparates := by
  sorry

/-- Consistency check (unregistered): the frozen universal-premise theorem
factors through the strengthens lemma and the self-edge route. -/
example {Being Respect Exercise : Type}
    (F : CauseFrame Being Respect)
    (Occurs : Exercise → Prop) (bearer : Exercise → Being)
    (produces : Exercise → Being → Prop)
    (hOrigin : OriginHasProductiveExercise F Occurs bearer produces)
    (hNoSelf : NoSelfProduction Occurs bearer produces) :
    NothingOriginatesItself F :=
  noSelfOriginFromSelfExercise F Occurs bearer produces
    (selfExerciseOfExercise F Occurs bearer produces hOrigin) hNoSelf

end TruthCore.Results.Causality.OriginExerciseBridge.SelfEdge
