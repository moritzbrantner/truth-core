import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question48.Articles2and3

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- ST I q.48 a.5 co., pinned passage `AQUINAS-ST-I-Q48-A5`:
privation of due operation in voluntary matters has the character of culpa.
The two operational defects named are total absence and lack of due mode/order.

`Agent` and `Operation` instantiate the existing q.48 being/perfection carriers;
no identification with the q.94 natural-law predicate or O'Connor's moral
sentences is asserted. `Voluntary a o` says the operation is under the agent's
voluntary control, not that every operation of a rational creature is voluntary.
`Ordered a o` means having its due mode and order. `Culpa` remains a predicate
constrained by this sourced sufficient condition, not a definition by fiat.

This directional reading does not assert that culpa occurs, nor its converse.
The contrasting poena concerns loss of form/integrity and opposition to the will;
the article's division concerns voluntary matters, expressly not all evil (ad 2).
-/
def VoluntaryOperationDefectIsCulpaReading {Agent : Type u} {Operation : Type v}
    (Voluntary Due Performs Ordered Culpa : Agent → Operation → Prop) : Prop :=
  ∀ a o, Voluntary a o → Due a o → (¬ Performs a o ∨ ¬ Ordered a o) → Culpa a o

/-- The wholly absent due-operation branch of q.48 a.5, as a conditional
answer to Q-MORAL-GROUNDING: for an agent with a voluntarily controlled due
operation wholly absent, there is both culpa in that operation and evil in
the agent. This does not cover every culpa (the disordered-performance branch
is not an absence of the operation), assert an actual instance, or supply
an explanation of divine permission. -/
def AbsentVoluntaryOperationIsCulpaAndEvilReading {Agent : Type u} {Operation : Type v}
    (Voluntary Due Performs Culpa : Agent → Operation → Prop)
    (Evil : Agent → Prop) : Prop :=
  ∀ a o, Voluntary a o → Due a o → ¬ Performs a o → Culpa a o ∧ Evil a

end TruthCore.Latin.Aquinas.SummaTheologiae
