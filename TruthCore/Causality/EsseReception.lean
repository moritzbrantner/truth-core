/-!
Two unattributed open premises about the reception of esse. They are used in
deriving `SubsistentBeingIsInfiniteReading` (result
SUBSISTENT-INFINITY-FROM-RECEPTION). No source claim states either in this
generality. Vocabulary as in `TruthCore.Latin.Aquinas.DeEnte`.
-/

namespace TruthCore.Causality.EsseReception

universe u w

/-- OPEN, unattributed: every principle in which the esse of x is received is
x's own essence.

De ente c.4 [69875] says this for created intellectual substances ("ad
capacitatem naturae recipientis"), and ST I q.7 a.2 co. says it for subsistent
created forms ("receptum et contractum ad determinatam naturam"). The
generalization to every thing whose esse is received is not attributed to
either text. It does not assert that any esse is received, and it says nothing
about forms received in matter. -/
def EsseReceivedOnlyInOwnEssence {Being : Sort u} {Principle : Sort w}
    (essenceOf : Being → Principle) (EsseReceivedIn : Being → Principle → Prop) : Prop :=
  ∀ x r, EsseReceivedIn x r → r = essenceOf x

/-- OPEN, unattributed: no principle is in receptive potency to itself as to
its own act. A receiver and the act it receives are two principles.

De ente c.3 [69874] correlates a receiver (potency) with what it receives
(act). That the correlation requires two principles is not stated there, and
the text applies it only after arguing that intelligences have esse distinct
from essence (ATTEMPT-SUBSISTENT-INFINITY-RECEPTION-AUDIT-20261031). -/
def NothingInReceptivePotencyToItself {Principle : Sort w}
    (ReceptivePotencyTo : Principle → Principle → Prop) : Prop :=
  ∀ p, ¬ ReceptivePotencyTo p p

end TruthCore.Causality.EsseReception
