/-!
Source-derived readings from Thomas Aquinas, *De ente et essentia* capp. 3–4
(Baur/Koch numbering, Corpus Thomisticum anchors [69874]–[69875]), passage
`AQUINAS-DE-ENTE-C3-4`, about the reception of a thing's act of being (esse).

Vocabulary, shared with `SubsistentBeingIsInfiniteReading` (ST I q.7 a.1) and
q.3 a.4: `essenceOf x` and `esseOf x` are the represented essence and act of
being of `x`, both values of one sort `Principle`. The new relation
`EsseReceivedIn x r` says that the act of being *of x* is received in the
principle `r` (DEF-ESSE-RECEIVED-IN). It is indexed to the act of being of a
particular thing: it is not the reception of a form in matter, not the
reception of a quality, and not efficient causation of esse "from another"
(DISAMB-ESSE-RECEPTION). Its content is fixed only by the premises that use it.
-/

namespace TruthCore.Latin.Aquinas.DeEnte

universe u w

/-- The esse of a thing, where received, is received in that thing's own
essence or nature: c.4 [69875] (second mode of essence) says the esse of
created intellectual substances is "receptum et ideo limitatum et finitum ad
capacitatem naturae recipientis", and c.3 [69874] says the quiddity of an
intelligence "sit in potentia respectu esse, quod a Deo recipit".

Read as: every principle in which x's esse is received is x's own essence. The
source names the receiving nature for the intellectual substances under
discussion; the reading generalizes it to every thing whose esse is received
(open generalization, see the claim). It says nothing about reception of forms
in matter.

Source: Thomas Aquinas, *De ente et essentia* c.4 [69875], with c.3 [69874].
-/
def EsseReceivedInOwnEssenceReading {Being : Sort u} {Principle : Sort w}
    (essenceOf : Being → Principle) (EsseReceivedIn : Being → Principle → Prop) : Prop :=
  ∀ x r, EsseReceivedIn x r → r = essenceOf x

/-- A receiving principle is not the act it receives: c.3 [69874], "omne autem
quod recipit aliquid ab alio est in potentia respectu illius, et hoc quod
receptum est in eo est actus eius".

Read as: if x's esse is received in r, then r is not x's esse itself. The
sentence correlates the receiver as potency with the received item as its act;
the reading takes that correlation to require two principles, so that no esse
is received in itself. That non-identity is the reading's step beyond the
sentence's words, stated in the claim.

Source: Thomas Aquinas, *De ente et essentia* c.3 [69874].
-/
def ReceiverIsNotTheReceivedEsseReading {Being : Sort u} {Principle : Sort w}
    (esseOf : Being → Principle) (EsseReceivedIn : Being → Principle → Prop) : Prop :=
  ∀ x r, EsseReceivedIn x r → r ≠ esseOf x

end TruthCore.Latin.Aquinas.DeEnte
