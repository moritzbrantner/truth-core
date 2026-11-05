module

/-!
Source-derived reading from Thomas Aquinas, *De ente et essentia* c.3
(Baur/Koch numbering, Corpus Thomisticum anchor [69874]), passage
`AQUINAS-DE-ENTE-C3-4`, about the reception of a thing's act of being (esse).

Vocabulary, shared with `SubsistentBeingIsInfiniteReading` (ST I q.7 a.1) and
q.3 a.4: `esseOf x` is the represented act of being of `x`, a value of the sort
`Principle`. `EsseReceivedIn x r` says that the act of being *of x* is received
in the principle `r` (DEF-ESSE-RECEIVED-IN). `ReceptivePotencyTo p a` says that
the principle `p` stands in receptive potency to `a` as to its act
(DEF-RECEPTIVE-POTENCY). This is the potency of a recipient that may already
actually have the received act. It is not the legacy `InPotency x r` (able to
have a respect without actually having it), and no step relates the two. Both
relations are parameters whose content is fixed only by the premises that use
them (DISAMB-ESSE-RECEPTION).
-/

@[expose] public section

namespace TruthCore.Latin.Aquinas.DeEnte

universe u w

/-- A receiver is in potency to what it receives: c.3 [69874], "omne autem quod
recipit aliquid ab alio est in potentia respectu illius, et hoc quod receptum
est in eo est actus eius".

Read as: if x's esse is received in r, then r stands in receptive potency to
x's esse. Only reception *in* a principle is formalized, not the origin "from
another". The reading does not say that a receiver differs from what it
receives; that is the separate unattributed premise
`TruthCore.Causality.EsseReception.NothingInReceptivePotencyToItself`.

Source: Thomas Aquinas, *De ente et essentia* c.3 [69874].
-/
def ReceiverInPotencyToReceivedEsseReading {Being : Sort u} {Principle : Sort w}
    (esseOf : Being → Principle) (EsseReceivedIn : Being → Principle → Prop)
    (ReceptivePotencyTo : Principle → Principle → Prop) : Prop :=
  ∀ x r, EsseReceivedIn x r → ReceptivePotencyTo r (esseOf x)

end TruthCore.Latin.Aquinas.DeEnte
