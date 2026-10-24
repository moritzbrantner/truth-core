/-!
Source-derived readings from Thomas Aquinas, *Summa theologiae* I-II q.94 a.4 co.
(*utrum lex naturae sit una apud omnes*), used by the moral-error comparison
(#183).

Vocabulary, all of it parameters rather than definitions:

* `Agent` — people and peoples who hold moral views.
* `Sentence` — declarative sentences, moral ones included.
* `Moral φ` — `φ` is a moral sentence: a practical judgment about what is to be
  done or what is just.
* `TruthApt φ` — `φ` has a truth value.
* `Holds φ` — `φ` is true.
* `Accepts x φ` — `x` holds `φ` to be so.

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 7 (Rome 1892),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-II-Q94-A4`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- Practical judgments have truth: in practical matters there is "truth or
practical rectitude" (*veritas vel rectitudo practica*), the same for all as to
the common principles; "this is right and true for all, that one act according
to reason" (*apud omnes enim hoc rectum est et verum, ut secundum rationem
agatur*). Even where a proper conclusion fails in some case, it fails by not
being right, that is by being false there.

Read as: every moral sentence has a truth value. Only truth-aptness is
formalized, not which moral sentences are true, nor the claim that the common
principles are equally known to all.

Source: Aquinas, *Summa theologiae* I-II q.94 a.4 co.
-/
def MoralJudgmentsAreTruthAptReading {Sentence : Sort u}
    (Moral TruthApt : Sentence → Prop) : Prop :=
  ∀ φ, Moral φ → TruthApt φ

/-- Among the ancient Germans robbery was not regarded as unjust, although it
is expressly against the natural law (*sicut apud Germanos olim latrocinium non
reputabatur iniquum, cum tamen sit expresse contra legem naturae*, citing
Caesar, *De bello Gallico*). Aquinas gives this as a case of natural-law
knowledge failing in a proper conclusion because reason was depraved "by
passion, or bad custom, or a bad disposition of nature".

`germans` is that people and `robberyNotUnjust` the moral sentence "robbery is
not unjust". The reading: they held it, it is moral, and it is not true. Its
truth-aptness is the separate reading `MoralJudgmentsAreTruthAptReading`.

Source: Aquinas, *Summa theologiae* I-II q.94 a.4 co.
-/
def GermansHeldRobberyNotUnjustReading {Agent : Sort u} {Sentence : Sort v}
    (Accepts : Agent → Sentence → Prop) (Moral Holds : Sentence → Prop)
    (germans : Agent) (robberyNotUnjust : Sentence) : Prop :=
  Accepts germans robberyNotUnjust ∧ Moral robberyNotUnjust ∧ ¬ Holds robberyNotUnjust

end TruthCore.Latin.Aquinas.SummaTheologiae
