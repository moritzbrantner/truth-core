/-!
Source-derived readings from Thomas Aquinas, *Summa theologiae* I q.2 a.3 co.,
the *quinta via* (argument from the governance of things), and ad 2.

Vocabulary, all of it parameters rather than definitions:

* `Being` — the things quantified over, shared with the *prima via*.
* `End` — that for the sake of which something operates (*finis*).
* `NaturalBody x` — `x` is a natural body (*corpus naturale*).
* `HasCognition x` — `x` has cognition (*cognitio*); `Intelligent x` — `x`
  understands (*intelligens*). They are kept apart because the text names both
  (*ab aliquo cognoscente et intelligente*).
* `RegularlyAttains x e` — `x` operates always or for the most part in the same
  way so as to attain `e` (*semper aut frequentius eodem modo operantur, ut
  consequantur*).
* `Best x e` — `e` is what is best (*optimum*) for `x`.
* `ByChance x e` — `x` reaches `e` by chance (*a casu*).
* `TendsTo x e` — `x` tends to `e` as to an end, reaching it from intention
  (*ex intentione perveniunt ad finem*; *tendunt in finem*). *Intentio* is read
  in the broad sense of an ordering to an end; whether it is a knower's intention
  is exactly what the arrow-and-archer premise adds.
* `Directs d x e` — `d` directs `x` to `e` (*directa ab aliquo*, as the archer
  directs the arrow).
The two premises that connect the director to the *prima via*'s first mover are
not readings of this article: they are open bridges in
`TruthCore.Case.Catholicism.StageOneQuintaVia`. Aristotle's *Physics* II.8 statements on natural
teleology are not used: that result (`NaturalTeleology`) is a transcription over
opaque propositions; the coinciding claims are related by `supports` relations.

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-Q2-A3`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v w

/-- Natural bodies lack cognition (*aliqua quae cognitione carent, scilicet corpora
naturalia*). The *scilicet* identifies the things lacking cognition with natural
bodies; animals, which have sense cognition, are not natural bodies in this sense.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., fifth way.
-/
def NaturalBodiesLackCognitionReading {Being : Sort u}
    (NaturalBody HasCognition : Being → Prop) : Prop :=
  ∀ x, NaturalBody x → ¬ HasCognition x

/-- We see that natural bodies operate always or for the most part in the same way
so as to attain what is best (*Videmus enim ... semper aut frequentius eodem modo
operantur, ut consequantur id quod est optimum*), and there are natural bodies.

Reading A: the observation is about natural bodies as such, so it is stated for
every natural body; this is what the conclusion's *omnes res naturales* needs.
Reading B (`SomeNaturalBodiesActRegularlyForTheBestReading`) takes *aliqua*
literally.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., fifth way.
-/
def NaturalBodiesActRegularlyForTheBestReading {Being : Sort u} {End : Sort w}
    (NaturalBody : Being → Prop) (RegularlyAttains Best : Being → End → Prop) :
    Prop :=
  (∃ x, NaturalBody x) ∧ ∀ x, NaturalBody x → ∃ e, RegularlyAttains x e ∧ Best x e

/-- Reading B of the observation: some natural bodies operate always or for the
most part in the same way so as to attain what is best. It yields the conclusion
only for those bodies, not for *omnes res naturales*.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., fifth way.
-/
def SomeNaturalBodiesActRegularlyForTheBestReading {Being : Sort u} {End : Sort w}
    (NaturalBody : Being → Prop) (RegularlyAttains Best : Being → End → Prop) :
    Prop :=
  ∃ x, NaturalBody x ∧ ∃ e, RegularlyAttains x e ∧ Best x e

/-- What is attained always or for the most part is not attained by chance (*unde
patet quod non a casu*). Chance concerns what happens rarely (Aristotle,
*Physics* II.5 and II.8, 198b34-199a3, which Aquinas follows).

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., fifth way.
-/
def RegularityIsNotByChanceReading {Being : Sort u} {End : Sort w}
    (RegularlyAttains ByChance : Being → End → Prop) : Prop :=
  ∀ x e, RegularlyAttains x e → ¬ ByChance x e

/-- What regularly attains what is best attains it either by chance or from
intention (*non a casu, sed ex intentione perveniunt ad finem*): the step *unde
patet* needs this dichotomy. Bare material necessity, indifferent to the best, is
excluded by the restriction to `Best` (compare Aristotle's rain example, *Physics*
II.8, 198b16-23). This is the premise that a selection account, which produces
regular best outcomes neither by chance nor by tending to them, denies
(countermodel `necessityModel`).

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., fifth way.
-/
def RegularBestByChanceOrByIntentionReading {Being : Sort u} {End : Sort w}
    (RegularlyAttains Best ByChance TendsTo : Being → End → Prop) : Prop :=
  ∀ x e, RegularlyAttains x e → Best x e → ByChance x e ∨ TendsTo x e

/-- What lacks cognition does not tend to an end unless directed by something
knowing and intelligent, as the arrow by the archer (*Ea autem quae non habent
cognitionem, non tendunt in finem nisi directa ab aliquo cognoscente et
intelligente, sicut sagitta a sagittante*).

Only some knowing director is asserted; nothing says it is one and the same for
every thing, nor that it is the immediate director. This is the premise that an
immanent-teleology or teleonomy account denies (countermodel `teleonomyModel`).

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., fifth way.
-/
def NonCognitiveTendingNeedsKnowingDirectorReading {Being : Sort u} {End : Sort w}
    (HasCognition Intelligent : Being → Prop) (TendsTo : Being → End → Prop)
    (Directs : Being → Being → End → Prop) : Prop :=
  ∀ x e, ¬ HasCognition x → TendsTo x e →
    ∃ d, HasCognition d ∧ Intelligent d ∧ Directs d x e

/-- Natural bodies act for an end, not by chance but from intention: each natural
body tends to something best for it, and not by chance (*operantur propter finem
... non a casu, sed ex intentione perveniunt ad finem*). Intermediate conclusion. -/
def NaturalBodiesActForAnEndNotByChanceReading {Being : Sort u} {End : Sort w}
    (NaturalBody : Being → Prop) (Best ByChance TendsTo : Being → End → Prop) :
    Prop :=
  ∀ x, NaturalBody x → ∃ e, Best x e ∧ ¬ ByChance x e ∧ TendsTo x e

/-- Each natural body is directed to what is best for it by some knowing and
intelligent being. The conclusion the premises of the fifth way's body give
before any scope step: "for each, some director", not "one director for all". -/
def EachNaturalBodyDirectedByAKnowerReading {Being : Sort u} {End : Sort w}
    (NaturalBody HasCognition Intelligent : Being → Prop) (Best : Being → End → Prop)
    (Directs : Being → Being → End → Prop) : Prop :=
  ∀ x, NaturalBody x → ∃ e, Best x e ∧
    ∃ d, HasCognition d ∧ Intelligent d ∧ Directs d x e

/-- There is something intelligent by which all natural things are ordered to their
end (*Ergo est aliquid intelligens, a quo omnes res naturales ordinantur ad
finem*). One director for all: the scope of `∃` is outside `∀`. The closing *et
hoc dicimus Deum* is a separate claim and is not formalized.

Only natural bodies are covered, the things the premises speak of.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., fifth way.
-/
def OneIntelligentDirectsAllNaturalThingsReading {Being : Sort u} {End : Sort w}
    (NaturalBody Intelligent : Being → Prop)
    (Directs : Being → Being → End → Prop) : Prop :=
  ∃ d, Intelligent d ∧ ∀ x, NaturalBody x → ∃ e, Directs d x e

end TruthCore.Latin.Aquinas.SummaTheologiae
