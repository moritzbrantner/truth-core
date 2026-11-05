module

/-!
Source-derived readings from Thomas Aquinas, *Summa theologiae* I q.7 a.1–2 co.
on limitation of esse by reception and on infinity in the sense of perfection.

Vocabulary: `EsseLimited x` says the act of being *of x* is limited (finite in
formal perfection, DEF-ESSE-LIMITED); `EsseReceivedIn x r` as in
`TruthCore.Latin.Aquinas.DeEnte` (DEF-ESSE-RECEIVED-IN); `Infinite` is the
existing primitive predicate of `SubsistentBeingIsInfiniteReading`
(DEF-INFINITE). Infinity here is infinity of perfection, not quantity or
indeterminate matter (q.7 a.1 ad 2; DISAMB-INFINITY).

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4,
`scta-texts/TAca84`, passages `AQUINAS-ST-I-Q7-A1` and `AQUINAS-ST-I-Q7-A2`.
-/

@[expose] public section

namespace TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception

universe u w

/-- Esse is limited only through reception: the warrant of q.7 a.1 co.'s step
"cum igitur esse divinum non sit esse receptum in aliquo ... manifestum est quod
ipse Deus sit infinitus", after "forma ... per hoc quod recipitur in materia, fit
forma determinate huius rei" and "illud autem quod est maxime formale omnium,
est ipsum esse".

Read as: if the esse of x is limited, it is received in some principle. Only
the act of being is covered, not every act or form; a form not received in
matter can still have limited esse (a.2), and that is consistent with this
reading because its esse is received.

Source: Thomas Aquinas, *Summa theologiae* I q.7 a.1 co.
-/
def EsseLimitedOnlyThroughReceptionReading {Being : Sort u} {Principle : Sort w}
    (EsseLimited : Being → Prop) (EsseReceivedIn : Being → Principle → Prop) : Prop :=
  ∀ x, EsseLimited x → ∃ r, EsseReceivedIn x r

/-- What has unlimited esse is infinite: "infinitum dicitur aliquid ex eo quod
non est finitum" (a.1 co.), where infinity "ex parte formae" is that of
perfection and esse is most formal; a.2 co. denies infinity simpliciter to a
subsistent created form exactly because "ipsum eius esse sit receptum et
contractum ad determinatam naturam".

Read as: a being whose esse is not limited satisfies the primitive `Infinite`.
This gives a sufficient condition only; it does not define `Infinite`.

Source: Thomas Aquinas, *Summa theologiae* I q.7 a.1 co., with a.2 co.
-/
def UnlimitedEsseIsInfiniteReading {Being : Sort u}
    (EsseLimited : Being → Prop) (Infinite : Being → Prop) : Prop :=
  ∀ x, ¬ EsseLimited x → Infinite x

end TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception
