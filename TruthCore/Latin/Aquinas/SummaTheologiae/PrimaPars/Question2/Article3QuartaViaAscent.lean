module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia

/-!
Two premises of a causal-ascent derivation of the *quarta via*'s
grades-to-maximum step (#341). They use the existing vocabulary of
`Question2.Article3QuartaVia` (`InAct`, `MoreIn`, `CausesIn`) and add no
primitive. The derivation itself, with one omission countermodel per premise,
is the result `QUARTA-VIA-GRADES-MAXIMUM-FROM-CAUSAL-ASCENT`.

Existing results deliberately leave `MoreIn` free of any link to `InAct`
(`QuartaViaMaximumInBeing.flatMaximum`). `MoreSuchHasThePerfectionReading`
adds that link as a separate premise; nothing here changes the earlier
vocabulary or results.
-/

@[expose] public section

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- Whatever is more `r` than something has `r`: what is hotter is hot
(*sicut magis calidum est, quod magis appropinquat maxime calido*).

Only the exceeding side is constrained. The lesser comparand need not have `r`,
and nothing makes `MoreIn r` an order. Read from ST I q.2 a.3 co., quarta via,
*magis et minus dicuntur de diversis*: "more" and "less" `r` are said of the
things compared, so what is said more `r` is said `r`. Claim
`AQUINAS-ST-I-Q2-A3-MORE-SUCH-HAS-PERFECTION-A`.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., fourth way. -/
def MoreSuchHasThePerfectionReading {Being : Sort u} {Respect : Sort v}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) : Prop :=
  ∀ r x y, MoreIn r x y → InAct x r

/-- Whatever has `r` and is exceeded in `r` by something has `r` from a cause
distinct from itself: if `y` is more `r` than `x`, and `x` has `r`, some `c ≠ x`
causes `x`'s being `r`.

Read from SCG II.15 n.3 (*Quod igitur alicui minus convenit quam aliis, non
convenit ei ex sua natura tantum, sed ex alia causa*): what belongs to
something less than to others belongs to it not from its nature alone but from
another cause. *Alia causa* is read as a cause other than the bearer itself
(claim `AQUINAS-SCG-II-15-LESSER-HAS-IT-FROM-ANOTHER-CAUSE`). ST I q.44 a.1 co.,
on participated *esse*, supports it only (relation
`REL-AQUINAS-ST-I-Q44-A1-SUPPORTS-EXCEEDED-PERFECTION-IS-CAUSED`). The cause is
not required to have `r`, to be more `r`, or to be the exceeding `y`. -/
def ExceededPerfectionIsCausedReading {Being : Sort u} {Respect : Sort v}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ r x y, InAct x r → MoreIn r y x → ∃ c, c ≠ x ∧ CausesIn c x r

end TruthCore.Latin.Aquinas.SummaTheologiae
