import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia

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

Unattributed open bridge. ST I q.44 a.1 co. says that what is found in
something by participation is caused in it by that to which it belongs
essentially, and that things diversified by diverse participation of *esse*,
as more or less perfect, are caused by a first being. It does not say that
being exceeded in an arbitrary perfection is having it by participation; that
step is this premise's, not the source's (relation
`REL-AQUINAS-ST-I-Q44-A1-SUPPORTS-EXCEEDED-PERFECTION-IS-CAUSED`). The cause is
not required to have `r`, to be more `r`, or to be the exceeding `y`. -/
def ExceededPerfectionIsCausedReading {Being : Sort u} {Respect : Sort v}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ r x y, InAct x r → MoreIn r y x → ∃ c, c ≠ x ∧ CausesIn c x r

end TruthCore.Latin.Aquinas.SummaTheologiae
