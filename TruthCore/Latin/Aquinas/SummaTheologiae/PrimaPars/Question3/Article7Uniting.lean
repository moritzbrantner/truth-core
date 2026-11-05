import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia

/-!
Typed premises of the third proof of ST I q.3 a.7 co. (*omne compositum causam
habet*) and of ST I q.11 a.1 co. on the being of a composite, used to derive the
existing `CompositeHasAUnitingCauseReading` (result
COMPOSITE-UNITING-CAUSE-FROM-UNION).

Vocabulary reused, all of it parameters:

* `Composite x` and `ComponentOf a x` of q.3 a.7 (`Question3.Article7`): `a` is
  one of the things `x` is composed of (a part, its matter or form, its essence
  or esse).
* `EfficientlyCausesIn c x r` of the *secunda via* (`Question2.Article3SecundaVia`).
* `CausesIn c x r` of the *quarta via*; `CausesIn c x esse` is "c causes the
  being of x".

New vocabulary, a parameter:

* `Unites c a b x` — `c` is a cause uniting the diverse things `a` and `b` into
  the one thing `x` (*causa adunans ipsa*). It is not identified with efficient
  causing or with causing being; each passage from uniting to either is a
  separate premise below.

Source witnesses: SCTA diplomatic TEI of the Leonine edition, `scta-texts/TAca84`,
passages `AQUINAS-ST-I-Q3-A7` and `AQUINAS-ST-I-Q11-A1`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting

universe u v

/-- A composite has at least two numerically distinct components (*quod autem
est compositum, non habet esse quandiu partes eius sunt divisae, sed postquam
constituunt et componunt ipsum compositum*).

Read from q.11 a.1 co.: a composite has parts that can be divided from one
another and that compose it, so it has two distinct components. This is stronger
than the q.3 a.7 fifth-proof reading `CompositeHasComponentOtherThanItselfReading`,
which gives only one component other than the composite.

Source: Thomas Aquinas, *Summa theologiae* I q.11 a.1 co.
-/
def CompositeHasTwoDistinctComponentsReading {Being : Sort u}
    (Composite : Being → Prop) (ComponentOf : Being → Being → Prop) : Prop :=
  ∀ x, Composite x → ∃ a b, ComponentOf a x ∧ ComponentOf b x ∧ a ≠ b

/-- Things diverse in themselves come together into one only through a cause
uniting them (*quae enim secundum se diversa sunt, non conveniunt in aliquod
unum, nisi per aliquam causam adunantem ipsa*).

Read as: for any two distinct components `a`, `b` of `x`, something unites `a`
and `b` into `x`. *Diversa* is read as numerical distinctness, the weakest sense,
because the proof concludes of every composite, including the homogeneous wholes
of the fifth proof, whose parts differ only in number. The uniter is not required
here to be distinct from `x`, to be an efficient cause, or to cause `x`'s being.

Source: Thomas Aquinas, *Summa theologiae* I q.3 a.7 co., third proof.
-/
def DiverseUnitedOnlyThroughUnitingCauseReading {Being : Sort u}
    (ComponentOf : Being → Being → Prop)
    (Unites : Being → Being → Being → Being → Prop) : Prop :=
  ∀ x a b, ComponentOf a x → ComponentOf b x → a ≠ b → ∃ c, Unites c a b x

/-- A uniting cause is an efficient cause of what it unites, in some respect.

Unattributed open premise. It is motivated by, but not stated in, ST I q.3 a.7
co., third proof (*Deus autem non habet causam ... cum sit prima causa
efficiens*): that sentence excludes a uniting cause of God because he is the
first efficient cause, but does not say that every uniting cause is efficient.
Only "in some respect" is asserted, the weakest form that the *secunda via*'s
exclusion of self-causation can use.
-/
def UnitingCauseIsEfficientCauseReading {Being : Sort u} {Respect : Sort v}
    (Unites : Being → Being → Being → Being → Prop)
    (EfficientlyCausesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ c a b x, Unites c a b x → ∃ r, EfficientlyCausesIn c x r

/-- A cause uniting the components of a composite causes the composite's being.

Unattributed open premise. ST I q.11 a.1 co. (*non habet esse quandiu partes eius
sunt divisae, sed postquam constituunt et componunt ipsum compositum*) makes
union a necessary condition of the composite's being; it does not say that what
brings about the union is an effective cause (`CausesIn`) of its esse. This
bridge supplies that further step.
-/
def UnitingCauseCausesBeingReading {Being : Sort u} {Respect : Sort v}
    (Unites : Being → Being → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∀ c a b x, Unites c a b x → CausesIn c x esse

end TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting
