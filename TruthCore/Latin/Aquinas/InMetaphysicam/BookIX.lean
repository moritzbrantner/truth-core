/-!
Source-derived readings from Thomas Aquinas, *Sententia libri Metaphysicae*
IX, lect. 9 n. 1–7, on *Metaphysics* Θ.8, 1050b6-19: act is prior to potency
in substance "more properly", by comparing incorruptible (sempiternal) beings
with corruptible ones.

**Vocabulary.** Beings and respects are those of the *prima via* readings
(`TruthCore.Latin.Aquinas.SummaTheologiae.MotionModel`); `esse` is the respect
of being, that is, of substance. The argument adds two primitives:

* `CanFailToBe x r` — `x` can fail to be `r` (*contingit non esse*). Aquinas
  calls such a thing corruptible in `r`: simply (*simpliciter*) when `r` is
  substance, in a respect (*secundum quid*) when `r` is a place, quantity or
  quality (lect. 9 n. 4). It is a primitive; nothing defines it from act or
  potency, and no modal semantics is encoded.
* `PriorInSubstance y x` — `y` is prior to `x` in substance and perfection
  (*prius substantia et perfectione*, lect. 9 n. 1). It is a primitive,
  distinct from simple priority (`SummaTheologiae.ActSimplyPriorToPotencyReading`)
  and from priority in time; no reading here identifies them.

Source witness: Corpus Thomisticum Latin page, pinned as web snapshot passage
`AQUINAS-IN-METAPH-IX-L7-L9`.
-/

namespace TruthCore.Latin.Aquinas.InMetaphysicam

universe u v

/-- `x` is incorruptible simply (*incorruptibile simpliciter*): it cannot fail
to be in substance, the respect `esse`. Lect. 9 n. 4–5 (*simpliciter est
corruptibile, quod potest non esse secundum substantiam*). Aquinas' "sempiternal"
beings in lect. 9 n. 1 and n. 6 are read as these. -/
def IncorruptibleSimply {Being : Sort u} {Respect : Sort v}
    (CanFailToBe : Being → Respect → Prop) (esse : Respect) (x : Being) : Prop :=
  ¬ CanFailToBe x esse

/-- Every potency is a potency of the contradictory: whatever is in potency in a
respect can fail to be so, and is in that respect corruptible (*Relinquitur
ergo, quod omne quod est in potentia, inquantum huiusmodi, corruptibile est*).

Aquinas says it of passive potency (*loquitur hic de potentia passiva*, n. 2),
the potency the case's `InPotency` names, and lets the corruptibility be simple
or in a respect according to the respect of the potency (n. 4: a body that can
fail to be in a place is corruptible in place). Read per respect: potency in
`r` gives the ability to fail to be `r`, not to fail to be in substance.

Source: Aquinas, *In Metaph.* IX, lect. 9 n. 2–4; Aristotle, *Met.* Θ.8,
1050b8-15. -/
def PotencyIsOfContradictionReading {Being : Sort u} {Respect : Sort v}
    (InPotency CanFailToBe : Being → Respect → Prop) : Prop :=
  ∀ x r, InPotency x r → CanFailToBe x r

/-- Incorruptible beings are prior in substance to corruptible ones (*sempiterna
sunt priora corruptibilibus substantia et perfectione: hoc enim manifestum
est*).

Read over every pair: each simply incorruptible being is prior in substance to
each simply corruptible one. It does not say that any incorruptible being
exists, and its priority is priority in substance, not simple priority.

Source: Aquinas, *In Metaph.* IX, lect. 9 n. 1; Aristotle, *Met.* Θ.8,
1050b6-7. -/
def IncorruptiblePriorInSubstanceReading {Being : Sort u} {Respect : Sort v}
    (CanFailToBe : Being → Respect → Prop) (esse : Respect)
    (PriorInSubstance : Being → Being → Prop) : Prop :=
  ∀ e p, IncorruptibleSimply CanFailToBe esse e → CanFailToBe p esse →
    PriorInSubstance e p

/-- Incorruptible beings, as such, are in act (*Patet ergo ex praedictis, quod
omnia sempiterna, inquantum huiusmodi, sunt in actu*).

Read as act in substance: a simply incorruptible being is in act in the respect
`esse`. The same sentence's context denies more: *nihil prohibet, id quod est
incorruptibile simpliciter, esse in potentia secundum quid, aut secundum quale,
aut ubi* (the sun in the east is in potency to be in the west). So the reading
does not say that an incorruptible being is in act in every respect.

Source: Aquinas, *In Metaph.* IX, lect. 9 n. 5–6; Aristotle, *Met.* Θ.8,
1050b16-18. -/
def IncorruptibleIsInActReading {Being : Sort u} {Respect : Sort v}
    (InAct CanFailToBe : Being → Respect → Prop) (esse : Respect) : Prop :=
  ∀ e, IncorruptibleSimply CanFailToBe esse e → InAct e esse

end TruthCore.Latin.Aquinas.InMetaphysicam
