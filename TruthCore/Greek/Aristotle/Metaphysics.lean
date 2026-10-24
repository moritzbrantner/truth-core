/-!
Source-derived claims from Aristotle's *Metaphysics*.
-/

namespace TruthCore.Greek.Aristotle.Metaphysics

universe u v w

/--
Formal-object reading of Aristotle, *Metaphysics* IV.1, 1003a21-26: there is an
inquiry that studies being qua being and studies what belongs to that formal object in
its own right.

`being` is deliberately a supplied formal object rather than a predicate whose extension
is fixed by this declaration. Thus this reading does not decide whether Aristotle's
"being" is a univocal genus, a focal notion, or something else. Likewise,
`BelongsInOwnRight` records the passage's *kath' hauto* relation without identifying it
with necessity, essence, or a modern modal notion.

Source: Aristotle, *Metaphysics* IV.1, 1003a21-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg025`.
-/
def BeingQuaBeingInquiryFormalObjectReading
    {Inquiry : Type u}
    {Subject : Type v}
    {Attribute : Type w}
    (StudiesBeingQuaBeing : Inquiry → Subject → Prop)
    (BelongsInOwnRight : Subject → Attribute → Prop)
    (StudiesAttribute : Inquiry → Attribute → Prop)
    (being : Subject) : Prop :=
  ∃ inquiry,
    StudiesBeingQuaBeing inquiry being ∧
      ∀ property, BelongsInOwnRight being property → StudiesAttribute inquiry property

/--
Distributive-scope reading of Aristotle, *Metaphysics* IV.1, 1003a21-26: one inquiry
studies every being under the respect in which it is, along with the attributes that
belong to each such being in its own right.

The immediately following contrast says that the particular sciences do not examine
being "universally" (*katholou*) qua being. This makes a quantificational scope reading
defensible, but it is kept separate from
`BeingQuaBeingInquiryFormalObjectReading`: the Greek need not require that the scope of
a science be represented by enumeration over entities. `StudiesEntityQuaBeing` expresses
scope only; it does not claim exhaustive possession of knowledge about each entity.

As in the formal-object reading, `BelongsInOwnRightTo` leaves *kath' hauto* uninterpreted
as a relation; no necessity, essence, or causal dependence is added.

Source: Aristotle, *Metaphysics* IV.1, 1003a21-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg025`.
-/
def BeingQuaBeingInquiryDistributiveReading
    {Inquiry : Type u}
    {Entity : Type v}
    {Attribute : Type w}
    (IsBeing : Entity → Prop)
    (StudiesEntityQuaBeing : Inquiry → Entity → Prop)
    (BelongsInOwnRightTo : Entity → Attribute → Prop)
    (StudiesAttribute : Inquiry → Attribute → Prop) : Prop :=
  ∃ inquiry,
    (∀ entity, IsBeing entity → StudiesEntityQuaBeing inquiry entity) ∧
      ∀ entity property,
        IsBeing entity →
          BelongsInOwnRightTo entity property →
            StudiesAttribute inquiry property

/--
Cause-is-most-such reading of Aristotle, *Metaphysics* II.1, 993b24-27: each
thing is most such, compared with the others, when the synonymous quality belongs
to the others in virtue of it (fire is hottest, being the cause of heat to the
others), so that what is the cause of the posterior things' being true is most
true.

Read per quality: whatever causes the quality `r` in another thing is more `r`
than that thing. `CausesIn y x r` says that `y` is the cause of `x`'s being `r`;
`MoreIn r y x` says that `y` is more `r` than `x`. The quality is the same on both
sides (*synonymous*); the reading supplies no step from causing one quality to
being more in another. Read for `r = being` it says that a cause of another's
being is more a being than it (993b28-31: the principles of the eternal beings
are cause of being to the others, and as each thing stands to being, so to
truth).

Source: Aristotle, *Metaphysics* II.1, 993b24-31 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg025`.
-/
def CauseOfQualityInAnotherIsMoreSuchReading
    {Entity : Sort u}
    {Respect : Sort v}
    (CausesIn : Entity → Entity → Respect → Prop)
    (MoreIn : Respect → Entity → Entity → Prop) : Prop :=
  ∀ y x r, y ≠ x → CausesIn y x r → MoreIn r y x

end TruthCore.Greek.Aristotle.Metaphysics
