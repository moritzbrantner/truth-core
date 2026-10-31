/-!
Source-derived readings from Aristotle, *Metaphysics* Λ.7, 1072a21-b13, and
Thomas Aquinas, *Sententia libri Metaphysicae* XII, lect. 7 n. 11–14: the
unmoved mover cannot be otherwise in any way (#352).

The sentence read here contrasts the first heaven with its mover. What is moved
can be otherwise: the first heaven, moved in circular locomotion, can be
otherwise in place, though not in substance (1072b4-7; lect. 7 n. 12). But the
mover that moves while itself unmoved, being in act, cannot be otherwise in any
way (τοῦτο οὐκ ἐνδέχεται ἄλλως ἔχειν οὐδαμῶς, 1072b7-8; *nullo modo possit
aliter et aliter se habere*, lect. 7 n. 13). This is the case that *In Metaph.*
IX, lect. 9 n. 6 leaves open for a simply incorruptible moved body: a potency
in place without a potency in substance.

**Vocabulary.** Beings and respects are those of the *prima via* readings
(`TruthCore.Latin.Aquinas.SummaTheologiae.MotionModel`); `esse` is the respect
of being, as in `BookIX`. `MovesIn y x r` and `MovedIn x r` are the prima via's
moving and being moved, in the broad sense of `DISAMB-MOTION` (educing from
potency to act). The readings add one primitive:

* `CanBeOtherwise x r` — `x` can be otherwise in respect `r` (ἐνδέχεται ἄλλως
  ἔχειν; *aliter et aliter se habere*). Aquinas counts the respects as
  substance, quantity, quality and place (lect. 7 n. 12). It is a primitive,
  distinct from `CanFailToBe` of `BookIX`; the two are related only by the
  explicit, unattributed bridge `CanFailToBeIsCanBeOtherwiseBridge`.
* `OfChange r` — `r` is a respect of change: substance, quantity, quality or
  place, the respects in which Aquinas says a moved thing is otherwise and
  otherwise (lect. 7 n. 12). Λ.7's "in no way" (οὐδαμῶς, *nullo modo*) is read
  over these respects only, because both authors give as its reason that the
  mover is not moved (1072b8-10; *quia non potest moveri*, n. 13). Carrying it
  to every respect of the case's abstract `Respect` (any perfection) is the
  separate unattributed bridge
  `UnchangeableInRespectsOfChangeIsUnchangeableSimplyBridge`.

The readings sit in the Aquinas commentary namespace, as `BookIX` does for
*Met.* Θ.8, because each Aristotle reading is paired with Aquinas' reading of
the same lines and both bind the same Lean declaration.

Source witnesses: Perseus Greek *Metaphysics* (passages `ARIST-MET-XII-7`, and
`ARIST-MET-V-5` and `ARIST-MET-XII-9` for context) and the Corpus Thomisticum
Latin pages, pinned as web snapshot passages `AQUINAS-IN-METAPH-XII-L7`,
`AQUINAS-IN-METAPH-XII-L11` and `AQUINAS-IN-METAPH-V-L6`.
-/

namespace TruthCore.Latin.Aquinas.InMetaphysicam

universe u v

/-- There is a mover that moves something, is moved in no respect of change, is
in act in being, and cannot be otherwise in any respect of change (ἐπεὶ δὲ ἔστι
τι κινοῦν αὐτὸ ἀκίνητον ὄν, ἐνεργείᾳ ὄν, τοῦτο οὐκ ἐνδέχεται ἄλλως ἔχειν
οὐδαμῶς).

Read as the sentence asserts it: existentially, of the mover whose existence
1072a21-26 has just argued (ἔστι τι ὃ οὐ κινούμενον κινεῖ). ἀκίνητον is read
with that participle as "not being moved", not as the modal "cannot be moved";
ἐνεργείᾳ ὄν as being in act in the respect of being; "in no way" as every
respect of change (`OfChange`). It does not say that the mover is unmoved or
fixed in a respect that is not one of change, that every unmoved mover cannot
be otherwise (sibling `EveryUnmovedMoverCannotBeOtherwiseReading`), or that the
mover is unique.

Source: Aristotle, *Met.* Λ.7, 1072b4-10 (with 1072a25-26); Aquinas, *In Metaph.*
XII, lect. 7 n. 12–13 (*primum movens, quod est immobile et semper actu ens,
nullo modo possit aliter et aliter se habere, quia non potest moveri*). -/
def SomeUnmovedMoverCannotBeOtherwiseReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop) (esse : Respect) (OfChange : Respect → Prop)
    (CanBeOtherwise : Being → Respect → Prop) : Prop :=
  ∃ m, (∃ x r, MovesIn m x r) ∧ (∀ r, OfChange r → ¬ MovedIn m r) ∧
    InAct m esse ∧ ∀ r, OfChange r → ¬ CanBeOtherwise m r

/-- Every mover that moves something, is moved in no respect of change and is in
act in being cannot be otherwise in any respect of change.

The generic sibling reading of the same sentence: the μέν/δέ contrast with the
general conditional just before it (εἰ μὲν οὖν τι κινεῖται, ἐνδέχεται καὶ
ἄλλως ἔχειν, 1072b4-5) can be read as stating what holds of whatever moves
while unmoved and in act. The sentence's own reason (circular locomotion is the
first change, and this mover causes it, 1072b8-10) is about the mover of the
first heaven, so the universal scope is a reading choice, not the plain sense.
Respects of change only, as in the existential reading.

Source: Aristotle, *Met.* Λ.7, 1072b4-10. -/
def EveryUnmovedMoverCannotBeOtherwiseReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop) (esse : Respect) (OfChange : Respect → Prop)
    (CanBeOtherwise : Being → Respect → Prop) : Prop :=
  ∀ m, (∃ x r, MovesIn m x r) → (∀ r, OfChange r → ¬ MovedIn m r) →
    InAct m esse → ∀ r, OfChange r → ¬ CanBeOtherwise m r

/-- Open bridge, unattributed: a mover that is moved in no respect of change and
cannot be otherwise in any respect of change is moved in no respect and cannot
be otherwise in any respect.

It says that such a mover has no respect, outside substance, quantity, quality
and place, in which it is moved or could be otherwise (for example in
understanding or willing). Λ.7 and lect. 7 do not say this: their "in no way" is
argued from the mover's not being moved. It carries the readings from the
respects of change to the case's abstract `Respect`.

Partial support only: *In Metaph.* XII, lect. 11 n. 8 (on Λ.9, 1074b25-27) denies
the first mover a change in what it understands
(`FirstMoverCannotChangeWhatItUnderstandsReading`), one respect that is not one
of change, of a mover it presupposes moved in no respect at all. No text read
for #352 says that such a mover cannot be otherwise in every further respect,
in particular in willing. *In Metaph.* V, lect. 6 n. 14 says that the first
necessary is necessary in every way and not otherwise and otherwise, but no text
read identifies the first necessary with this mover (lect. 7 n. 13–15 refers
the necessity of Λ.7, 1072b10-13 to the first motion). -/
def UnchangeableInRespectsOfChangeIsUnchangeableSimplyBridge {Being : Sort u}
    {Respect : Sort v} (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) (OfChange : Respect → Prop)
    (CanBeOtherwise : Being → Respect → Prop) : Prop :=
  ∀ m, (∃ x r, MovesIn m x r) → (∀ r, OfChange r → ¬ MovedIn m r) →
    (∀ r, OfChange r → ¬ CanBeOtherwise m r) →
    ∀ r, ¬ MovedIn m r ∧ ¬ CanBeOtherwise m r

/-- Open bridge, unattributed: whatever can fail to be `r` can be otherwise in
respect `r`.

It holds when `CanFailToBe` is read in the two-way sense of the potency of the
contradictory (*possibile esse et non esse*, *In Metaph.* IX, lect. 9 n. 2):
what can be `r` and can fail to be `r` can, whichever it is, be the other way.
It fails if "can fail to be `r`" is read as the bare possibility of not being
`r`, which an unchangeable being that is not `r` also has
(`DISAMB-CAN-FAIL-TO-BE-OR-BE-OTHERWISE`). No source read for #352 states it:
*In Metaph.* XII, lect. 7 n. 13 infers (*unde sequitur*) from the mover's not
being able to be otherwise that the first motion, a different subject, cannot
not be, and n. 15 denies that this necessity is the absolute "cannot be
otherwise", so it does not tie the two for one subject in one respect. *Met.*
Δ.5, 1015a33-35 only defines the necessary as what cannot be otherwise, and
1015b11-13 argues the converse direction.

Partial support only: `WhatCanBeInMoreWaysCanBeOtherwiseReading` has the same
consequent predicate but speaks of what can be in more ways and names no respect.
Two steps stay unattributed: that the two-way potency to `r` is an ability to be
in more ways, and that the respect of being otherwise is `r`. -/
def CanFailToBeIsCanBeOtherwiseBridge {Being : Sort u} {Respect : Sort v}
    (CanFailToBe CanBeOtherwise : Being → Respect → Prop) : Prop :=
  ∀ x r, CanFailToBe x r → CanBeOtherwise x r

/-- Whatever can be in more ways can be otherwise in some respect.

Read from Aquinas: *quae autem pluribus modis habere se possunt, possunt se
habere aliter et aliter* (what can be in more ways can be otherwise and
otherwise). `CanBeInMoreWays` is a parameter for *pluribus modis se habere posse*.
The sentence names no respect, so the reading says only that there is one. It
does not mention the potency of the contradictory, and it does not state
`CanFailToBeIsCanBeOtherwiseBridge`.

Source: Aquinas, *In Metaph.* V, lect. 6 n. 14. -/
def WhatCanBeInMoreWaysCanBeOtherwiseReading {Being : Sort u} {Respect : Sort v}
    (CanBeInMoreWays : Being → Prop)
    (CanBeOtherwise : Being → Respect → Prop) : Prop :=
  ∀ x, CanBeInMoreWays x → ∃ s, CanBeOtherwise x s

/-- Some mover that moves something and is moved in no respect cannot be
otherwise in the respect `understood` of what it understands: it cannot pass
from one object of understanding to another.

Aquinas on Λ.9, 1074b25-27: the first intellect does not change from one
object of understanding to another, both because the change would be to
something less worthy and because passing from one object to another is a kind
of motion (*quidam motus*), which cannot belong to the first mover, since it is
altogether unmovable (*cum sit omnino immobile*). Read existentially, of the
first mover whose existence is presupposed, as the Λ.7 readings are. "Moved in
no respect" is entailed by *omnino immobile*; the modal *immobile* (cannot be
moved) is not kept. "Cannot pass from one object to another" is read as cannot
be otherwise in the respect `understood`.

For this mover it says "moved in no respect" of every respect, willing
included, but "cannot be otherwise" only of `understood`, which the reading
glosses as a respect that is not one of change (substance, quantity, quality,
place); the type does not encode that gloss. It does not say that the mover
cannot be otherwise in further respects such as willing, and it is existential,
so it does not state `UnchangeableInRespectsOfChangeIsUnchangeableSimplyBridge`;
it supports that bridge's `MovedIn` half and, for `understood` only, its
`CanBeOtherwise` half.

Source: Aquinas, *In Metaph.* XII, lect. 11 n. 8; Aristotle, *Met.* Λ.9,
1074b25-27 (*the most divine thing thinks ... and does not change; for change
would be for the worse, and such a thing would already be a motion*), for
context. -/
def FirstMoverCannotChangeWhatItUnderstandsReading {Being : Sort u}
    {Respect : Sort v} (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (CanBeOtherwise : Being → Respect → Prop) (understood : Respect) : Prop :=
  ∃ m, (∃ x r, MovesIn m x r) ∧ (∀ r, ¬ MovedIn m r) ∧
    ¬ CanBeOtherwise m understood

end TruthCore.Latin.Aquinas.InMetaphysicam
