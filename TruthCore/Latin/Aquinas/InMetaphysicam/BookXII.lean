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

Source witnesses: Perseus Greek *Metaphysics* (passage `ARIST-MET-XII-7`) and
the Corpus Thomisticum Latin page, pinned as web snapshot passage
`AQUINAS-IN-METAPH-XII-L7`.
-/

namespace TruthCore.Latin.Aquinas.InMetaphysicam

universe u v

/-- There is a mover that moves something, is moved in no respect, is in act in
being, and cannot be otherwise in any respect (ἐπεὶ δὲ ἔστι τι κινοῦν αὐτὸ
ἀκίνητον ὄν, ἐνεργείᾳ ὄν, τοῦτο οὐκ ἐνδέχεται ἄλλως ἔχειν οὐδαμῶς).

Read as the sentence asserts it: existentially, of the mover whose existence
1072a21-26 has just argued (ἔστι τι ὃ οὐ κινούμενον κινεῖ). ἀκίνητον is read
with that participle as "not being moved", that is, moved in no respect, not as
the modal "cannot be moved"; ἐνεργείᾳ ὄν as being in act in the respect of
being. It does not say that every unmoved mover cannot be otherwise (that is the
sibling reading `EveryUnmovedMoverCannotBeOtherwiseReading`), and it does not
say that the mover is unique.

Source: Aristotle, *Met.* Λ.7, 1072b7-8 (with 1072a25-26); Aquinas, *In Metaph.*
XII, lect. 7 n. 13 (*primum movens, quod est immobile et semper actu ens, nullo
modo possit aliter et aliter se habere, quia non potest moveri*). -/
def SomeUnmovedMoverCannotBeOtherwiseReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop) (esse : Respect)
    (CanBeOtherwise : Being → Respect → Prop) : Prop :=
  ∃ m, ((∃ x r, MovesIn m x r) ∧ ∀ r, ¬ MovedIn m r) ∧ InAct m esse ∧
    ∀ r, ¬ CanBeOtherwise m r

/-- Every mover that moves something, is moved in no respect and is in act in
being cannot be otherwise in any respect.

The generic sibling reading of the same sentence: the μέν/δέ contrast with the
general conditional just before it (εἰ μὲν οὖν τι κινεῖται, ἐνδέχεται καὶ
ἄλλως ἔχειν, 1072b4-5) can be read as stating what holds of whatever moves
while unmoved and in act. The sentence's own reason (circular locomotion is the
first change, and this mover causes it, 1072b8-10) is about the mover of the
first heaven, so the universal scope is a reading choice, not the plain sense.

Source: Aristotle, *Met.* Λ.7, 1072b4-8. -/
def EveryUnmovedMoverCannotBeOtherwiseReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop) (esse : Respect)
    (CanBeOtherwise : Being → Respect → Prop) : Prop :=
  ∀ m, ((∃ x r, MovesIn m x r) ∧ ∀ r, ¬ MovedIn m r) → InAct m esse →
    ∀ r, ¬ CanBeOtherwise m r

/-- Open bridge, unattributed: whatever can fail to be `r` can be otherwise in
respect `r`.

It holds when `CanFailToBe` is read in the two-way sense of the potency of the
contradictory (*possibile esse et non esse*, *In Metaph.* IX, lect. 9 n. 2):
what can be `r` and can fail to be `r` can, whichever it is, be the other way.
It fails if "can fail to be `r`" is read as the bare possibility of not being
`r`, which an unchangeable being that is not `r` also has
(`DISAMB-CAN-FAIL-TO-BE-OR-BE-OTHERWISE`). No source read for #352 states it:
*In Metaph.* XII, lect. 7 n. 13–15 glosses the necessary both as what cannot
not be and as what cannot be otherwise, but applies the first gloss to the
first motion, whose necessity n. 15 denies is of the second, absolute kind. -/
def CanFailToBeIsCanBeOtherwiseBridge {Being : Sort u} {Respect : Sort v}
    (CanFailToBe CanBeOtherwise : Being → Respect → Prop) : Prop :=
  ∀ x r, CanFailToBe x r → CanBeOtherwise x r

end TruthCore.Latin.Aquinas.InMetaphysicam
