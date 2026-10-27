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

Source witnesses: Perseus Greek *Metaphysics* (passage `ARIST-MET-XII-7`) and
the Corpus Thomisticum Latin page, pinned as web snapshot passage
`AQUINAS-IN-METAPH-XII-L7`.
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
respects of change to the case's abstract `Respect`. -/
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
otherwise", so it does not tie the two for one subject in one respect. -/
def CanFailToBeIsCanBeOtherwiseBridge {Being : Sort u} {Respect : Sort v}
    (CanFailToBe CanBeOtherwise : Being → Respect → Prop) : Prop :=
  ∀ x r, CanFailToBe x r → CanBeOtherwise x r

end TruthCore.Latin.Aquinas.InMetaphysicam
