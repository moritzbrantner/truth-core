import TruthCore.Alternatives.ActPotencyRegress

/-!
The inertia bridge (#497): is a body's perseverance in uniform rectilinear
motion a *being moved* (`MovedIn`, a reduction from potency to act) in the
case vocabulary's sense? The inertial rival
`TruthCore.Alternatives.ActPotencyRegress.UniformMotionWithoutMoverReading`
and the root premise `ReducedOnlyByAMoverReading` disagree only through this
question (DISAMB-UNIFORM-MOTION-STATE-OR-BECOMING).

New vocabulary, all of it parameters:

* `Perseveres x r` — body `x` perseveres in its state `r` (Newton's
  *perseverare in statu suo*), that is, it is in that state and does not change
  it. Only states of uniform rectilinear motion (`UniformLocalMotion r`) are
  used here.
* `PerseveresBy y x r` — `y` is a being by which `x` perseveres in `r` (Newton's
  *qua corpus ... perseverat*). Not identified with `MovesIn`; the passage
  between them is the open bridge `MoverOfPerseveringBodyAccountsForPerseveranceReading`
  (DISAMB-PERSEVERANCE-SOURCE-AND-MOVER).

A Newtonian reading, a sourced Aquinas reading, two contrary readings of the
bridge (Garrigou-Lagrange's own, and the mechanist one he reports) and two
unattributed open premises. The bundle of the inertial objection is
`TruthCore.Comparison.Inertia.InertialObjection`.
-/

namespace TruthCore.Alternatives.Inertia

universe u v

/-- Newton, *Principia*, Def. III-IV: the inherent force (*vis insita*, *vis
inertiae*) is the power by which each body, as far as in it lies, perseveres in
its state of rest or of uniform rectilinear motion; the impressed force consists
in the action alone and does not remain in the body after the action, "for the
body perseveres in every new state by the force of inertia alone" (*per solam
vim inertiae*).

Read, for states of uniform motion, as: whatever being a body perseveres in that
state by is the body itself. The *vis insita* is the body's own power and not a
further being, so "by inertia alone" leaves the body as the only being by which
it perseveres. Weaker than Def. III-IV in one way: rest is left out. It says
nothing about whether the perseverance is a being moved.

Source: Newton, *Philosophiae naturalis principia mathematica* (1687),
Definitiones, Def. III and its explanation, Def. IV and its explanation.
-/
def PerseveranceByInherentForceAloneReading {Being : Sort u} {Respect : Sort v}
    (UniformLocalMotion : Respect → Prop)
    (Perseveres : Being → Respect → Prop)
    (PerseveresBy : Being → Being → Respect → Prop) : Prop :=
  ∀ x r y, UniformLocalMotion r → Perseveres x r → PerseveresBy y x r → y = x

/-- Unattributed open premise: some body perseveres in a state of uniform
rectilinear motion.

Newton's examples (projectiles, a top, planets "in less resisting spaces")
are bodies on which resistance and gravity act; Lex I and Def. III state
conditionals and assert no such body. Garrigou-Lagrange, citing Poincaré, holds
that no experiment has been made on bodies withdrawn from every force (*Dieu*,
1914, pp. 254, 759-760). -/
def SomeBodyPerseveresInUniformMotionReading {Being : Sort u} {Respect : Sort v}
    (UniformLocalMotion : Respect → Prop)
    (Perseveres : Being → Respect → Prop) : Prop :=
  ∃ x r, UniformLocalMotion r ∧ Perseveres x r

/-- The becoming reading of the bridge: a body persevering in uniform
rectilinear motion is being moved in that respect, a passage from potency to
act. Garrigou-Lagrange's own thesis: "local motion is no more a state than the
other motions; it is a becoming", since there is no less change from one
position to the next during the motion than from rest to motion.

Source: Garrigou-Lagrange, *Dieu, son existence et sa nature* (1914), I, ch. III,
n. 36 B, pp. 252, 254.
-/
def UniformPerseveranceIsBeingMovedReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (UniformLocalMotion : Respect → Prop)
    (Perseveres : Being → Respect → Prop) : Prop :=
  ∀ x r, UniformLocalMotion r → Perseveres x r → MovedIn x r

/-- The state reading of the bridge: a body persevering in uniform rectilinear
motion is not thereby being moved in that respect; it acquires nothing and does
not pass from potency to act. The Cartesian mechanist view as Garrigou-Lagrange
reports it (he rejects it): "by local motion a body would acquire nothing; it
would not pass from potency to act; it would only change position", so a mobile
needs an actual mover only to pass from rest to the state of motion.

Source: Garrigou-Lagrange, *Dieu, son existence et sa nature* (1914), I, ch. III,
n. 36 B, p. 250 (report, not endorsement).
-/
def UniformPerseveranceIsNotBeingMovedReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (UniformLocalMotion : Respect → Prop)
    (Perseveres : Being → Respect → Prop) : Prop :=
  ∀ x r, UniformLocalMotion r → Perseveres x r → ¬ MovedIn x r

/-- Unattributed open bridge: whatever moves a body that perseveres in uniform
motion, in that respect, is a being by which the body perseveres in it.

It identifies the case's mover (`MovesIn`, per se and simultaneous) with what
Newton's definitions account for perseverance by. Garrigou-Lagrange denies it:
a local motion cannot continue as a passage from potency to act without the
invisible motion of Pure Act, on which physics cannot pronounce (*Dieu*, 1914,
pp. 760-761, with Duhem's letter, pp. 761-763). -/
def MoverOfPerseveringBodyAccountsForPerseveranceReading
    {Being : Sort u} {Respect : Sort v}
    (MovesIn : Being → Being → Respect → Prop)
    (UniformLocalMotion : Respect → Prop)
    (Perseveres : Being → Respect → Prop)
    (PerseveresBy : Being → Being → Respect → Prop) : Prop :=
  ∀ y x r, UniformLocalMotion r → Perseveres x r → MovesIn y x r → PerseveresBy y x r

/-- Aquinas, following Aristotle, on projectiles: a thrown body that continues
in local motion after contact with the thrower has ceased is being moved, and
by another, not by itself: by the medium (air or water), to which the thrower
gave the power to move, mover after mover, until the power fails.

`ProjectedIn x r` says that `x` continues in the local motion `r` after being
thrown. Read only for projectiles in a medium; it says nothing about motion in a
void or about Newton's uniform motion.

Source: Thomas Aquinas, *In octo libros Physicorum* VIII, lect. 22, nn. 1160,
1162-1163 (Conway translation).
-/
def ProjectileMovedByAnotherReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (ProjectedIn : Being → Respect → Prop) : Prop :=
  ∀ x r, ProjectedIn x r → MovedIn x r ∧ ∃ y, y ≠ x ∧ MovesIn y x r

end TruthCore.Alternatives.Inertia
