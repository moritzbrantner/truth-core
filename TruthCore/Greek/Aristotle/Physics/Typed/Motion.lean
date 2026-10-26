import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3

/-!
Typed readings of Aristotle, *Physics* III.3, VII.1 and VIII.4-5, on motion, mover
and moved, in the act/potency vocabulary the case already uses (#401, item 1).

The older readings of these chapters (`TruthCore.Greek.Aristotle.Physics`, the
`BookIII`/`BookVII` modules) take `Prop` atoms, so they cannot imply anything and
nothing can imply them. The readings below state the same passages over shared
predicates, so that they can be derived, used and refuted. The older readings stay
as they are; each new reading is recorded as a sibling claim of the older one
(`interpretation_of`), not as the same statement.

**Shared vocabulary**, the parameters of
`TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading` and its
neighbours (`MotionModel`, `ActPotencyModel`):

* `Being`, `Respect`: beings, and that in respect of which a being is moved
  (`DEF-RESPECT`). For these Aristotelian readings a respect is the terminus of one
  kind of κίνησις: a place, a quality or a quantity.
* `MovedIn x r`: `x` is being moved in respect `r`; `MovesIn y x r`: `y` moves `x`
  in respect `r`, in its own right (καθʼ αὑτό). In these readings motion is
  Aristotle's physical change (`DEF-MOTION-AS-PHYSICAL-CHANGE`); `DISAMB-MOTION`
  says why that is one kind of the reduction from potency to act that the
  *prima via* reads with the same predicates.
* `InPotency`, `InAct`, `MovesAsMoved` as in the *prima via*.

**Added vocabulary**, only what these chapters need and the case lacks. All of it
is primitive, never defined:

* `ByNature x r`, `ByForce x r`: `x` is moved in `r` by nature, or by force and
  contrary to nature (φύσει, βίᾳ καὶ παρὰ φύσιν; *Physics* VIII.4, 254b12-24).
* `SelfMovedIn x r`: `x` is moved in `r` by itself (ὑφʼ αὑτοῦ), as an animal is;
  Aristotle analyses this as one part moving and another moved (254b27-33).
  This is **not** `MovesIn x x r`: see `DISAMB-SELF-MOTION`.
* `PassiveNaturalIn x r`: `x` is moved in `r` by nature but not by itself, having
  in itself a principle of being acted on, not of acting, as the light and the
  heavy are (255b29-31).
* `MovesPerAccidensIn y x r`: `y` moves `x` in `r` only per accidens
  (κατὰ συμβεβηκός), as the one who takes away a hindrance does (255b24-27).
* `IsLocal r`: `r` is a respect of local, bodily motion (κατὰ τόπον καὶ σωματικὴν
  κίνησιν; VII.1, 242a15-16, 242b24-25).
* `MovesPrimarily y x`: `y` is a primary (proximate) mover of `x`, the
  `τὸ κινοῦν πρώτως` of VII.1, 242b24 and the adjacent mover of 242a17-19.
* `Touches y x`: `y` touches or is continuous with `x` (ἅπτεσθαι ἢ συνεχὲς εἶναι).
* `ComposedOf u c`: `u` is one thing made of all the members of the chain `c`
  (εἶναί τι ἐξ ἁπάντων ἕν, 242b26).
* `TraversesInfiniteInFiniteTime u`: `u` goes through an infinite motion in a
  finite time (242b30-243a1).

Source: Aristotle, *Physics* III.3, VII.1, VIII.4, VIII.5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/

namespace TruthCore.Greek.Aristotle.Physics.Typed

universe u v

/-! ## *Physics* III.3: motion is in the moved -/

/-- Motion is in the movable, for it is the actuality of the movable, brought about
by what can move it (*Physics* III.3, 202a13-14: ἐστὶν ἡ κίνησις ἐν τῷ κινητῷ·
ἐντελέχεια γάρ ἐστι τούτου καὶ ὑπὸ τοῦ κινητικοῦ).

Weakest typed reading: whenever `y` moves `x` in `r`, `x` is being moved in `r`.
The moving is not a second motion in the mover but the moved thing's being moved
(202a15-16: the mover's actuality "is not another"). The reading adds no claim
about the mover's own motion, and it says nothing about motions as objects; the
older reading `MotionLocatedInMovableReading` keeps that occurrence-level form.

Source: Aristotle, *Physics* III.3, 202a13-16 (Bekker pagination).
-/
def MovingIsInTheMovedReading {Being : Sort u} {Respect : Sort v}
    (MovesIn : Being → Being → Respect → Prop)
    (MovedIn : Being → Respect → Prop) : Prop :=
  ∀ y x r, MovesIn y x r → MovedIn x r

/-- No mover moves itself in the respect in which it moves: whatever moves something
in a respect is distinct from what it moves.

A consequence, not a source reading: it is derived in result
`ARIST-PHYS-III-1-3-NO-MOVER-MOVES-ITSELF` from *Physics* III.1's analysis of
being moved, III.3's location of motion in the moved, and the *prima via*'s
premises that a mover is in act and that nothing is in act and in potency in the
same respect. It is stronger than
`TruthCore.Latin.Aquinas.SummaTheologiae.NothingMovesItselfInSameRespectReading`,
which assumes that the self-mover is being moved in that respect. -/
def NoMoverMovesItselfInItsRespectReading {Being : Sort u} {Respect : Sort v}
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ y x r, MovesIn y x r → y ≠ x

/-! ## *Physics* VIII.4: everything moved is moved by something -/

/-- Every motion is either by nature or by force and contrary to nature
(*Physics* VIII.4, 255b31: εἰ δὴ πάντα τὰ κινούμενα ἢ φύσει κινεῖται ἢ παρὰ φύσιν
καὶ βίᾳ), the division set out at 254b12-24.

Source: Aristotle, *Physics* VIII.4, 254b12-24, 255b31 (Bekker pagination).
-/
def EveryMotionNaturalOrForcedReading {Being : Sort u} {Respect : Sort v}
    (MovedIn ByNature ByForce : Being → Respect → Prop) : Prop :=
  ∀ x r, MovedIn x r → ByNature x r ∨ ByForce x r

/-- Of natural motions, some are motions of things moved by themselves and the rest
of things not moved by themselves, as the light and the heavy (*Physics* VIII.4,
255b32-33: τῶν δὲ φύσει πάλιν τά θʼ ὑφʼ αὑτῶν κινούμενα … καὶ τὰ μὴ ὑφʼ αὑτῶν, οἷον
τὰ κοῦφα καὶ τὰ βαρέα).

The second kind is stated positively, as natural motion from a principle of being
acted on (255b29-31), so that the division is the text's and not an instance of
excluded middle.

Source: Aristotle, *Physics* VIII.4, 255b29-33 (Bekker pagination).
-/
def NaturalMotionSelfOrPassiveReading {Being : Sort u} {Respect : Sort v}
    (ByNature SelfMovedIn PassiveNaturalIn : Being → Respect → Prop) : Prop :=
  ∀ x r, ByNature x r → SelfMovedIn x r ∨ PassiveNaturalIn x r

/-- Whatever is moved by force and contrary to nature is moved by something, and by
another (*Physics* VIII.4, 255b31-32: τά τε βίᾳ καὶ παρὰ φύσιν πάντα ὑπό τινος καὶ
ὑπʼ ἄλλου; 254b24-27).

Source: Aristotle, *Physics* VIII.4, 254b24-27, 255b31-32 (Bekker pagination).
-/
def ForcedMotionByAnotherReading {Being : Sort u} {Respect : Sort v}
    (ByForce : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ x r, ByForce x r → ∃ y, y ≠ x ∧ MovesIn y x r

/-- Of natural motions, those of things moved by themselves are moved by something
(*Physics* VIII.4, 255b32-33; 254b27-33: "it is not unclear whether it is moved by
something, but how one must distinguish in it the mover and the moved").

"By something" may be the thing itself: Aristotle's self-mover is moved by itself,
a part moving another part. The reading says only that the motion has a mover in
that respect.

Source: Aristotle, *Physics* VIII.4, 254b27-33, 255b32-33 (Bekker pagination).
-/
def NaturalSelfMotionByAMoverReading {Being : Sort u} {Respect : Sort v}
    (ByNature SelfMovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ x r, ByNature x r → SelfMovedIn x r → ∃ y, MovesIn y x r

/-- The natural motions of things not moved by themselves, as of the light and the
heavy, are moved either by what generated them and made them light or heavy, or by
what removed the hindrance (*Physics* VIII.4, 255b35-256a2: ἢ γὰρ ὑπὸ τοῦ
γεννήσαντος καὶ ποιήσαντος κοῦφον ἢ βαρύ, ἢ ὑπὸ τοῦ τὰ ἐμποδίζοντα καὶ κωλύοντα
λύσαντος).

Literal reading: the remover of a hindrance moves only per accidens (255b24-27:
κατὰ συμβεβηκὸς γὰρ κινεῖ), so the mover is either a per se mover (the generator)
or a per accidens one.

Source: Aristotle, *Physics* VIII.4, 255b24-27, 255b35-256a2 (Bekker pagination).
-/
def PassiveNaturalMotionByGeneratorOrRemoverReading {Being : Sort u} {Respect : Sort v}
    (PassiveNaturalIn : Being → Respect → Prop)
    (MovesIn MovesPerAccidensIn : Being → Being → Respect → Prop) : Prop :=
  ∀ x r, PassiveNaturalIn x r → ∃ y, MovesIn y x r ∨ MovesPerAccidensIn y x r

/-- Sibling reading of the same sentence: the natural motion of a thing not moved by
itself, as of the light and the heavy, is moved per se by what generated it and
made it light or heavy.

This is stronger than the literal disjunction. Its ground is that VIII.4 itself
says fire and earth are moved by something also when they move by nature to their
own actualities (255a28-30), and calls the remover of a hindrance a mover only per
accidens (255b24-27); of the two movers 256a1-2 names, only the generator is left
as a per se mover. Whether the generator still *moves* the light thing while it
rises is the reading's open commitment.

Source: Aristotle, *Physics* VIII.4, 255a28-30, 255b24-27, 255b35-256a2 (Bekker
pagination).
-/
def PassiveNaturalMotionByGeneratorReading {Being : Sort u} {Respect : Sort v}
    (PassiveNaturalIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ x r, PassiveNaturalIn x r → ∃ y, MovesIn y x r

/-- All things that are moved would be moved by something (*Physics* VIII.4,
256a2-3: ἅπαντα ἂν τὰ κινούμενα ὑπό τινος κινοῖτο), with "by something" covering
the per accidens mover that the literal reading of 255b35-256a2 admits.

Source: Aristotle, *Physics* VIII.4, 256a2-3 (Bekker pagination).
-/
def EveryMovedThingMovedPerSeOrPerAccidensReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn MovesPerAccidensIn : Being → Being → Respect → Prop) : Prop :=
  ∀ x r, MovedIn x r → ∃ y, MovesIn y x r ∨ MovesPerAccidensIn y x r

/-! ## *Physics* VII.1: the regress of local moved movers -/

/-- A link of VII.1's regress: `y` is another thing than `x`, a primary mover of
`x`, moves `x` in local motion, and is itself being moved in local motion
(242a15-19: "if something is moved in local motion by another that is moved, and
the mover in turn by another moved thing, and so always").

Vocabulary, not a reading. -/
def LocalMovedMoverLink {Being : Sort u} {Respect : Sort v}
    (IsLocal : Respect → Prop)
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (MovesPrimarily : Being → Being → Prop) (y x : Being) : Prop :=
  y ≠ x ∧ MovesPrimarily y x ∧ (∃ r, IsLocal r ∧ MovesIn y x r) ∧
    ∃ r, IsLocal r ∧ MovedIn y r

/-- What primarily moves something in local, bodily motion touches it or is
continuous with it (*Physics* VII.1, 242b24-26: εἰ τὸ κινοῦν πρώτως κατὰ τόπον καὶ
σωματικὴν κίνησιν ἀνάγκη ἢ ἅπτεσθαι ἢ συνεχὲς εἶναι τῷ κινουμένῳ, καθάπερ ὁρῶμεν ἐπὶ
πάντων).

The contact condition is Aristotle's repair of the failed first reductio. It is
kept as its own premise and restricted to primary movers in local motion, as the
sentence restricts it.

Source: Aristotle, *Physics* VII.1, 242b24-26 (Bekker pagination).
-/
def PrimaryLocalMoverTouchesReading {Being : Sort u} {Respect : Sort v}
    (IsLocal : Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (MovesPrimarily Touches : Being → Being → Prop) : Prop :=
  ∀ y x r, IsLocal r → MovesPrimarily y x → MovesIn y x r → Touches y x

/-- If each member of a chain touches or is continuous with the next, some one thing
is made of them all (*Physics* VII.1, 242b26: ἀνάγκη τὰ κινούμενα καὶ τὰ κινοῦντα
συνεχῆ εἶναι ἢ ἅπτεσθαι ἀλλήλων, ὥστʼ εἶναί τι ἐξ ἁπάντων ἕν).

Source: Aristotle, *Physics* VII.1, 242b25-26 (Bekker pagination).
-/
def TouchingChainFormsOneReading {Being : Sort u}
    (Touches : Being → Being → Prop)
    (ComposedOf : Being → (Nat → Being) → Prop) : Prop :=
  ∀ c : Nat → Being, (∀ n, Touches (c (n + 1)) (c n)) → ∃ w, ComposedOf w c

/-- The one thing made of an infinite chain of local moved movers, whether it is
finite or infinite, would go through an infinite motion in the finite time of the
first moved thing's motion (*Physics* VII.1, 242b27-243a1).

This premise carries the chapter's aggregate argument: the members move together
(242a20-30), each motion is one and finite (242a30-242b11), the aggregate of
infinitely many equal or greater motions is infinite, and what is possible may be
taken as actual (242b11-16, 242b29-30, 243a1-2). It is stated only for chains of
`LocalMovedMoverLink`s.

Source: Aristotle, *Physics* VII.1, 242a20-243a2 (Bekker pagination).
-/
def OneOfInfiniteLocalChainTraversesInfiniteReading {Being : Sort u} {Respect : Sort v}
    (IsLocal : Respect → Prop)
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (MovesPrimarily : Being → Being → Prop)
    (ComposedOf : Being → (Nat → Being) → Prop)
    (TraversesInfiniteInFiniteTime : Being → Prop) : Prop :=
  ∀ (c : Nat → Being) (w : Being),
    (∀ n, LocalMovedMoverLink IsLocal MovedIn MovesIn MovesPrimarily (c (n + 1)) (c n)) →
      ComposedOf w c → TraversesInfiniteInFiniteTime w

/-- Nothing, finite or infinite, goes through an infinite motion in a finite time
(*Physics* VII.1, 242b30-243a1: ἀμφοτέρως δὲ ἀδύνατον, relying on VI.7).

Source: Aristotle, *Physics* VII.1, 242b30-243a1 (Bekker pagination).
-/
def NoInfiniteTraversalInFiniteTimeReading {Being : Sort u}
    (TraversesInfiniteInFiniteTime : Being → Prop) : Prop :=
  ∀ w, ¬ TraversesInfiniteInFiniteTime w

/-- The series of local moved movers stops: there is no infinite chain in which each
member is moved in local motion by the next, a primary mover of it that is itself
moved in local motion (*Physics* VII.1, 242a15-20 and 242b30-243a2: ἀνάγκη ἵστασθαι
καὶ εἶναί τι πρῶτον κινοῦν καὶ κινούμενον).

Restricted as audit B (#388) found the source restricts it: to local, bodily motion
and to primary movers that are themselves moved. It is weaker than
`TruthCore.Latin.Aquinas.SummaTheologiae.NoInfinitePerSeMoverSeriesReading`
(result `ARIST-PHYS-VII-1-REGRESS-FROM-PER-SE-REGRESS`). It speaks of chains
indexed by `Nat`, so it denies an infinite descending chain; it does not assert
well-foundedness, which without choice is stronger.

Source: Aristotle, *Physics* VII.1, 242a15-20, 242b23-243a2 (Bekker pagination).
-/
def NoInfiniteLocalMovedMoverChainReading {Being : Sort u} {Respect : Sort v}
    (IsLocal : Respect → Prop)
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (MovesPrimarily : Being → Being → Prop) : Prop :=
  ¬ ∃ c : Nat → Being,
    ∀ n, LocalMovedMoverLink IsLocal MovedIn MovesIn MovesPrimarily (c (n + 1)) (c n)

/-! ## *Physics* VIII.5: a first mover not moved by another -/

/-- `y` is moved by another: some other thing moves it in some respect.
Vocabulary, not a reading. -/
def MovedByAnother {Being : Sort u} {Respect : Sort v}
    (MovesIn : Being → Being → Respect → Prop) (y : Being) : Prop :=
  ∃ z r, z ≠ y ∧ MovesIn z y r

/-- A link of VIII.5's series: `y` is another thing than `x`, moves `x` in some
respect, and is itself moved by another (τὸ κινοῦν καὶ κινούμενον ὑπʼ ἄλλου).
Vocabulary, not a reading. -/
def MoverMovedByAnotherLink {Being : Sort u} {Respect : Sort v}
    (MovesIn : Being → Being → Respect → Prop) (y x : Being) : Prop :=
  y ≠ x ∧ (∃ r, MovesIn y x r) ∧ MovedByAnother MovesIn y

/-- Everything that is moved is moved by something (*Physics* VIII.5, 256a13-14:
εἰ δὴ ἀνάγκη πᾶν τὸ κινούμενον ὑπό τινός τε κινεῖσθαι; the conclusion of VIII.4
and the opening thesis of VII.1, 241b24).

Respect-free reading: some mover moves the moved thing in some respect. It does not
say that the mover moves it in the respect in which it is moved, which
`TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading` says, and it
does not say "by another".

Source: Aristotle, *Physics* VII.1, 241b24; VIII.5, 256a13-14 (Bekker pagination).
-/
def EveryMovedThingHasSomeMoverReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ x r, MovedIn x r → ∃ y r', MovesIn y x r'

/-- A mover that is moved by another cannot go on to infinity, for among infinitely
many there is no first (*Physics* VIII.5, 256a17-19: ἀδύνατον γὰρ εἰς ἄπειρον ἰέναι
τὸ κινοῦν καὶ κινούμενον ὑπʼ ἄλλου αὐτό· τῶν γὰρ ἀπείρων οὐκ ἔστιν οὐδὲν πρῶτον).

Formalized as well-foundedness of `MoverMovedByAnotherLink`, as the *prima via*'s
regress is formalized. Unlike that premise it is not restricted to per se links:
it covers every mover moved by another.

Source: Aristotle, *Physics* VIII.5, 256a17-19 (Bekker pagination).
-/
def NoInfiniteSeriesOfMoversMovedByAnotherReading {Being : Sort u} {Respect : Sort v}
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ x, Acc (MoverMovedByAnotherLink MovesIn) x

/-- There must be a mover that is not moved by another (*Physics* VIII.5,
256a13-17: ἀνάγκη τι εἶναι κινοῦν ὃ οὐχ ὑπʼ ἄλλου πρῶτον).

Stated as the reductio, like the *prima via*'s conclusion, so that it is axiom-free.
It is weaker than that conclusion: the first mover may be moved by itself, as
Aristotle goes on to say (256a19-21), where the *prima via*'s first mover is moved
by none.

Source: Aristotle, *Physics* VIII.5, 256a13-21 (Bekker pagination).
-/
def FirstMoverNotMovedByAnotherCannotBeLackingReading {Being : Sort u} {Respect : Sort v}
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ¬ ¬ ∃ f, (∃ x r, MovesIn f x r) ∧ ¬ MovedByAnother MovesIn f

end TruthCore.Greek.Aristotle.Physics.Typed
