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
* `IsPhysicalRespect r`: `r` is a respect of physical motion in Aristotle's sense:
  a place, a quality or a quantity (*Physics* V.1-2). It marks the scope of the
  VIII.4 readings, so that they say nothing about other reductions from potency to
  act that the *prima via*'s broad reading of `MovedIn` may include
  (`DISAMB-MOTION`).
* `IsLocal r`: `r` is a respect of local, bodily motion (κατὰ τόπον καὶ σωματικὴν
  κίνησιν; VII.1, 242a15-16, 242b24-25).
* `MovesPrimarily y x`: `y` is a primary (proximate) mover of `x`, the
  `τὸ κινοῦν πρώτως` of VII.1, 242b24 and the adjacent mover of 242a17-19.
* `Touches y x`: `y` touches or is continuous with `x` (ἅπτεσθαι ἢ συνεχὲς εἶναι).
* `ComposedOf u c`: `u` is one thing made of all the members of the chain `c`
  (εἶναί τι ἐξ ἁπάντων ἕν, 242b26).
* `TraversesInfiniteInFiniteTime u`: `u` goes through an infinite motion in a
  finite time (242b30-243a1).

**Scope.** These are readings of Aristotle's physical motion. Only VIII.4's
division and its two conclusions carry an explicit guard (`IsPhysicalRespect`);
VIII.4's other readings are scoped by their antecedent primitives (`ByForce`,
`ByNature`, `SelfMovedIn`, `PassiveNaturalIn` are kinds of physical motion by their
definitions). The III.3 and VIII.5 readings carry no guard: they are accepted only
under a physical instantiation of `MovedIn`/`MovesIn`. The results that use them
with *prima via* premises derive only new statements, and a universal *prima via*
premise restricts to physical motion; no result carries a physical premise to a
statement about every reduction from potency to act except through the explicit,
unattributed scope premise `EveryReductionIsPhysicalMotionReading`
(`DISAMB-MOTION`).

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
Scope: physical motion, by instantiation (no guard).

Source: Aristotle, *Physics* III.3, 202a13-16 (Bekker pagination).
-/
def MovingIsInTheMovedReading {Being : Sort u} {Respect : Sort v}
    (MovesIn : Being → Being → Respect → Prop)
    (MovedIn : Being → Respect → Prop) : Prop :=
  ∀ y x r, MovesIn y x r → MovedIn x r

/-- No mover moves itself in the respect in which it moves: whatever moves something
in a respect is distinct from what it moves. Since every moving is in some respect,
this says that nothing moves itself in any respect; an Aristotelian self-mover
(`SelfMovedIn`) is a whole whose mover is a part (`DISAMB-SELF-MOTION`).

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

Scope: only physical motion (`IsPhysicalRespect`), the motion the *Physics*
treats. The reading says nothing about a reduction from potency to act in any
other respect.

Source: Aristotle, *Physics* VIII.4, 254b12-24, 255b31 (Bekker pagination).
-/
def EveryMotionNaturalOrForcedReading {Being : Sort u} {Respect : Sort v}
    (IsPhysicalRespect : Respect → Prop)
    (MovedIn ByNature ByForce : Being → Respect → Prop) : Prop :=
  ∀ x r, IsPhysicalRespect r → MovedIn x r → ByNature x r ∨ ByForce x r

/-- Of natural motions, some are motions of things moved by themselves and the rest
of things not moved by themselves, as the light and the heavy (*Physics* VIII.4,
255b32-33: τῶν δὲ φύσει πάλιν τά θʼ ὑφʼ αὑτῶν κινούμενα … καὶ τὰ μὴ ὑφʼ αὑτῶν, οἷον
τὰ κοῦφα καὶ τὰ βαρέα).

The second kind is stated positively, as natural motion from a principle of being
acted on. That is a reading step: 255b29-31 says this of the light and the heavy,
the text's example (οἷον), and the reading extends it to every natural motion that
is not a self-motion. It also keeps the division from being an instance of
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

Aristotle's self-mover is moved by itself, a part moving another part, so the
mover is the moving part. The Lean leaves open which being the mover is; with
`NoMoverMovesItselfInItsRespectReading` it must be other than the whole. The
reading says only that the motion has a per se mover in that respect.

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
or a per accidens one. Reading the generator as a per se mover of the motion in
its respect (the place) is itself a reading step; and the inclusive "or" admits a
motion whose only mover is the per accidens remover. Extended from the light and
the heavy to every `PassiveNaturalIn` motion, as in
`NaturalMotionSelfOrPassiveReading`.

Source: Aristotle, *Physics* VIII.4, 255b24-27, 255b35-256a2 (Bekker pagination).
-/
def PassiveNaturalMotionByGeneratorOrRemoverReading {Being : Sort u} {Respect : Sort v}
    (PassiveNaturalIn : Being → Respect → Prop)
    (MovesIn MovesPerAccidensIn : Being → Being → Respect → Prop) : Prop :=
  ∀ x r, PassiveNaturalIn x r → ∃ y, MovesIn y x r ∨ MovesPerAccidensIn y x r

/-- **Added premise, not a source reading.** If the natural motion of a thing not
moved by itself, as of the light and the heavy, has a per accidens mover (the
remover of a hindrance), it also has a per se mover in that respect.

Aristotle gives the disjunction "by the generator or by the remover"
(`PassiveNaturalMotionByGeneratorOrRemoverReading`). Its inclusive "or" admits a
motion whose only mover is the per accidens remover; this premise excludes that
case. It is what the disjunction lacks for a per se mover (result
`ARIST-PHYS-VIII-4-EVERY-MOVED-PER-SE-OR-PER-ACCIDENS`,
`literalReadingDoesNotGivePerSeMover`). It is open and has no source claim.
Bearing on it: VIII.4, 254b33-255a1 places the natural motion of the light and the
heavy among things moved by another, which suggests a per se mover in every case
but does not say so; Aquinas' commentary on VIII.4 is another place to look (not
pinned). -/
def PerAccidensMovedPassiveMotionHasPerSeMoverReading {Being : Sort u} {Respect : Sort v}
    (PassiveNaturalIn : Being → Respect → Prop)
    (MovesIn MovesPerAccidensIn : Being → Being → Respect → Prop) : Prop :=
  ∀ x r y, PassiveNaturalIn x r → MovesPerAccidensIn y x r → ∃ z, MovesIn z x r

/-- All things that are moved would be moved by something (*Physics* VIII.4,
256a2-3: ἅπαντα ἂν τὰ κινούμενα ὑπό τινος κινοῖτο), with "by something" covering
the per accidens mover that the literal reading of 255b35-256a2 admits.

Scope: physical motion only (`IsPhysicalRespect`).

Source: Aristotle, *Physics* VIII.4, 256a2-3 (Bekker pagination).
-/
def EveryMovedThingMovedPerSeOrPerAccidensReading {Being : Sort u} {Respect : Sort v}
    (IsPhysicalRespect : Respect → Prop)
    (MovedIn : Being → Respect → Prop)
    (MovesIn MovesPerAccidensIn : Being → Being → Respect → Prop) : Prop :=
  ∀ x r, IsPhysicalRespect r → MovedIn x r → ∃ y, MovesIn y x r ∨ MovesPerAccidensIn y x r

/-- Whatever is moved in a respect of physical motion has a per se mover in that
respect.

A consequence, not a source reading: result
`ARIST-PHYS-VIII-4-EVERY-PHYSICAL-MOTION-HAS-A-PER-SE-MOVER` derives it from the
VIII.4 readings and the added premise
`PerAccidensMovedPassiveMotionHasPerSeMoverReading`. It is the *prima via*'s
`ReducedOnlyByAMoverReading` restricted to physical motion. -/
def EveryPhysicalMotionHasAPerSeMoverReading {Being : Sort u} {Respect : Sort v}
    (IsPhysicalRespect : Respect → Prop)
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ x r, IsPhysicalRespect r → MovedIn x r → ∃ y, MovesIn y x r

/-- **Added premise, not a source reading.** Every respect in which something is
being moved, in the sense of `MovedIn` that the root premise
`TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading` uses, is a
respect of physical motion.

This is the scope extension that carries VIII.4's physical premises to the
*prima via*'s premise, which on the case's reading covers every reduction from
potency to act (`DISAMB-MOTION`). It is open and doubtful: Aquinas counts
reductions that are not physical motion (for example in understanding and
willing) under *moveri*, so on that reading this premise is false and the
VIII.4 route does not reach the root premise. -/
def EveryReductionIsPhysicalMotionReading {Being : Sort u} {Respect : Sort v}
    (IsPhysicalRespect : Respect → Prop)
    (MovedIn : Being → Respect → Prop) : Prop :=
  ∀ x r, MovedIn x r → IsPhysicalRespect r

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

Chains are injective (infinitely many distinct members: ἄπειρα τὰ κινοῦντα,
242b12), so a finite cycle is not such a chain. The sentence is said of the
hypothesised chain of movers; the reading generalizes it to every injective
touching chain.

Source: Aristotle, *Physics* VII.1, 242b25-26 (Bekker pagination).
-/
def TouchingChainFormsOneReading {Being : Sort u}
    (Touches : Being → Being → Prop)
    (ComposedOf : Being → (Nat → Being) → Prop) : Prop :=
  ∀ c : Nat → Being, Function.Injective c →
    (∀ n, Touches (c (n + 1)) (c n)) → ∃ w, ComposedOf w c

/-- The one thing made of an infinite chain of local moved movers, whether it is
finite or infinite, would go through an infinite motion in the finite time of the
first moved thing's motion (*Physics* VII.1, 242b27-243a1).

This premise carries the chapter's aggregate argument: the members move together
(242a20-30), each motion is one and finite (242a30-242b11), the aggregate of
infinitely many equal or greater motions is infinite, and what is possible may be
taken as actual (242b11-16, 242b29-30, 243a1-2). It is stated only for injective
chains of `LocalMovedMoverLink`s (ἀπείρων ὄντων, 242b29).

Source: Aristotle, *Physics* VII.1, 242a20-243a2 (Bekker pagination).
-/
def OneOfInfiniteLocalChainTraversesInfiniteReading {Being : Sort u} {Respect : Sort v}
    (IsLocal : Respect → Prop)
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (MovesPrimarily : Being → Being → Prop)
    (ComposedOf : Being → (Nat → Being) → Prop)
    (TraversesInfiniteInFiniteTime : Being → Prop) : Prop :=
  ∀ (c : Nat → Being) (w : Being), Function.Injective c →
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
indexed by `Nat` and injective, so it denies an infinite descending chain of
distinct members; it does not exclude a finite cycle of mutual movers, and it does
not assert well-foundedness, which is stronger.

Source: Aristotle, *Physics* VII.1, 242a15-20, 242b23-243a2 (Bekker pagination).
-/
def NoInfiniteLocalMovedMoverChainReading {Being : Sort u} {Respect : Sort v}
    (IsLocal : Respect → Prop)
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (MovesPrimarily : Being → Being → Prop) : Prop :=
  ¬ ∃ c : Nat → Being, Function.Injective c ∧
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
does not say "by another". It takes ὑπό τινος as a per se mover (`MovesIn`): a
stronger reading than VIII.4's literal conclusion, which admits a per accidens
mover, and not derived from it; and stronger than what VII.1's own proof secures
in the internal-source case (rest-dependence, 242a1-4). Scope: physical motion, by
instantiation (no guard).

Source: Aristotle, *Physics* VII.1, 241b24; VIII.5, 256a13-14 (Bekker pagination).
-/
def EveryMovedThingHasSomeMoverReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ x r, MovedIn x r → ∃ y r', MovesIn y x r'

/-- *Physics* VIII.5, 256a17-19 prohibits proceeding to infinity through movers
moved by another. This weak reading rules out a sequence of infinitely many
distinct movers linked by `MoverMovedByAnotherLink`. It does not exclude finite
cycles and does not assert accessibility or supply an induction principle.

The source-level prohibition is kept separate from the stronger, unattributed
`NoInfiniteSeriesOfMoversMovedByAnotherReading` consumed by the induction proof.
The broader reading of the links (all movers moved by another) is used here; a
restriction to the instrumental series of 256a4-13 remains a defensible alternative.
Scope: physical motion, by instantiation (no guard).

Source: Aristotle, *Physics* VIII.5, 256a17-19 (Bekker pagination).
-/
def NoInfiniteDistinctMoversMovedByAnotherReading {Being : Sort u} {Respect : Sort v}
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ¬ ∃ c : Nat → Being, Function.Injective c ∧
    ∀ n, MoverMovedByAnotherLink MovesIn (c (n + 1)) (c n)

/-- **Additional commitment, not an attributed source reading.** The relation
`MoverMovedByAnotherLink` is accessible at every being. The declaration's existing
name is retained to preserve statement and theorem identities.

This is stronger than the prohibition of infinitely many distinct movers read
from *Physics* VIII.5, 256a17-19 in
`NoInfiniteDistinctMoversMovedByAnotherReading`: it also excludes finite cycles
and supplies the induction principle used by `firstMoverNotMovedByAnother`.
No claim attributes this additional strength to Aristotle. The transfer result
`movedByAnotherRegressFromPerSeRegress` derives it conditionally from the
*prima via*'s accessibility premise, III.3 and the second-movers premise; that
does not establish it from VIII.5's source-level prohibition. Scope: physical
motion, by instantiation (no guard). -/
def NoInfiniteSeriesOfMoversMovedByAnotherReading {Being : Sort u} {Respect : Sort v}
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ x, Acc (MoverMovedByAnotherLink MovesIn) x

/-- There must be a mover that is not moved by another (*Physics* VIII.5,
256a13-17: ἀνάγκη τι εἶναι κινοῦν ὃ οὐχ ὑπʼ ἄλλου πρῶτον).

Stated as the reductio, like the *prima via*'s conclusion, so that it is axiom-free.
It is weaker than that conclusion: the first mover may be moved by itself, as
Aristotle goes on to say (256a19-21), where the *prima via*'s first mover is moved
by none. "First" (πρῶτον) is not formalized: the mover is not shown to head any
particular series.

Source: Aristotle, *Physics* VIII.5, 256a13-21 (Bekker pagination).
-/
def FirstMoverNotMovedByAnotherCannotBeLackingReading {Being : Sort u} {Respect : Sort v}
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ¬ ¬ ∃ f, (∃ x r, MovesIn f x r) ∧ ¬ MovedByAnother MovesIn f

end TruthCore.Greek.Aristotle.Physics.Typed
