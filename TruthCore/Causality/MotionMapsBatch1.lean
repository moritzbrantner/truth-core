module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question105.Article5
public import TruthCore.Greek.Aristotle.Physics
public import TruthCore.Logic.CogitoSubject

/-! Motion maps, batch 1: second movers, created agents, grades from the cogito

Analyst formulations (attribution deferred) for three exploration maps:
`explorations/second-movers-as-moved.toml`,
`explorations/created-agent-applied.toml` and
`explorations/grades-found-in-things.toml`. Every definition below is an OPEN
premise; the vocabulary of the existing statements is reused unchanged
(`MovedIn`, `MovesIn`, `MovesAsMoved`, `RelevantTo` of the *prima via*;
`CausesIn`, `esse`, `God` of q.105 a.5; `InPotency`, `ActualizedQuaPotential`
of *Physics* III.1; `Occurs`, `Bears` of the cogito; `MoreIn` of the *quarta
via*).

New primitives:
* `ByOwnForm y x`: y moves x by the power of its own form, as a principal agent
  does (q.18 a.3 co.: *agens principale est quod per suam formam agit*); a mover
  that does not is an instrument (*instrumentum, quod non agit ex virtute suae
  formae, sed ex virtute principalis agentis*). `DEF-MOVES-BY-OWN-FORM`.
* `OperationOf y x r o`: y's moving x in respect r is an operation of y in its
  own respect o. `DEF-OPERATION-RESPECT`.
* `Lives x`: x lives, i.e. operates from itself (q.18 a.3). `DEF-LIVING`.
* `Actual z`: z is an actual thing; `Actual z ∧ ¬ Lives z` is merely existing
  (SCG I.28 [1]). `DEF-MERELY-EXISTING`.
-/

@[expose] public section

namespace TruthCore.Causality.MotionMapsBatch1

universe u v w

/-! ### Map 1: second movers move only as moved -/

/-- A mover other than what it moves that is being moved in a respect relevant
to its moving does not move by the power of its own form: it is an instrument.
Restricted to the relevant respect; weaker than "whatever moves and is moved
moves as an instrument" (`STMT-WHATEVER-MOVES-AND-IS-MOVED-MOVES-AS-INSTRUMENT`,
SCG I.13 [15]), which is not formalized. -/
def MovedMoverIsInstrument {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
    (RelevantTo : Being → Being → Respect → Respect → Prop)
    (ByOwnForm : Being → Being → Prop) : Prop :=
  ∀ y x r r', y ≠ x → MovesIn y x r → MovedIn y r' → RelevantTo y x r r' →
    ¬ ByOwnForm y x

/-- An instrument acts not by the power of its own form but by the power of the
principal agent (q.18 a.3 co.), so a mover that does not move by its own form
moves only insofar as it is moved: it is a per se link (`MovesAsMoved`). -/
def InstrumentMovesByPrincipalPower {Being : Sort u} {Respect : Sort v}
    (MovesIn : Being → Being → Respect → Prop) (ByOwnForm : Being → Being → Prop)
    (MovesAsMoved : Being → Being → Prop) : Prop :=
  ∀ y x r, MovesIn y x r → ¬ ByOwnForm y x → MovesAsMoved y x

/-- Scope bridge from the weak to the strong per se reading: a mover other than
what it moves that is being moved in some respect is being moved in some respect
relevant to that moving. This is exactly the contested strengthening. -/
def RelevantRespectCoversEveryMovedMover {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
    (RelevantTo : Being → Being → Respect → Respect → Prop) : Prop :=
  ∀ y x r, y ≠ x → MovesIn y x r → (∃ r', MovedIn y r') →
    ∃ r', MovedIn y r' ∧ RelevantTo y x r r'

/-! ### Map 2: every created agent is moved when it moves -/

/-- Whenever an agent other than God whose being God causes moves something, its
acting actualizes a potency of its own as such: it has some respect in which it
is in potency and that potency is being actualized. -/
def CreatureActingIsNewActuality {Being : Sort u} {Respect : Sort v}
    (MovesIn : Being → Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) (God : Being → Prop)
    (InPotency ActualizedQuaPotential : Being → Respect → Prop) : Prop :=
  ∀ g y, God g → y ≠ g → CausesIn g y esse → ∀ x r, MovesIn y x r →
    ∃ r', InPotency y r' ∧ ActualizedQuaPotential y r'

/-- A creature is not its own operation: whenever an agent other than God whose
being God causes moves something, that moving is an operation of the agent in
some respect in which the agent is in potency. -/
def CreatureInPotencyToItsOperation {Being : Sort u} {Respect : Sort v}
    (MovesIn : Being → Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) (God : Being → Prop)
    (OperationOf : Being → Being → Respect → Respect → Prop)
    (InPotency : Being → Respect → Prop) : Prop :=
  ∀ g y, God g → y ≠ g → CausesIn g y esse → ∀ x r, MovesIn y x r →
    ∃ o, OperationOf y x r o ∧ InPotency y o

/-- Acting actualizes the agent's potency to that operation as such. Contested:
*Physics* III.3 places motion in the moved, not in the mover qua mover. -/
def ActingActualizesOperationPotency {Being : Sort u} {Respect : Sort v}
    (MovesIn : Being → Being → Respect → Prop)
    (OperationOf : Being → Being → Respect → Respect → Prop)
    (ActualizedQuaPotential : Being → Respect → Prop) : Prop :=
  ∀ y x r o, MovesIn y x r → OperationOf y x r o → ActualizedQuaPotential y o

/-! ### Map 3: grades found in things, from the cogito -/

/-- Whatever bears an occurring thought lives: thinking is an operation that
remains in the agent (q.18 a.3 co.: *actio quae manet in agente, ut
intelligere*), and to live is to operate from oneself. -/
def ThinkerLives {Episode : Sort u} {Being : Sort v}
    (Occurs : Episode → Prop) (Bears : Being → Episode → Prop)
    (Lives : Being → Prop) : Prop :=
  ∀ s e, Occurs e → Bears s e → Lives s

/-- Some actual thing exists without living (a stone). -/
def SomethingMerelyExists {Being : Sort u} (Actual Lives : Being → Prop) : Prop :=
  ∃ z, Actual z ∧ ¬ Lives z

/-- What lives is more noble than any actual thing that merely exists
(SCG I.28 [1]: living things are more perfect than merely existing ones). -/
def LivingMoreNobleThanMerelyExisting {Being : Sort u} {Respect : Sort v}
    (MoreIn : Respect → Being → Being → Prop) (nobile : Respect)
    (Actual Lives : Being → Prop) : Prop :=
  ∀ x z, Lives x → Actual z → ¬ Lives z → MoreIn nobile x z

/-- Grades of nobility are grades of goodness and truth: if one thing is more
noble than another, it is also more good and more true (the convertibility of
the transcendentals, read for the comparative). -/
def NobilityGradeConvertible {Being : Sort u} {Respect : Sort v}
    (MoreIn : Respect → Being → Being → Prop) (bonum verum nobile : Respect) : Prop :=
  ∀ x y, MoreIn nobile x y → MoreIn bonum x y ∧ MoreIn verum x y

/-! ### Controls

Finite interpretations, not claims about real movers, creatures or stones. -/

namespace Control
open TruthCore.Latin.Aquinas.SummaTheologiae
  (SecondMoversMoveOnlyAsMovedReading SecondMoversMoveAsMovedInRelevantRespectReading
    CreatedAgentIsAppliedToActByGodReading GradesFoundInThingsReading)
open TruthCore.Greek.Aristotle.Physics (BeingMovedIsActualizationOfPotencyReading)
open TruthCore.Logic.CogitoSubject (ThoughtOccurs EveryThoughtHasSubject)

/-! Map 1: a stick `true` moves a stone `false` in the one respect while being moved in
it, and that being moved is relevant to its moving. -/

abbrev movedIn1 : Bool → Unit → Prop := fun y _ => y = true
abbrev movesIn1 : Bool → Bool → Unit → Prop := fun y x _ => y = true ∧ x = false
abbrev relevant1 : Bool → Bool → Unit → Unit → Prop := fun y x _ _ => y = true ∧ x = false
abbrev noRelevant : Bool → Bool → Unit → Unit → Prop := fun _ _ _ _ => False
abbrev ownForm1 : Bool → Bool → Prop := fun y x => y = true ∧ x = false
abbrev noOwnForm : Bool → Bool → Prop := fun _ _ => False
abbrev noMovesAsMoved : Bool → Bool → Prop := fun _ _ => False

/-- Omitting the instrument premise: the stick moves by its own form, and is no
per se link. -/
def OmitInstrument : Prop :=
  ¬ MovedMoverIsInstrument movedIn1 movesIn1 relevant1 ownForm1 ∧
  InstrumentMovesByPrincipalPower movesIn1 ownForm1 noMovesAsMoved ∧
  ¬ SecondMoversMoveAsMovedInRelevantRespectReading movedIn1 movesIn1 noMovesAsMoved relevant1

/-- Omitting the principal-power premise: the stick is an instrument and still
no per se link. -/
def OmitPrincipal : Prop :=
  MovedMoverIsInstrument movedIn1 movesIn1 relevant1 noOwnForm ∧
  ¬ InstrumentMovesByPrincipalPower movesIn1 noOwnForm noMovesAsMoved ∧
  ¬ SecondMoversMoveAsMovedInRelevantRespectReading movedIn1 movesIn1 noMovesAsMoved relevant1

/-- Omitting the weak reading: the scope bridge alone gives no per se link. -/
def OmitWeak : Prop :=
  ¬ SecondMoversMoveAsMovedInRelevantRespectReading movedIn1 movesIn1 noMovesAsMoved relevant1 ∧
  RelevantRespectCoversEveryMovedMover movedIn1 movesIn1 relevant1 ∧
  ¬ SecondMoversMoveOnlyAsMovedReading movedIn1 movesIn1 noMovesAsMoved

/-- Omitting the scope bridge: the stick is moved only in an irrelevant respect,
the weak reading holds vacuously and the strong one fails. -/
def OmitScope : Prop :=
  SecondMoversMoveAsMovedInRelevantRespectReading movedIn1 movesIn1 noMovesAsMoved noRelevant ∧
  ¬ RelevantRespectCoversEveryMovedMover movedIn1 movesIn1 noRelevant ∧
  ¬ SecondMoversMoveOnlyAsMovedReading movedIn1 movesIn1 noMovesAsMoved

/-! Map 2: God `true` causes the esse of creature `false`, which moves `true`. -/

abbrev god2 : Bool → Prop := fun g => g = true
abbrev causes2 : Bool → Bool → Unit → Prop := fun g y _ => g = true ∧ y = false
abbrev moves2 : Bool → Bool → Unit → Prop := fun y x _ => y = false ∧ x = true
abbrev none2 : Bool → Unit → Prop := fun _ _ => False
abbrev creature2 : Bool → Unit → Prop := fun y _ => y = false
abbrev noOperation : Bool → Bool → Unit → Unit → Prop := fun _ _ _ _ => False
abbrev operation2 : Bool → Bool → Unit → Unit → Prop := fun y _ _ _ => y = false

/-- Omitting the new-actuality premise: the creature moves with no potency
actualized, and is not moved. -/
def OmitNew : Prop :=
  ¬ CreatureActingIsNewActuality moves2 causes2 () god2 none2 none2 ∧
  BeingMovedIsActualizationOfPotencyReading none2 none2 none2 ∧
  ¬ CreatedAgentIsAppliedToActByGodReading none2 moves2 causes2 () god2

/-- Omitting *Physics* III.1: the creature's potency is actualized as such, but
nothing counts as being moved. -/
def OmitMotion : Prop :=
  CreatureActingIsNewActuality moves2 causes2 () god2 creature2 creature2 ∧
  ¬ BeingMovedIsActualizationOfPotencyReading none2 creature2 creature2 ∧
  ¬ CreatedAgentIsAppliedToActByGodReading none2 moves2 causes2 () god2

/-- Omitting the operation-potency premise: the creature's moving is no operation
in potency, and no actuality is new. -/
def OmitPotency : Prop :=
  ¬ CreatureInPotencyToItsOperation moves2 causes2 () god2 noOperation none2 ∧
  ActingActualizesOperationPotency moves2 noOperation none2 ∧
  ¬ CreatureActingIsNewActuality moves2 causes2 () god2 none2 none2

/-- Omitting the acting premise: the creature is in potency to its operation,
but acting does not actualize that potency (the Aristotelian reply that motion
is in the moved). -/
def OmitActing : Prop :=
  CreatureInPotencyToItsOperation moves2 causes2 () god2 operation2 creature2 ∧
  ¬ ActingActualizesOperationPotency moves2 operation2 none2 ∧
  ¬ CreatureActingIsNewActuality moves2 causes2 () god2 creature2 none2

/-! Map 3: one thought episode; a thinker `true` and a stone `false`. -/

abbrev occurs3 : Unit → Prop := fun _ => True
abbrev noOccurs : Unit → Prop := fun _ => False
abbrev bears3 : Bool → Unit → Prop := fun s _ => s = true
abbrev noBears : Bool → Unit → Prop := fun _ _ => False
abbrev lives3 : Bool → Prop := fun x => x = true
abbrev noLives : Bool → Prop := fun _ => False
abbrev actual3 : Bool → Prop := fun x => x = false
abbrev allActual : Bool → Prop := fun _ => True
abbrev allLive : Bool → Prop := fun _ => True
abbrev more3 : Unit → Bool → Bool → Prop := fun _ x y => x = true ∧ y = false
abbrev noMore : Unit → Bool → Bool → Prop := fun _ _ _ => False
/-- Two respects: `true` is nobility, `false` goodness and truth. -/
abbrev nobleOnly : Bool → Bool → Bool → Prop := fun r x y => r = true ∧ x = true ∧ y = false

/-- Nonvacuity: the thinker lives, the stone merely exists, the thinker is more
noble, good and true; all six premises and the conclusion hold. -/
def GradesWitness : Prop :=
  ThoughtOccurs occurs3 ∧ EveryThoughtHasSubject occurs3 bears3 ∧
  ThinkerLives occurs3 bears3 lives3 ∧ SomethingMerelyExists actual3 lives3 ∧
  LivingMoreNobleThanMerelyExisting more3 () actual3 lives3 ∧
  NobilityGradeConvertible more3 () () () ∧ GradesFoundInThingsReading more3 () () ()

/-- Omitting the occurrence premise: no thought occurs and no grades. -/
def OmitOccurs : Prop :=
  ¬ ThoughtOccurs noOccurs ∧ EveryThoughtHasSubject noOccurs noBears ∧
  ThinkerLives noOccurs noBears noLives ∧ SomethingMerelyExists allActual noLives ∧
  LivingMoreNobleThanMerelyExisting noMore () allActual noLives ∧
  NobilityGradeConvertible noMore () () () ∧ ¬ GradesFoundInThingsReading noMore () () ()

/-- Omitting the bearer principle: a thought occurs with no bearer. -/
def OmitSubject : Prop :=
  ThoughtOccurs occurs3 ∧ ¬ EveryThoughtHasSubject occurs3 noBears ∧
  ThinkerLives occurs3 noBears noLives ∧ SomethingMerelyExists allActual noLives ∧
  LivingMoreNobleThanMerelyExisting noMore () allActual noLives ∧
  NobilityGradeConvertible noMore () () () ∧ ¬ GradesFoundInThingsReading noMore () () ()

/-- Omitting that the thinker lives: the bearer of the thought does not live. -/
def OmitLives : Prop :=
  ThoughtOccurs occurs3 ∧ EveryThoughtHasSubject occurs3 bears3 ∧
  ¬ ThinkerLives occurs3 bears3 noLives ∧ SomethingMerelyExists allActual noLives ∧
  LivingMoreNobleThanMerelyExisting noMore () allActual noLives ∧
  NobilityGradeConvertible noMore () () () ∧ ¬ GradesFoundInThingsReading noMore () () ()

/-- Omitting the stone: everything lives, nothing merely exists. -/
def OmitStone : Prop :=
  ThoughtOccurs occurs3 ∧ EveryThoughtHasSubject occurs3 bears3 ∧
  ThinkerLives occurs3 bears3 allLive ∧ ¬ SomethingMerelyExists allActual allLive ∧
  LivingMoreNobleThanMerelyExisting noMore () allActual allLive ∧
  NobilityGradeConvertible noMore () () () ∧ ¬ GradesFoundInThingsReading noMore () () ()

/-- Omitting the nobility premise: thinker and stone, ungraded. -/
def OmitNoble : Prop :=
  ThoughtOccurs occurs3 ∧ EveryThoughtHasSubject occurs3 bears3 ∧
  ThinkerLives occurs3 bears3 lives3 ∧ SomethingMerelyExists actual3 lives3 ∧
  ¬ LivingMoreNobleThanMerelyExisting noMore () actual3 lives3 ∧
  NobilityGradeConvertible noMore () () () ∧ ¬ GradesFoundInThingsReading noMore () () ()

/-- Omitting convertibility: the thinker is more noble but not more good or
true. -/
def OmitConvert : Prop :=
  ThoughtOccurs occurs3 ∧ EveryThoughtHasSubject occurs3 bears3 ∧
  ThinkerLives occurs3 bears3 lives3 ∧ SomethingMerelyExists actual3 lives3 ∧
  LivingMoreNobleThanMerelyExisting nobleOnly true actual3 lives3 ∧
  ¬ NobilityGradeConvertible nobleOnly false false true ∧ ¬ GradesFoundInThingsReading nobleOnly false false true

/-- The batch controls: one nonvacuity witness and an omission model for every
premise of the five derivations (the composed route inherits them). -/
def Certificate : Prop :=
  GradesWitness ∧ OmitInstrument ∧ OmitPrincipal ∧ OmitWeak ∧ OmitScope ∧
  OmitNew ∧ OmitMotion ∧ OmitPotency ∧ OmitActing ∧
  OmitOccurs ∧ OmitSubject ∧ OmitLives ∧ OmitStone ∧ OmitNoble ∧ OmitConvert

end Control

end TruthCore.Causality.MotionMapsBatch1
