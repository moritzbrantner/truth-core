/-!
Source-derived claims from Aristotle's *Physics*.
-/

namespace TruthCore.Greek.Aristotle.Physics

universe u v w

/--
An exhaustive-classification reading of Aristotle, *Physics* II.3, 194b16-195a3:
when something is a cause of an effect, that causal role falls under at least one of the
material, formal, source-of-change, or final modes.

The causal roles remain relation-valued parameters. This avoids treating Aristotle's four
causes as intrinsic unary labels on isolated objects and avoids imposing a universal ontology
of causation before later passages require one.

Source: Aristotle, *Physics* II.3, 194b16-195a3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FourCauseExhaustiveReading
    {Cause : Type u}
    {Effect : Type v}
    (IsCause : Cause → Effect → Prop)
    (Material : Cause → Effect → Prop)
    (Formal : Cause → Effect → Prop)
    (SourceOfChange : Cause → Effect → Prop)
    (Final : Cause → Effect → Prop) : Prop :=
  ∀ cause effect,
    IsCause cause effect →
      Material cause effect ∨
      Formal cause effect ∨
      SourceOfChange cause effect ∨
      Final cause effect

/--
Relation-preserving definitional reading of Aristotle, *Physics* III.1, 201a10-11:
an occurrence is change exactly when it is the actuality of some subject that exists
potentially, precisely qua potential.

`ExistsPotentially` and `IsActualityOfQuaPotential` remain supplied predicates. The
second preserves the passage's compound actuality/qua-potential relation without deciding
whether `entelecheia` should be further explained as a product-like actuality, a
process-like actualization, or a manifested potentiality. This reading adds no target state,
temporal interval, mover, completed outcome, or particular category of change.

The opening at 200b12-15 motivates the inquiry into change; the definition itself occurs at
201a10-11. The subsequent examples and explanation clarify it but are not folded into this
weakest reading.

Source: Aristotle, *Physics* III.1, 201a10-11; immediate context 200b12-201b15
(Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangeAsActualityOfPotentialReading
    {Occurrence : Type u}
    {Subject : Type v}
    (IsChange : Occurrence → Prop)
    (ExistsPotentially : Subject → Prop)
    (IsActualityOfQuaPotential : Occurrence → Subject → Prop) : Prop :=
  ∀ occurrence,
    IsChange occurrence ↔
      ∃ subject,
        ExistsPotentially subject ∧
          IsActualityOfQuaPotential occurrence subject

/--
Outcome-indexed reading of Aristotle, *Physics* III.1, 201a10-11: an occurrence is
change exactly when it is the actuality of a subject's potential for some outcome,
precisely qua having that potential.

The examples immediately following the definition—alterable qua alterable, increasable,
buildable qua buildable—make a potential-for-an-outcome reading defensible. It remains
separate from `ChangeAsActualityOfPotentialReading` because the compact Greek definition
does not itself supply an explicit outcome variable.

`PotentialFor` and `IsActualityOfQuaPotentialFor` remain primitive. Consequently this
reading does not assert that change reaches the outcome, consumes the potentiality, is a
completed actuality, or has any modern temporal or causal analysis.

Source: Aristotle, *Physics* III.1, 201a10-15; explanatory context 201a27-201b15
(Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangeAsActualityOfPotentialForOutcomeReading
    {Occurrence : Type u}
    {Subject : Type v}
    {Outcome : Type w}
    (IsChange : Occurrence → Prop)
    (PotentialFor : Subject → Outcome → Prop)
    (IsActualityOfQuaPotentialFor : Occurrence → Subject → Outcome → Prop) : Prop :=
  ∀ occurrence,
    IsChange occurrence ↔
      ∃ subject outcome,
        PotentialFor subject outcome ∧
          IsActualityOfQuaPotentialFor occurrence subject outcome

/--
Physical-mover reading of Aristotle, *Physics* III.1, 201a19-25: a thing that is actively
moving something in the relevant physical way is itself moved.

`MovesPhysically` deliberately packages the passage's qualification. This does not say that
every mover without qualification is moved; Aristotle immediately distinguishes the case of
an unmoved mover.

Source: Aristotle, *Physics* III.1, 201a19-25 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PhysicalMoverIsMovedReading
    {Entity : Type u}
    (MovesPhysically : Entity → Prop)
    (IsMoved : Entity → Prop) : Prop :=
  ∀ mover, MovesPhysically mover → IsMoved mover

/--
Existential reading of Aristotle, *Physics* III.1, 201a25-27: there is a mover that is
unmoved.

The passage only announces the exception here and defers its fuller demonstration. This
reading therefore records existence without importing the later argument or identifying the
mover with any theological description.

Source: Aristotle, *Physics* III.1, 201a25-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def UnmovedMoverExistsReading
    {Entity : Type u}
    (IsMover : Entity → Prop)
    (IsMoved : Entity → Prop) : Prop :=
  ∃ mover, IsMover mover ∧ ¬ IsMoved mover

/--
Temporal-coincidence reading of Aristotle, *Physics* III.1, 201b5-8: a subject is moving at
exactly those times at which the relevant actuality of it qua potential is present—neither
before nor after.

This is intentionally separate from the compact 201a10-11 definition because the later
passage makes the temporal qualification explicit. `QuaPotentialActualityAt` remains
primitive; the definition does not impose a modern theory of time or persistence.

Source: Aristotle, *Physics* III.1, 201b5-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionCoincidesWithQuaPotentialActualityReading
    {Subject : Type u}
    {Time : Type v}
    (IsMovingAt : Subject → Time → Prop)
    (QuaPotentialActualityAt : Subject → Time → Prop) : Prop :=
  ∀ subject time,
    IsMovingAt subject time ↔ QuaPotentialActualityAt subject time

/--
First premise of Aristotle's buildable example in *Physics* III.1, 201b9-11: for the
actuality relevant to the buildable qua buildable, the live alternatives under discussion are
the process of building or the completed house.

The proposition variables are deliberately narrow: this is not a claim that every actuality
whatsoever has exactly these alternatives.

Source: Aristotle, *Physics* III.1, 201b9-11 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BuildableActualityAlternativeReading
    (BuildingIsActuality : Prop)
    (HouseIsActuality : Prop) : Prop :=
  BuildingIsActuality ∨ HouseIsActuality

/--
Second premise distilled from Aristotle's parenthetical reasoning in *Physics* III.1,
201b10-13: the completed house is not the actuality of the buildable precisely qua buildable,
because once the house is there the subject is no longer buildable in that respect.

This does not deny that the completed house is an actuality in another respect. It excludes
only the completed-house alternative from the actuality whose subject is the buildable qua
buildable.

Source: Aristotle, *Physics* III.1, 201b10-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CompletedHouseNotBuildableActualityReading
    (HouseIsActuality : Prop) : Prop :=
  ¬ HouseIsActuality

/--
Conclusion of Aristotle's buildable example in *Physics* III.1, 201b9-15: the actuality of
the buildable precisely qua buildable is building.

The wrapper preserves the source proposition as an independently identified statement while
the corresponding verified argument records the disjunctive inference from Aristotle's two
explicit premises.

Source: Aristotle, *Physics* III.1, 201b9-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BuildableActualityIsBuildingReading
    (BuildingIsActuality : Prop) : Prop :=
  BuildingIsActuality

/--
Non-necessitation reading of Aristotle, *Physics* III.2, 201b19-24: being different, unequal,
or a non-being does not by itself necessitate being in motion.

The three predicates remain uninterpreted. This preserves Aristotle's immediate argument
against identifying motion with any of them without importing a modern account of
difference, inequality, or non-being.

Source: Aristotle, *Physics* III.2, 201b19-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AlternativePredicatesDoNotNecessitateMotionReading
    {Entity : Type u}
    (Different : Entity → Prop)
    (Unequal : Entity → Prop)
    (NonBeing : Entity → Prop)
    (IsMoved : Entity → Prop) : Prop :=
  (¬ (∀ entity, Different entity → IsMoved entity)) ∧
    (¬ (∀ entity, Unequal entity → IsMoved entity)) ∧
    (¬ (∀ entity, NonBeing entity → IsMoved entity))

/--
Conclusion drawn in Aristotle, *Physics* III.2, 201b19-24: motion is not identical with
difference, inequality, or non-being.

Identity here is represented extensionally only for the purpose of the explicit rejection.
No claim is made that Aristotle's metaphysical notion of identity is exhausted by predicate
coextension.

Source: Aristotle, *Physics* III.2, 201b19-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionNotIdenticalWithAlternativePredicatesReading
    {Entity : Type u}
    (Different : Entity → Prop)
    (Unequal : Entity → Prop)
    (NonBeing : Entity → Prop)
    (IsMoved : Entity → Prop) : Prop :=
  (¬ (∀ entity, Different entity ↔ IsMoved entity)) ∧
    (¬ (∀ entity, Unequal entity ↔ IsMoved entity)) ∧
    (¬ (∀ entity, NonBeing entity ↔ IsMoved entity))

/--
Classification reading of Aristotle, *Physics* III.2, 201b27-202a2: motion cannot simply be
identified either with bare potentiality or with sheer/completed actuality.

The passage argues by noting that what is merely potential need not already be moving and
what is actually the relevant completed kind need not be moving either. The primitive
predicates avoid deciding a broader Aristotelian taxonomy of actuality at this stage.

Source: Aristotle, *Physics* III.2, 201b27-202a2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionNeitherBarePotentialNorSheerActualityReading
    {Entity : Type u}
    (BarePotential : Entity → Prop)
    (SheerActuality : Entity → Prop)
    (IsMoved : Entity → Prop) : Prop :=
  (¬ (∀ entity, BarePotential entity ↔ IsMoved entity)) ∧
    (¬ (∀ entity, SheerActuality entity ↔ IsMoved entity))

/--
Positive classification reading of Aristotle, *Physics* III.2, 201b31-202a2: motion is an
actuality, but an incomplete actuality, because the potential whose actuality it is is
incomplete.

`IsIncompleteActualityOfPotential` remains a supplied relation. This records Aristotle's
classification without equating incompleteness with a modern temporal, mereological, or
process-theoretic notion.

Source: Aristotle, *Physics* III.2, 201b31-202a2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionAsIncompleteActualityReading
    {Occurrence : Type u}
    (IsMotion : Occurrence → Prop)
    (IsIncompleteActualityOfPotential : Occurrence → Prop) : Prop :=
  ∀ occurrence, IsMotion occurrence → IsIncompleteActualityOfPotential occurrence

/--
Reciprocity-by-contact reading of Aristotle, *Physics* III.2, 202a3-7: when a mover acts on
a movable by contact in the relevant way, the mover is at the same time affected.

This is narrower than the earlier existence of an unmoved mover and does not erase that
exception. `MovesByContact` records the local physical qualification supplied by this
passage.

Source: Aristotle, *Physics* III.2, 202a3-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContactMoverIsAffectedReading
    {Mover : Type u}
    {Movable : Type v}
    (MovesByContact : Mover → Movable → Prop)
    (IsAffected : Mover → Prop) : Prop :=
  ∀ mover movable, MovesByContact mover movable → IsAffected mover

/--
Restatement reading of Aristotle, *Physics* III.2, 202a7-9: motion is the actuality of the
movable precisely qua movable, with the occurrence taking place through contact with a mover.

The contact relation is kept explicit rather than silently folded into the general III.1
definition. This statement therefore records the additional mover/movable structure exposed
in III.2.

Source: Aristotle, *Physics* III.2, 202a7-9 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionAsActualityOfMovableByContactReading
    {Occurrence : Type u}
    {Movable : Type v}
    {Mover : Type w}
    (IsMotion : Occurrence → Prop)
    (IsActualityOfQuaMovable : Occurrence → Movable → Prop)
    (OccursByContactWith : Occurrence → Mover → Movable → Prop) : Prop :=
  ∀ occurrence,
    IsMotion occurrence ↔
      ∃ movable mover,
        IsActualityOfQuaMovable occurrence movable ∧
          OccursByContactWith occurrence mover movable

/--
Form-as-source reading of Aristotle, *Physics* III.2, 202a9-12: a mover, insofar as it acts
as mover, brings or carries a form that functions as source and cause of the change.

The example of an actual human generating a human from a potential human motivates the
relation while the formalization remains generic. It does not identify every efficient cause
with a form or settle the relation among Aristotle's four causal modes.

Source: Aristotle, *Physics* III.2, 202a9-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MoverCarriesFormAsCauseReading
    {Mover : Type u}
    {Form : Type v}
    {Change : Type w}
    (Moves : Mover → Change → Prop)
    (CarriesForm : Mover → Form → Prop)
    (FormIsSourceAndCauseOf : Form → Change → Prop) : Prop :=
  ∀ mover change,
    Moves mover change →
      ∃ form,
        CarriesForm mover form ∧
          FormIsSourceAndCauseOf form change

/--
Location reading of Aristotle, *Physics* III.3, 202a13-15: the motion is in the movable.

`IsMotionOf` and `IsInMovable` remain supplied relations so that "in" is not silently
converted into spatial containment. The source explains the location through motion's being
the actuality of the movable under the action of what can move it.

Typed sibling reading over the act/potency vocabulary:
`TruthCore.Greek.Aristotle.Physics.Typed.MovingIsInTheMovedReading` (docs/typed-physics.md).

Source: Aristotle, *Physics* III.3, 202a13-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionLocatedInMovableReading
    {Motion : Type u}
    {Movable : Type v}
    (IsMotionOf : Motion → Movable → Prop)
    (IsInMovable : Motion → Movable → Prop) : Prop :=
  ∀ motion movable, IsMotionOf motion movable → IsInMovable motion movable

/--
Shared-actuality reading of Aristotle, *Physics* III.3, 202a14-20: the actuality of the mover
as acting on the movable and the actuality of the movable as being moved are one actuality.

The two actuality relations remain distinct predicates even when one witness satisfies both.
This preserves Aristotle's later insistence that the accounts of agency and patiency differ.

Source: Aristotle, *Physics* III.3, 202a14-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MoverMovedShareOneActualityReading
    {Mover : Type u}
    {Movable : Type v}
    {Actuality : Type w}
    (Moves : Mover → Movable → Prop)
    (ActualityOfMoverActing : Actuality → Mover → Movable → Prop)
    (ActualityOfMovableBeingMoved : Actuality → Mover → Movable → Prop) : Prop :=
  ∀ mover movable,
    Moves mover movable →
      ∃ actuality,
        ActualityOfMoverActing actuality mover movable ∧
          ActualityOfMovableBeingMoved actuality mover movable

/--
First premise of Aristotle's dialectical resolution in *Physics* III.3, 202a25-35: if
agency and patiency were two distinct motions in the patient, the patient would undergo two
simultaneous alterations toward one definite form.

The propositions are intentionally scoped to the objection being answered; no general rule
about every pair of activities is asserted.

Source: Aristotle, *Physics* III.3, 202a25-35 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DistinctAgencyPatiencyWouldDoubleAlterationReading
    (AgencyPatiencyAreDistinctMotions : Prop)
    (TwoAlterationsTowardOneForm : Prop) : Prop :=
  AgencyPatiencyAreDistinctMotions → TwoAlterationsTowardOneForm

/--
Second premise in Aristotle's *Physics* III.3, 202a31-35: two simultaneous alterations of
one patient toward one definite form are impossible in the case under discussion.

Source: Aristotle, *Physics* III.3, 202a31-35 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TwoAlterationsTowardOneFormImpossibleReading
    (TwoAlterationsTowardOneForm : Prop) : Prop :=
  ¬ TwoAlterationsTowardOneForm

/--
Conclusion of the preceding argument in Aristotle, *Physics* III.3, 202a31-36: agency and
patiency are not two distinct motions in the patient; the actualization is one.

This weak conclusion does not yet say that agency and patiency have the same definition.

Source: Aristotle, *Physics* III.3, 202a31-36 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AgencyPatiencyNotDistinctMotionsReading
    (AgencyPatiencyAreDistinctMotions : Prop) : Prop :=
  ¬ AgencyPatiencyAreDistinctMotions

/--
Qualified identity reading of Aristotle, *Physics* III.3, 202b5-10: one actuality can belong
to the agent and patient while their activities are not thereby the same in account.

The two proposition parameters keep underlying actuality identity distinct from identity in
definition. The statement records the combination Aristotle explicitly permits rather than a
general principle that every shared actuality entails difference of account.

Source: Aristotle, *Physics* III.3, 202b5-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SharedActualityDifferentAccountReading
    (ShareOneActuality : Prop)
    (SameInAccount : Prop) : Prop :=
  ShareOneActuality ∧ ¬ SameInAccount

/--
Teaching/learning conclusion of Aristotle, *Physics* III.3, 202b16-22: teaching and learning,
and more generally agency and patiency, belong to one underlying motion while differing in
account.

This preserves the source's distinction between sameness of the underlying motion and
sameness of definition; it does not infer that the teacher learns merely because teaching and
learning concern the same motion.

Source: Aristotle, *Physics* III.3, 202b16-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TeachingLearningSameMotionDifferentAccountReading
    (ShareUnderlyingMotion : Prop)
    (SameInAccount : Prop) : Prop :=
  ShareUnderlyingMotion ∧ ¬ SameInAccount

/--
Respect-indexed reading of Aristotle, *Physics* III.1, 201a10-11, in the act/potency
vocabulary of the *prima via*: a being is being moved in a respect exactly when it is
potentially that respect and that potency, precisely as a potency, is being actualized
(ἡ τοῦ δυνάμει ὄντος ἐντελέχεια, ᾗ τοιοῦτον, κίνησίς ἐστιν).

`MovedIn` and `InPotency` are the predicates of
`TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading`. The respect `r`
plays the part of the outcome in `ChangeAsActualityOfPotentialForOutcomeReading`, and
`ActualizedQuaPotential x r` stays primitive: it does not decide between actuality and
actualization, adds no time, mover or completion, and does not say that the potency
survives the motion's end. Unlike the occurrence readings above, this one speaks of a
being moved in a respect, not of an occurrence that is a change.

This is a *definitional analysis* of being moved. It makes
`MovedOnlyAsInPotencyReading` analytic; the formal fact
`TruthCore.Latin.Aquinas.SummaTheologiae.ActPotencyDefinitionalAnalysesConservative`
shows that it is also no stronger than that premise while `ActualizedQuaPotential` is
constrained by nothing else.

Source: Aristotle, *Physics* III.1, 201a10-11 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BeingMovedIsActualizationOfPotencyReading
    {Being : Sort u}
    {Respect : Sort v}
    (MovedIn InPotency ActualizedQuaPotential : Being → Respect → Prop) : Prop :=
  ∀ x r, MovedIn x r ↔ InPotency x r ∧ ActualizedQuaPotential x r

/--
Some potential is not being actualized: a being is in potency in a respect without being
moved in it. Aristotle, *Physics* III.1, 201b8-9: motion occurs just when the actuality of
the potential is present, "for each thing can be active at one time and not at another, as
the buildable" (ἐνδέχεται γὰρ ἕκαστον ὁτὲ μὲν ἐνεργεῖν ὁτὲ δὲ μή, οἷον τὸ οἰκοδομητόν).
The buildable's activity as buildable is building (201b9-15), so a buildable that is not
being built is in potency to the house and is not being moved toward it.

Reading steps. "The buildable" is read with the case's `InPotency` (it is able to be a house
and is not one) and "being active" as the buildable with the case's `MovedIn` (motion as
reduction, `DEF-MOTION-AS-REDUCTION`). The source says that each thing *can* at some time
not be active; the formal statement takes one such time, the time at which the case's
premises are read, and asserts only that at it some potential is not being actualized. It
says nothing of every potential, and nothing about why it is not being actualized.

Source: Aristotle, *Physics* III.1, 201b8-9 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SomePotencyNotBeingActualizedReading
    {Being : Sort u}
    {Respect : Sort v}
    (InPotency MovedIn : Being → Respect → Prop) : Prop :=
  ∃ x r, InPotency x r ∧ ¬ MovedIn x r

end TruthCore.Greek.Aristotle.Physics
