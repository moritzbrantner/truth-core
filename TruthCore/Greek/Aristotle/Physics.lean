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
the buildable precisely qua buildable is building, and building is a kind of motion.

The wrapper preserves the source proposition as an independently identified statement while
the corresponding verified argument records the disjunctive inference from Aristotle's two
explicit premises.

Source: Aristotle, *Physics* III.1, 201b9-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BuildableActualityIsBuildingReading
    (BuildingIsActuality : Prop) : Prop :=
  BuildingIsActuality

end TruthCore.Greek.Aristotle.Physics
