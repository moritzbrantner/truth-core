import TruthCore.Comparison.Inertia
import TruthCore.Models.Inertia
namespace TruthCore.Results.Alternatives.InertialObjectionYieldsRival
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Alternatives.ActPotencyRegress
open TruthCore.Alternatives.Inertia
open TruthCore.Comparison.Inertia

/-- The inertial objection yields the inertial rival (#497). If a body
perseveres in uniform motion by its inherent force alone (Newton, Def. III-IV),
some body so perseveres (open), whatever moves such a body in that respect is
something it perseveres by (open bridge), such perseverance is a being moved
(Garrigou-Lagrange's becoming reading), and nothing moved in a respect moves
itself in it (ST I q.2 a.3), then some body is being moved in a respect of
uniform motion with nothing moving it in that respect. -/
theorem inertialObjectionYieldsRival {Being Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (UniformLocalMotion : Respect → Prop)
    (Perseveres : Being → Respect → Prop)
    (PerseveresBy : Being → Being → Respect → Prop)
    (hTheory : InertialObjection MovedIn MovesIn UniformLocalMotion Perseveres PerseveresBy)
    (hNoSelfMotion : NothingMovesItselfInSameRespectReading MovedIn MovesIn) :
    UniformMotionWithoutMoverReading MovedIn MovesIn UniformLocalMotion := by
  obtain ⟨hAlone, ⟨x, r, hUniform, hPerseveres⟩, hBridge, hBecoming⟩ := hTheory
  -- On the becoming reading the persevering body is being moved.
  have hMoved : MovedIn x r := hBecoming x r hUniform hPerseveres
  refine ⟨x, r, hUniform, hMoved, fun y hMoves => ?_⟩
  -- A mover would be something the body perseveres by, hence the body itself.
  have hSame : y = x := hAlone x r y hUniform hPerseveres (hBridge y x r hUniform hPerseveres hMoves)
  -- But nothing moved moves itself in the same respect.
  exact hNoSelfMotion x r hMoved (hSame ▸ hMoves)

/-- With the mover premise the objection and no self-motion are inconsistent:
the minimal core. The premise it rivals is used here, so this is the clash, not
an elimination. -/
theorem objectionWithMoverPremiseInconsistent :
    ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (UniformLocalMotion : Respect → Prop)
        (Perseveres : Being → Respect → Prop)
        (PerseveresBy : Being → Being → Respect → Prop),
      InertialObjection MovedIn MovesIn UniformLocalMotion Perseveres PerseveresBy →
        NothingMovesItselfInSameRespectReading MovedIn MovesIn →
          ReducedOnlyByAMoverReading MovedIn MovesIn → False := by
  intro Being Respect MovedIn MovesIn UniformLocalMotion Perseveres PerseveresBy
    hTheory hNoSelfMotion hHasMover
  obtain ⟨x, r, _, hMoved, hNoMover⟩ :=
    inertialObjectionYieldsRival MovedIn MovesIn UniformLocalMotion Perseveres PerseveresBy
      hTheory hNoSelfMotion
  obtain ⟨y, hMoves⟩ := hHasMover x r hMoved
  exact hNoMover y hMoves

/-- Newton's "by inertia alone" is needed: in `MODEL-INERTIA-OTHER-SUSTAINER`
another being both moves the persevering body and is what it perseveres by. -/
theorem needsPerseveranceAlone :
    ¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (UniformLocalMotion : Respect → Prop)
        (Perseveres : Being → Respect → Prop)
        (PerseveresBy : Being → Being → Respect → Prop),
      SomeBodyPerseveresInUniformMotionReading UniformLocalMotion Perseveres →
        MoverOfPerseveringBodyAccountsForPerseveranceReading MovesIn UniformLocalMotion
          Perseveres PerseveresBy →
          UniformPerseveranceIsBeingMovedReading MovedIn UniformLocalMotion Perseveres →
            NothingMovesItselfInSameRespectReading MovedIn MovesIn →
              UniformMotionWithoutMoverReading MovedIn MovesIn UniformLocalMotion := by
  intro h
  open TruthCore.Models.Inertia.OtherSustainer in
  exact evaluation6 (h Bool Unit model.MovedIn model.MovesIn model.UniformLocalMotion
    model.Perseveres model.PerseveresBy evaluation1 evaluation2 evaluation3 evaluation4)

/-- The persevering body is needed: in `MODEL-INERTIA-NO-PERSEVERING` nothing
perseveres in uniform motion. -/
theorem needsPersevering :
    ¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (UniformLocalMotion : Respect → Prop)
        (Perseveres : Being → Respect → Prop)
        (PerseveresBy : Being → Being → Respect → Prop),
      PerseveranceByInherentForceAloneReading UniformLocalMotion Perseveres PerseveresBy →
        MoverOfPerseveringBodyAccountsForPerseveranceReading MovesIn UniformLocalMotion
          Perseveres PerseveresBy →
          UniformPerseveranceIsBeingMovedReading MovedIn UniformLocalMotion Perseveres →
            NothingMovesItselfInSameRespectReading MovedIn MovesIn →
              UniformMotionWithoutMoverReading MovedIn MovesIn UniformLocalMotion := by
  intro h
  open TruthCore.Models.Inertia.NoPersevering in
  exact evaluation6 (h Unit Unit model.MovedIn model.MovesIn model.UniformLocalMotion
    model.Perseveres model.PerseveresBy evaluation0 evaluation2 evaluation3 evaluation4)

/-- The mover bridge is needed: in `MODEL-INERTIA-DIVINE-MOVER` the body
perseveres by itself alone and is moved by another being it does not persevere
by. -/
theorem needsMoverBridge :
    ¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (UniformLocalMotion : Respect → Prop)
        (Perseveres : Being → Respect → Prop)
        (PerseveresBy : Being → Being → Respect → Prop),
      PerseveranceByInherentForceAloneReading UniformLocalMotion Perseveres PerseveresBy →
        SomeBodyPerseveresInUniformMotionReading UniformLocalMotion Perseveres →
          UniformPerseveranceIsBeingMovedReading MovedIn UniformLocalMotion Perseveres →
            NothingMovesItselfInSameRespectReading MovedIn MovesIn →
              UniformMotionWithoutMoverReading MovedIn MovesIn UniformLocalMotion := by
  intro h
  open TruthCore.Models.Inertia.DivineMover in
  exact evaluation6 (h Bool Unit model.MovedIn model.MovesIn model.UniformLocalMotion
    model.Perseveres model.PerseveresBy evaluation0 evaluation1 evaluation3 evaluation4)

/-- The becoming reading is needed: in `MODEL-INERTIA-STATE-READING` the
persevering body is not moved in its uniform motion. -/
theorem needsBecomingReading :
    ¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (UniformLocalMotion : Respect → Prop)
        (Perseveres : Being → Respect → Prop)
        (PerseveresBy : Being → Being → Respect → Prop),
      PerseveranceByInherentForceAloneReading UniformLocalMotion Perseveres PerseveresBy →
        SomeBodyPerseveresInUniformMotionReading UniformLocalMotion Perseveres →
          MoverOfPerseveringBodyAccountsForPerseveranceReading MovesIn UniformLocalMotion
            Perseveres PerseveresBy →
            NothingMovesItselfInSameRespectReading MovedIn MovesIn →
              UniformMotionWithoutMoverReading MovedIn MovesIn UniformLocalMotion := by
  intro h
  open TruthCore.Models.Inertia.StateReading in
  exact evaluation6 (h Bool Bool model.MovedIn model.MovesIn model.UniformLocalMotion
    model.Perseveres model.PerseveresBy evaluation0 evaluation1 evaluation2 evaluation4)

/-- No self-motion is needed: in `MODEL-INERTIA-SELF-MOVER` the persevering
body moves itself. -/
theorem needsNoSelfMotion :
    ¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (UniformLocalMotion : Respect → Prop)
        (Perseveres : Being → Respect → Prop)
        (PerseveresBy : Being → Being → Respect → Prop),
      InertialObjection MovedIn MovesIn UniformLocalMotion Perseveres PerseveresBy →
        UniformMotionWithoutMoverReading MovedIn MovesIn UniformLocalMotion := by
  intro h
  open TruthCore.Models.Inertia.SelfMover in
  exact evaluation6 (h Unit Unit model.MovedIn model.MovesIn model.UniformLocalMotion
    model.Perseveres model.PerseveresBy ⟨evaluation0, evaluation1, evaluation2, evaluation3⟩)

/-- The mover premise is not refuted by the rest of the core: in
`MODEL-INERTIA-RIVAL-SURVIVES` the bundle and no self-motion hold and the mover
premise fails. So the clash cannot be resolved against the objection without
the premise it rivals: no non-circular elimination from these commitments. -/
theorem rivalSurvivesCore :
    ¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (UniformLocalMotion : Respect → Prop)
        (Perseveres : Being → Respect → Prop)
        (PerseveresBy : Being → Being → Respect → Prop),
      InertialObjection MovedIn MovesIn UniformLocalMotion Perseveres PerseveresBy →
        NothingMovesItselfInSameRespectReading MovedIn MovesIn →
          ReducedOnlyByAMoverReading MovedIn MovesIn := by
  intro h
  open TruthCore.Models.Inertia.RivalSurvives in
  exact evaluation5 (h Unit Unit model.MovedIn model.MovesIn model.UniformLocalMotion
    model.Perseveres model.PerseveresBy ⟨evaluation0, evaluation1, evaluation2, evaluation3⟩
    evaluation4)

/-- Compatibility on the state reading: Newton's Def. III-IV and Lex I, a body
persevering in uniform motion, the mover bridge, no self-motion, the state
reading, the mover premise and something moved hold together in
`MODEL-INERTIA-STATE-READING`. On that reading the mover premise's scope
excludes inertial perseverance, and Newton's commitments do not rival it. -/
theorem stateReadingCompatible :
    ∃ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (UniformLocalMotion : Respect → Prop)
        (Perseveres : Being → Respect → Prop)
        (PerseveresBy : Being → Being → Respect → Prop)
        (ChangesState : Being → Prop) (ImpressesForceOn : Being → Being → Prop),
      PerseveranceByInherentForceAloneReading UniformLocalMotion Perseveres PerseveresBy ∧
        ChangeOfStateOnlyByImpressedForceReading ChangesState ImpressesForceOn ∧
        (∃ x, ChangesState x) ∧
        SomeBodyPerseveresInUniformMotionReading UniformLocalMotion Perseveres ∧
        MoverOfPerseveringBodyAccountsForPerseveranceReading MovesIn UniformLocalMotion
          Perseveres PerseveresBy ∧
        NothingMovesItselfInSameRespectReading MovedIn MovesIn ∧
        UniformPerseveranceIsNotBeingMovedReading MovedIn UniformLocalMotion Perseveres ∧
        ReducedOnlyByAMoverReading MovedIn MovesIn ∧
        SomethingIsMovedReading MovedIn := by
  open TruthCore.Models.Inertia.StateReading in
  exact ⟨Bool, Bool, model.MovedIn, model.MovesIn, model.UniformLocalMotion,
    model.Perseveres, model.PerseveresBy, model.ChangesState, model.ImpressesForceOn,
    evaluation0, evaluation8, ⟨true, rfl⟩, evaluation1, evaluation2, evaluation4,
    evaluation7, evaluation5, evaluation9⟩

end TruthCore.Results.Alternatives.InertialObjectionYieldsRival
