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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- No self-motion is needed: in `MODEL-INERTIA-SELF-MOVER` the persevering
body moves itself. -/
theorem needsNoSelfMotion :
    ¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (UniformLocalMotion : Respect → Prop)
        (Perseveres : Being → Respect → Prop)
        (PerseveresBy : Being → Being → Respect → Prop),
      InertialObjection MovedIn MovesIn UniformLocalMotion Perseveres PerseveresBy →
        UniformMotionWithoutMoverReading MovedIn MovesIn UniformLocalMotion := by
  sorry

/-- The rest of the core does not entail the mover premise: in
`MODEL-INERTIA-RIVAL-SURVIVES` the bundle and no self-motion hold and the mover
premise fails. So the bundle with no self-motion is satisfiable: these
commitments do not refute the objection without assuming the premise it rivals. -/
theorem rivalSurvivesCore :
    ¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (UniformLocalMotion : Respect → Prop)
        (Perseveres : Being → Respect → Prop)
        (PerseveresBy : Being → Being → Respect → Prop),
      InertialObjection MovedIn MovesIn UniformLocalMotion Perseveres PerseveresBy →
        NothingMovesItselfInSameRespectReading MovedIn MovesIn →
          ReducedOnlyByAMoverReading MovedIn MovesIn := by
  sorry

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
  sorry

end TruthCore.Results.Alternatives.InertialObjectionYieldsRival
