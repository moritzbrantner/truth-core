import TruthCore.Alternatives.Inertia

/-!
The inertial objection to the prima via's mover premise as a theory bundle
(#497): the strongest recorded rival behind the unattributed
`TruthCore.Alternatives.ActPotencyRegress.UniformMotionWithoutMoverReading`.

Four commitments. One is sourced to Newton (Def. III-IV, claim
`NEWTON-PRINCIPIA-PERSEVERANCE-BY-INERTIA-A`); the becoming reading is sourced to
Garrigou-Lagrange, a Thomist who holds it while rejecting the objection
(claim `GARRIGOU-LAGRANGE-DIEU-1914-LOCAL-MOTION-IS-BECOMING-A`); the existence
of a persevering body and the mover bridge are unattributed open premises. No
pinned source states the whole bundle; no modern statement of the objection is
pinned.
-/

namespace TruthCore.Comparison.Inertia

open TruthCore.Alternatives.Inertia

universe u v

/-- The inertial objection: a body perseveres in uniform motion by its inherent
force alone; some body so perseveres; whatever moves such a body in that respect
is something it perseveres by; and such perseverance is a being moved. -/
def InertialObjection {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (UniformLocalMotion : Respect → Prop)
    (Perseveres : Being → Respect → Prop)
    (PerseveresBy : Being → Being → Respect → Prop) : Prop :=
  PerseveranceByInherentForceAloneReading UniformLocalMotion Perseveres PerseveresBy ∧
    SomeBodyPerseveresInUniformMotionReading UniformLocalMotion Perseveres ∧
    MoverOfPerseveringBodyAccountsForPerseveranceReading MovesIn UniformLocalMotion
      Perseveres PerseveresBy ∧
    UniformPerseveranceIsBeingMovedReading MovedIn UniformLocalMotion Perseveres

end TruthCore.Comparison.Inertia
