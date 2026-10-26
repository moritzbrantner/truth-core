/-!
A capacity requirement from Aristotle, *Physics* VIII.1, 251a8–16.
The beings, respects, `MovedIn` and `InPotency` are the shared act/potency
vocabulary used in `Typed.Motion`; no new per-chapter vocabulary is introduced.
-/

namespace TruthCore.Greek.Aristotle.Physics.Typed

universe u v

/-- Whatever undergoes a physical motion is capable of that particular motion
(*Physics* VIII.1, 251a8–16: τὰ πράγματα τὰ δυνάμενα κινεῖσθαι καθʼ ἑκάστην
κίνησιν). The examples are alteration and local motion.

`InPotency x r` here records the capacity for the terminus of the motion in `r`.
The declaration keeps only the capacity requirement; it does not formalize the
preceding definition of motion as actuality, the existence of movable subjects
independently of an actual motion, or the further temporal priority claim
(πρότερον … πρὶν). In particular it does not assert that a capacity existed at
an earlier time. Those are separate readings.

The physical-respect guard prevents this source reading from asserting a
requirement for every reduction from potency to act in the prima via's broader
sense (`DISAMB-MOTION`). This is a source commitment, not a proved theorem.
-/
def PhysicalMotionRequiresCapacityReading {Being : Sort u} {Respect : Sort v}
    (IsPhysicalRespect : Respect → Prop)
    (MovedIn InPotency : Being → Respect → Prop) : Prop :=
  ∀ x r, IsPhysicalRespect r → MovedIn x r → InPotency x r

end TruthCore.Greek.Aristotle.Physics.Typed
