/-!
Unattributed bridges from Papineau's completeness of physics
(`TruthCore.Modern.Papineau.RiseOfPhysicalism.CompletenessOfPhysicsReading`) to
the case's motion vocabulary (`MovedIn`, `MovesIn`, `IsPhysicalRespect`) (#512,
#497).

Neither bridge is stated by Papineau, Aristotle or Aquinas. Both are open
premises recorded so that the agreement and the disagreement between the two
vocabularies can be located exactly: DISAMB-PHYSICAL for the first,
DISAMB-PRIOR-DETERMINATION-AND-MOVER for the second.

`motionOf x r` is the occurrence of `x`'s being moved in respect `r`; it is a
parameter, so no identification of beings with occurrences is made.
-/

namespace TruthCore.Alternatives.PhysicalCompleteness

/-- Bridge, unattributed: whatever is being moved in a respect of physical
motion (place, quality or quantity, DEF-PHYSICAL-RESPECT) undergoes an
occurrence that is physical in Papineau's sense and is an effect.

Open. It fails if some being moved in such a respect, for example in a quality
that is a sensation, is not specifiable without mental vocabulary, or if some
such motion is no effect at all. -/
def PhysicalMotionIsPhysicalEffect {Being Respect Occurrence : Type}
    (IsPhysicalRespect : Respect → Prop)
    (MovedIn : Being → Respect → Prop)
    (motionOf : Being → Respect → Occurrence)
    (Physical IsEffect : Occurrence → Prop) : Prop :=
  ∀ x r, IsPhysicalRespect r → MovedIn x r →
    Physical (motionOf x r) ∧ IsEffect (motionOf x r)

/-- Bridge, unattributed: if `x`'s being moved in `r` is fully determined by law
by prior physical occurrences, then something moves `x` in `r` (per se, in the
case's sense of `MovesIn`, at the same time).

Open, and the place where the two vocabularies part (DISAMB-PRIOR-DETERMINATION-AND-MOVER):
Papineau's determiners are *prior occurrences* and may include `x`'s own
earlier state, as in inertial motion; the case's mover is a *being* that moves
`x` *now*. The bridge passes from the first to the second without argument. -/
def PriorPhysicalDeterminationGivesMover {Being Respect Occurrence : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (motionOf : Being → Respect → Occurrence)
    (Physical : Occurrence → Prop)
    (Prior : Occurrence → Occurrence → Prop)
    (FullyDeterminedByLaw : (Occurrence → Prop) → Occurrence → Prop) : Prop :=
  ∀ x r, MovedIn x r →
    FullyDeterminedByLaw (fun c => Physical c ∧ Prior c (motionOf x r)) (motionOf x r) →
    ∃ y, MovesIn y x r

end TruthCore.Alternatives.PhysicalCompleteness
