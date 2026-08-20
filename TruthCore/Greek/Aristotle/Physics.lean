/-!
Source-derived claims from Aristotle's *Physics*.
-/

namespace TruthCore.Greek.Aristotle.Physics

universe u

/--
An exhaustive-classification reading of Aristotle, *Physics* II.3, 194b16-195a3:
an explanatory cause falls under at least one of the material, formal, source-of-change,
or final modes.

The four predicates are parameters because this MVP does not yet impose a universal ontology
of causation. Later passages can refine what each mode means without changing this source record.

Source: Aristotle, *Physics* II.3, 194b16-195a3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FourCauseExhaustiveReading
    {Cause : Type u}
    (Material : Cause → Prop)
    (Formal : Cause → Prop)
    (SourceOfChange : Cause → Prop)
    (Final : Cause → Prop) : Prop :=
  ∀ c, Material c ∨ Formal c ∨ SourceOfChange c ∨ Final c

end TruthCore.Greek.Aristotle.Physics
