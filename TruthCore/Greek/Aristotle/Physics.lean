/-!
Source-derived claims from Aristotle's *Physics*.
-/

namespace TruthCore.Greek.Aristotle.Physics

universe u v

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

end TruthCore.Greek.Aristotle.Physics
