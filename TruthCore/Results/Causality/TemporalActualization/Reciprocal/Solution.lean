import TruthCore.Results.Causality.TemporalActualization.Framework.Solution
namespace TruthCore.Results.Causality.TemporalActualization.Reciprocal
open TruthCore.Causality.TemporalActualization
/-- Apply the certified direction fork and the existing canonical respect-switch
result at one shared exercise time. No actual temporal profile is selected. -/
theorem consume {E B R T : Type} [LinearOrder T]
    (clock : E → T) (bearer : E → B) (respect : E → R) (C : E → E → Prop)
    (Moves : T → B → B → R → Prop) (Moved Actual Potency : T → B → R → Prop)
    (hNoBack : NoBackward clock C)
    (hProjection : MotionProjection clock bearer respect C Moves)
    (hLocated : LocatedMotion Moves Moved)
    (hPotential : PotentialMotion Moved Potency)
    (hActual : ActualMover Moves Actual)
    (hNotBoth : NotBoth Actual Potency) : ReciprocalConstraint clock respect C := by
  have fork := (Framework.framework E T clock C).1
  rcases fork with strict | ⟨nonbackward, _⟩ | backward
  · intro e f ef fe
    exact False.elim (Framework.strict_acyclic clock C strict e
      ((Relation.TransGen.single ef).trans (Relation.TransGen.single fe)))
  · intro e f ef fe
    have same : clock e = clock f := le_antisymm
      (le_of_not_gt (nonbackward e f ef)) (le_of_not_gt (nonbackward f e fe))
    refine ⟨same, ?_⟩
    have outgoing : Moves (clock e) (bearer e) (bearer f) (respect f) := by
      rw [same]
      exact hProjection e f ef
    exact TruthCore.Results.Alternatives.RespectSwitch.consecutiveRespects
      (Moved (clock e)) (Actual (clock e)) (Potency (clock e)) (Moves (clock e))
      (hLocated (clock e)) (hPotential (clock e)) (hActual (clock e)) (hNotBoth (clock e))
      (bearer f) (bearer e) (bearer f) (respect e) (respect f)
      (hProjection f e fe) outgoing
  · obtain ⟨e, f, edge, rev⟩ := backward
    exact False.elim (hNoBack e f edge rev)
end TruthCore.Results.Causality.TemporalActualization.Reciprocal
