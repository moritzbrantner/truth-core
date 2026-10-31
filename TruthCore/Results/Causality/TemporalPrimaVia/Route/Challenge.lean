import TruthCore.Causality.TemporalPrimaVia
namespace TruthCore.Results.Causality.TemporalPrimaVia.Route
open TruthCore.Causality.TemporalActualization
open TruthCore.Causality.TemporalPrimaVia
theorem route {E B R T : Type} [LinearOrder T]
    (clock : E → T) (bearer : E → B) (respect : E → R) (C : E → E → Prop)
    (Moves : T → B → B → R → Prop) (Moved Actual Potency : T → B → R → Prop)
    (Link : T → B → B → Prop)
    (hNoBack : NoBackward clock C)
    (hProjection : MotionProjection clock bearer respect C Moves)
    (hLocated : LocatedMotion Moves Moved)
    (hPotential : PotentialMotion Moved Potency)
    (hActual : ActualMover Moves Actual)
    (hNotBoth : NotBoth Actual Potency)
    (hReduction : SliceReduction Moved Moves)
    (hPerSe : SliceSecondMovers Moved Moves Link)
    (hBridge : LinkOnSimultaneousEdge clock bearer C Link)
    (hRegress : RegressIfSimultaneous clock C Link) :
    SliceRouteOutcome clock C Moved Moves := by
  sorry
end TruthCore.Results.Causality.TemporalPrimaVia.Route
