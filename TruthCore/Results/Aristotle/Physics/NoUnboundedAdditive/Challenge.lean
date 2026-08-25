import TruthCore.Greek.Aristotle.Physics.BookIII.Chapter6

namespace TruthCore.Results.Aristotle.Physics.NoUnboundedAdditive

open TruthCore.Greek.Aristotle.Physics

/--
If an additive potential exceeding every determinate magnitude would require an actually
infinite sensible body, while III.5 rules out such a body, then that unbounded additive
potential does not exist.
-/
theorem noUnboundedAdditivePotential
    (UnboundedAdditivePotential : Prop)
    (ActuallyInfiniteSensibleBody : Prop)
    (hRequiresActual :
      UnboundedAdditivePotentialRequiresActualInfiniteBodyReading
        UnboundedAdditivePotential ActuallyInfiniteSensibleBody)
    (hNoActual :
      NoActuallyInfiniteSensibleBodyReading ActuallyInfiniteSensibleBody) :
    NoUnboundedAdditivePotentialReading UnboundedAdditivePotential := by
  sorry

end TruthCore.Results.Aristotle.Physics.NoUnboundedAdditive
