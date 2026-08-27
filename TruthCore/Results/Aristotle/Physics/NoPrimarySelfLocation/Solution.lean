import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter3

namespace TruthCore.Results.Aristotle.Physics.NoPrimarySelfLocation

open TruthCore.Greek.Aristotle.Physics

/-- Distinct container and contained roles exclude primary self-location. -/
theorem noPrimarySelfLocation
    (ContainerAndContainedDifferInAccount
      SurfaceAndWhiteDifferInNature
      SurfaceAndWhiteDifferInCapacity
      PrimarySelfLocation : Prop)
    (hRoles :
      ContainerAndContainedDifferInAccountReading
        ContainerAndContainedDifferInAccount
        SurfaceAndWhiteDifferInNature
        SurfaceAndWhiteDifferInCapacity)
    (hBridge :
      DistinctRolesExcludePrimarySelfLocationReading
        ContainerAndContainedDifferInAccount PrimarySelfLocation) :
    PrimarySelfLocationImpossibleReading PrimarySelfLocation := by
  exact hBridge hRoles.1

end TruthCore.Results.Aristotle.Physics.NoPrimarySelfLocation
