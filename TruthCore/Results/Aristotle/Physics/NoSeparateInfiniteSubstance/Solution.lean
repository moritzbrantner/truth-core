import TruthCore.Greek.Aristotle.Physics.BookIII.Chapter5

namespace TruthCore.Results.Aristotle.Physics.NoSeparateInfiniteSubstance

open TruthCore.Greek.Aristotle.Physics

/--
If a separable infinite substance would have to be indivisible, while the infinite relevant
to the inquiry is not such an indivisible item, then there is no separable substance which is
itself that infinite.
-/
theorem noSeparateInfiniteSubstance
    (SeparateInfiniteSubstance : Prop)
    (Indivisible : Prop)
    (hWouldBeIndivisible :
      SeparateInfiniteSubstanceWouldBeIndivisibleReading
        SeparateInfiniteSubstance Indivisible)
    (hNotIndivisible : RelevantInfiniteNotIndivisibleReading Indivisible) :
    NoSeparateInfiniteSubstanceReading SeparateInfiniteSubstance := by
  intro hSeparate
  exact hNotIndivisible (hWouldBeIndivisible hSeparate)

end TruthCore.Results.Aristotle.Physics.NoSeparateInfiniteSubstance
