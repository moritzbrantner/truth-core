import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter6

namespace TruthCore.Greek.Aristotle.Physics

/-- A finite magnitude traversed as a whole is measured by finitely many finite
segments even when the motion is not uniform in Aristotle, *Physics* VI.7,
237b34-238a17.

Source: Aristotle, *Physics* VI.7, 237b34-238a17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FiniteMagnitudeHasFiniteSegmentMeasureReading
    (MagnitudeTraversalFinite HasFiniteSegmentMeasure : Prop) : Prop :=
  MagnitudeTraversalFinite → HasFiniteSegmentMeasure

/-- Each finite segment in the finite measure of a completed traversal is traversed
in a finite subtime, whether the motion accelerates, decelerates, or remains steady,
in Aristotle, *Physics* VI.7, 238a1-10.

Source: Aristotle, *Physics* VI.7, 238a1-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EachMeasuringSegmentHasFiniteTraversalTimeReading
    (HasFiniteSegmentMeasure AllMeasuringSegmentTimesFinite : Prop) : Prop :=
  HasFiniteSegmentMeasure → AllMeasuringSegmentTimesFinite

/-- The finitely many finite times corresponding to a finite segment measure compose
a finite whole traversal time in Aristotle, *Physics* VI.7, 238a10-17.

Source: Aristotle, *Physics* VI.7, 238a10-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FiniteSegmentTimesYieldFiniteWholeTimeReading
    (HasFiniteSegmentMeasure AllMeasuringSegmentTimesFinite
      WholeTraversalTimeFinite : Prop) : Prop :=
  HasFiniteSegmentMeasure → AllMeasuringSegmentTimesFinite →
    WholeTraversalTimeFinite

/-- A finite magnitude traversed as a whole cannot take infinite time, whether the
motion is uniform or non-uniform, in Aristotle, *Physics* VI.7, 237b23-238a17.

Source: Aristotle, *Physics* VI.7, 237b23-238a17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FiniteMagnitudeTraversalHasFiniteTimeReading
    (MagnitudeTraversalFinite WholeTraversalTimeFinite : Prop) : Prop :=
  MagnitudeTraversalFinite → WholeTraversalTimeFinite

/-- The same finite-time restriction applies to the process of coming to rest in
Aristotle, *Physics* VI.7, 238a17-18; this does not limit how long the resulting
state of rest may persist.

Source: Aristotle, *Physics* VI.7, 238a17-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FiniteCessationProcessHasFiniteTimeReading
    (CessationProcessFinite CessationTimeFinite : Prop) : Prop :=
  CessationProcessFinite → CessationTimeFinite

/-- One and the same thing cannot be forever undergoing a single generation or a
single destruction in Aristotle, *Physics* VI.7, 238a18-20.

Source: Aristotle, *Physics* VI.7, 238a18-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SameThingNotGeneratingOrPerishingForeverReading
    (SameThingGeneratesForever SameThingPerishesForever : Prop) : Prop :=
  ¬ SameThingGeneratesForever ∧ ¬ SameThingPerishesForever

end TruthCore.Greek.Aristotle.Physics
