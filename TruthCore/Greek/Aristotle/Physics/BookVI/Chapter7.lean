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

/-- Dividing a finite time into finitely many parts associates only finite traversed
portions with those parts, so finite removal cannot exhaust an infinite extent in
Aristotle, *Physics* VI.7, 238a20-30.

Source: Aristotle, *Physics* VI.7, 238a20-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FiniteTimePartsLeaveInfiniteExtentUnexhaustedReading
    (FiniteTimeHasFinitePartMeasure EachTimePartTraversesFiniteExtent
      InfiniteRemainderPersists : Prop) : Prop :=
  FiniteTimeHasFinitePartMeasure ∧ EachTimePartTraversesFiniteExtent ∧
    InfiniteRemainderPersists

/-- The impossibility of exhausting an infinite extent in finite time is unchanged
whether the extent is infinite in one direction or in both in Aristotle,
*Physics* VI.7, 238a30-32.

Source: Aristotle, *Physics* VI.7, 238a30-32 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def OneOrBothDirectionsInfiniteSameTraversalLimitReading
    (OneDirectionInfiniteCovered BothDirectionsInfiniteCovered : Prop) : Prop :=
  OneDirectionInfiniteCovered ∧ BothDirectionsInfiniteCovered

/-- A finite moving magnitude cannot traverse an infinite extent in a finite time
in Aristotle, *Physics* VI.7, 238a32-238b1.

Source: Aristotle, *Physics* VI.7, 238a32-238b1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FiniteMovingMagnitudeCannotTraverseInfiniteExtentInFiniteTimeReading
    (FiniteMovingMagnitudeTraversesInfiniteExtentInFiniteTime : Prop) : Prop :=
  ¬ FiniteMovingMagnitudeTraversesInfiniteExtentInFiniteTime

/-- An infinite moving magnitude cannot pass over a finite extent in a finite time,
because the finite extent would thereby measure across the infinite moving
magnitude, in Aristotle, *Physics* VI.7, 238b1-11.

Source: Aristotle, *Physics* VI.7, 238b1-11 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfiniteMovingMagnitudeCannotTraverseFiniteExtentInFiniteTimeReading
    (InfiniteMovingMagnitudeTraversesFiniteExtentInFiniteTime : Prop) : Prop :=
  ¬ InfiniteMovingMagnitudeTraversesFiniteExtentInFiniteTime

/-- An infinite moving magnitude cannot traverse an infinite extent in a finite
time, since it contains a finite moving part already excluded from traversing that
infinite extent in finite time, in Aristotle, *Physics* VI.7, 238b11-15.

Source: Aristotle, *Physics* VI.7, 238b11-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfiniteMovingMagnitudeCannotTraverseInfiniteExtentInFiniteTimeReading
    (InfiniteMovingMagnitudeTraversesInfiniteExtentInFiniteTime : Prop) : Prop :=
  ¬ InfiniteMovingMagnitudeTraversesInfiniteExtentInFiniteTime

/-- Any supposed infinite locomotion in a finite time would instantiate one of
three configurations: a finite moving magnitude across an infinite extent, an
infinite moving magnitude across a finite extent, or an infinite moving magnitude
across an infinite extent, in Aristotle, *Physics* VI.7, 238a32-238b22.

Source: Aristotle, *Physics* VI.7, 238a32-238b22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfiniteMotionFiniteTimeConfigurationCasesReading
    (InfiniteMotionInFiniteTime FiniteAcrossInfinite InfiniteAcrossFinite
      InfiniteAcrossInfinite : Prop) : Prop :=
  InfiniteMotionInFiniteTime →
    FiniteAcrossInfinite ∨ InfiniteAcrossFinite ∨ InfiniteAcrossInfinite

/-- No infinite locomotion occurs in a finite time; if locomotion or its spatial
magnitude were infinite, the other would have to be infinite as well, and the
earlier cases exclude the traversal, in Aristotle, *Physics* VI.7, 238b15-22.

Source: Aristotle, *Physics* VI.7, 238b15-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoInfiniteMotionInFiniteTimeReading
    (InfiniteMotionInFiniteTime : Prop) : Prop :=
  ¬ InfiniteMotionInFiniteTime

end TruthCore.Greek.Aristotle.Physics
