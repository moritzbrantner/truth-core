import TruthCore.Causality.Round3FourthWay

namespace TruthCore.Results.Causality.Round3FourthWay
open TruthCore.Causality.Round3FourthWay
open TruthCore.Causality.MaximumDefinitionFork
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics
open TruthCore.Case.Catholicism
open TruthCore.Logic

/-- What is more `r` than `y` stands strictly above `y`'s degree, which is at
least null; so it stands strictly above null, and whatever does has `r`. -/
theorem moreSuchFromPositiveDegree {B R D : Type} [Preorder D]
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop) (deg : R → B → D) (null : D)
    (hExceed : MoreInExceedsDegree MoreIn deg)
    (hNull : NoDegreeBelowNull deg null)
    (hPos : AboveNullDegreeHasThePerfection InAct deg null) :
    MoreSuchHasThePerfectionReading InAct MoreIn := by
  sorry

/-- From any bearer of being, climb by "more in being": the climb cannot go on
forever, so it ends at a bearer that nothing exceeds in being. Grades give a
first bearer, since what is more a being than something is a being. -/
theorem gradesAtBeingFromNoInfiniteAscent {B R : Type}
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R)
    (hWF : NoInfiniteAscentInBeing MoreIn esse)
    (hMore : MoreSuchHasThePerfectionReading InAct MoreIn)
    (hEM : ExcludedMiddle) :
    GradesToMaximumAtBeing InAct MoreIn esse := by
  sorry

/-- On the order by approach, with strict primacy, the primary is a maximum in
being, whatever grades there are. -/
theorem gradesAtBeingFromApproach {B R D : Type} [Preorder D]
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R)
    (near : B → D) (p : B)
    (hApproach : ApproachToPrimaryReading InAct MoreIn esse near p)
    (hStrict : StrictPrimacyReading near p) :
    GradesToMaximumAtBeing InAct MoreIn esse := by
  sorry

/-- Whatever is God is the primary of being, and on the order by approach with
strict primacy the primary is maximal in being. -/
theorem godMaximalFromPrimaryOfBeing {B R D : Type} [Preorder D]
    (IsGod : B → Prop) (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (esse : R) (near : B → D) (p : B)
    (hPrimary : GodIsThePrimaryOfBeing IsGod p)
    (hApproach : ApproachToPrimaryReading InAct MoreIn esse near p)
    (hStrict : StrictPrimacyReading near p) :
    GodIsMaximalInBeing IsGod InAct MoreIn esse := by
  sorry

/-- Being more such goes with approaching the primary more nearly, and the
represented degrees are ordered as the approach; so, among bearers, being more
such goes with a strictly higher represented degree. -/
theorem strictCalibrationFromApproachMeasure {Degree E : Type} [Preorder Degree]
    [Preorder E] (f : Frame Degree) (near : f.Being → E) (p : f.Being)
    (hApproach : ApproachToPrimaryReading f.InAct f.MoreIn f.selected near p)
    (hMeasure : AsMuchAsItApproaches f.value near) :
    StrictDegreeCalibration f := by
  sorry

/-- Comparable bearers are directed: the higher of the two bounds both. -/
theorem directedFromComparableDegrees {Degree : Type} [Preorder Degree]
    (f : Frame Degree) (hComp : BearerDegreesComparable f) :
    DirectedBearers f := by
  sorry

/-- A bearer at the greatest degree bounds every pair of bearers. -/
theorem directedFromGreatestBearer {Degree : Type} [Preorder Degree]
    (f : Frame Degree) (hTop : SomeBearerHasGreatestDegree f) :
    DirectedBearers f := by
  sorry

/-- A greatest-degree bearer is the primary: anything else falls strictly short
of the primary, which is itself a bearer. The primary causes the perfection in
every creature that has it, and everything else is a creature. -/
theorem greatestCausesFromOrderedPrimary {B R D : Type} [Preorder D]
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (Creature : B → Prop) (r : R)
    (value : B → D) (p : B)
    (hApproach : ApproachToPrimaryReading InAct MoreIn r value p)
    (hStrict : StrictPrimacyReading value p)
    (hOrdered : OrderedToPrimaryAsCauseReading InAct CausesIn Creature r p)
    (hOthers : OthersAreCreaturesReading Creature p)
    (hEM : ExcludedMiddle) :
    GreatestDegreeCausesAllInGenusReading InAct CausesIn r value := by
  sorry

/-- A greatest-degree bearer is maximal: whatever exceeded it would be a bearer
(more such has the perfection) at a strictly higher degree (calibration), above
the greatest. The maximal-in-genus principle then makes it the cause of all. -/
theorem greatestCausesFromMaximalPrinciple {Degree : Type} [Preorder Degree]
    (f : Frame Degree)
    (hMax : MaximumInGenusCausesAllInGenusReading f.InAct f.MoreIn f.CausesIn)
    (hMore : MoreSuchHasThePerfectionReading f.InAct f.MoreIn)
    (hCal : StrictDegreeCalibration f) :
    GreatestDegreeCausesAllInGenusReading f.InAct f.CausesIn f.selected f.value := by
  sorry

/-- A maximal bearer of `r` is at the greatest degree of `r`: any bearer is
bounded with it by a third bearer, which cannot stand strictly above it (it
would then be more `r`), so stands at or below it. The greatest-degree genus
principle then makes it the cause of `r` in all others. -/
theorem maximumInGenusFromGreatestEveryGenus {B R D : Type} [Preorder D]
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (deg : R → B → D)
    (hGreatest : GreatestDegreeCausesAllInEveryGenus InAct CausesIn deg)
    (hExcess : DegreeExcessAmongBearersIsMoreIn InAct MoreIn deg)
    (hDir : BearerDegreesDirectedInEveryGenus InAct deg)
    (hEM : ExcludedMiddle) :
    MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn := by
  sorry

/-- Truth goes with intelligibility, and intelligibility with being; so truth
goes with being, both in having and in the comparative. -/
theorem asToBeingSoToTruthFromIntelligibility {E R : Type}
    (Has : E → R → Prop) (MoreIn : R → E → E → Prop) (truth being intel : R)
    (hTruth : TruthOfThingsIsIntelligibility Has MoreIn truth intel)
    (hBeing : IntelligibilityProportionedToBeing Has MoreIn intel being) :
    AsToBeingSoToTruthReading Has MoreIn truth being := by
  sorry

/-- Being more such is a strictly higher degree, and degrees are ordered as the
approach to the primary; so being more such is approaching more nearly. The
primary has the perfection: something is more such than something, so is a
bearer; if it is not the primary it falls short of the primary, which then
exceeds it and so has the perfection. -/
theorem approachToPrimaryFromDegreeMeasure {B R D E : Type} [Preorder D] [Preorder E]
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop) (r : R)
    (value : B → D) (near : B → E) (p : B)
    (hCal : MoreInMatchesDegreeEverywhere MoreIn r value)
    (hMeasure : AsMuchAsItApproaches value near)
    (hStrict : StrictPrimacyReading near p)
    (hMore : MoreSuchHasThePerfectionReading InAct MoreIn)
    (hGrades : GradesFoundInBeing MoreIn r)
    (hEM : ExcludedMiddle) :
    ApproachToPrimaryReading InAct MoreIn r near p := by
  sorry

/-- The batch controls: every omission model and the joint witness. -/
theorem controls : TruthCore.Causality.Round3FourthWay.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.Round3FourthWay
