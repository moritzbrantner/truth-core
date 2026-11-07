module

public import TruthCore.Causality.Round3FourthWay

@[expose] public section

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
  intro r x y h
  have hy : null ≤ deg r y := hNull r y
  have hxy : deg r y < deg r x := hExceed r x y h
  exact hPos r x (lt_of_le_of_lt hy hxy)

/-- From any bearer of being, climb by "more in being": the climb cannot go on
forever, so it ends at a bearer that nothing exceeds in being. Grades give a
first bearer, since what is more a being than something is a being. -/
theorem gradesAtBeingFromNoInfiniteAscent {B R : Type}
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R)
    (hWF : NoInfiniteAscentInBeing MoreIn esse)
    (hMore : MoreSuchHasThePerfectionReading InAct MoreIn)
    (hEM : ExcludedMiddle) :
    GradesToMaximumAtBeing InAct MoreIn esse := by
  intro ⟨x0, y0, h0⟩
  have climb : ∀ x, InAct x esse → ∃ n, IsMaximumIn InAct MoreIn esse n := by
    intro x
    induction x using hWF.induction with
    | h x ih =>
      intro hx
      cases hEM (∃ y, MoreIn esse y x) with
      | inl hUp =>
        obtain ⟨y, hy⟩ := hUp
        exact ih y hy (hMore esse y x hy)
      | inr hTop =>
        exact ⟨x, hx, fun y hy => hTop ⟨y, hy⟩⟩
  exact climb x0 (hMore esse x0 y0 h0)

/-- On the order by approach, with strict primacy, the primary is a maximum in
being, whatever grades there are. -/
theorem gradesAtBeingFromApproach {B R D : Type} [Preorder D]
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R)
    (near : B → D) (p : B)
    (hApproach : ApproachToPrimaryReading InAct MoreIn esse near p)
    (hStrict : StrictPrimacyReading near p) :
    GradesToMaximumAtBeing InAct MoreIn esse :=
  fun _ => ⟨p, hApproach.isMaximumIn_primary hStrict⟩

/-- Whatever is God is the primary of being, and on the order by approach with
strict primacy the primary is maximal in being. -/
theorem godMaximalFromPrimaryOfBeing {B R D : Type} [Preorder D]
    (IsGod : B → Prop) (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (esse : R) (near : B → D) (p : B)
    (hPrimary : GodIsThePrimaryOfBeing IsGod p)
    (hApproach : ApproachToPrimaryReading InAct MoreIn esse near p)
    (hStrict : StrictPrimacyReading near p) :
    GodIsMaximalInBeing IsGod InAct MoreIn esse := by
  intro g hg
  have hgp : g = p := hPrimary g hg
  subst hgp
  exact hApproach.isMaximumIn_primary hStrict

/-- Strict comparison of degrees transported along an order-matching map. -/
theorem lt_transport {B D E : Type} [Preorder D] [Preorder E]
    {value : B → D} {near : B → E} (h : AsMuchAsItApproaches value near)
    (x y : B) : value x < value y ↔ near x < near y := by
  constructor
  · intro hv
    have hle : value x ≤ value y := le_of_lt hv
    have hnot : ¬ value y ≤ value x := not_le_of_gt hv
    exact lt_of_le_not_ge ((h x y).1 hle) (fun hn => hnot ((h y x).2 hn))
  · intro hn
    have hle : near x ≤ near y := le_of_lt hn
    have hnot : ¬ near y ≤ near x := not_le_of_gt hn
    exact lt_of_le_not_ge ((h x y).2 hle) (fun hv => hnot ((h y x).1 hv))

/-- Being more such goes with approaching the primary more nearly, and the
represented degrees are ordered as the approach; so, among bearers, being more
such goes with a strictly higher represented degree. -/
theorem strictCalibrationFromApproachMeasure {Degree E : Type} [Preorder Degree]
    [Preorder E] (f : Frame Degree) (near : f.Being → E) (p : f.Being)
    (hApproach : ApproachToPrimaryReading f.InAct f.MoreIn f.selected near p)
    (hMeasure : AsMuchAsItApproaches f.value near) :
    StrictDegreeCalibration f := by
  intro x y _ _
  exact Iff.trans (hApproach.2 x y) (lt_transport hMeasure y x).symm

/-- Comparable bearers are directed: the higher of the two bounds both. -/
theorem directedFromComparableDegrees {Degree : Type} [Preorder Degree]
    (f : Frame Degree) (hComp : BearerDegreesComparable f) :
    DirectedBearers f := by
  intro x y hx hy
  cases hComp x y hx hy with
  | inl hxy => exact ⟨y, hy, hxy, le_refl _⟩
  | inr hyx => exact ⟨x, hx, le_refl _, hyx⟩

/-- A bearer at the greatest degree bounds every pair of bearers. -/
theorem directedFromGreatestBearer {Degree : Type} [Preorder Degree]
    (f : Frame Degree) (hTop : SomeBearerHasGreatestDegree f) :
    DirectedBearers f := by
  intro x y hx hy
  obtain ⟨m, hm, hGreatest⟩ := hTop
  exact ⟨m, hm, hGreatest.2 ⟨x, hx, rfl⟩, hGreatest.2 ⟨y, hy, rfl⟩⟩

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
  intro m hm
  cases hEM (m = p) with
  | inl hmp =>
    subst hmp
    exact hOrdered.causesAllInGenus hOthers
  | inr hne =>
    have hlt : value m < value p := hStrict m hne
    have hle : value p ≤ value m := hm.2.2 ⟨p, hApproach.1, rfl⟩
    exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl _)

/-- A greatest-degree bearer is maximal: whatever exceeded it would be a bearer
(more such has the perfection) at a strictly higher degree (calibration), above
the greatest. The maximal-in-genus principle then makes it the cause of all. -/
theorem greatestCausesFromMaximalPrinciple {Degree : Type} [Preorder Degree]
    (f : Frame Degree)
    (hMax : MaximumInGenusCausesAllInGenusReading f.InAct f.MoreIn f.CausesIn)
    (hMore : MoreSuchHasThePerfectionReading f.InAct f.MoreIn)
    (hCal : StrictDegreeCalibration f) :
    GreatestDegreeCausesAllInGenusReading f.InAct f.CausesIn f.selected f.value := by
  intro m hm
  refine hMax f.selected m ⟨hm.1, fun y hy => ?_⟩
  have hyb : f.InAct y f.selected := hMore f.selected y m hy
  have hlt : f.value m < f.value y := (hCal y m hyb hm.1).1 hy
  have hle : f.value y ≤ f.value m := hm.2.2 ⟨y, hyb, rfl⟩
  exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl _)

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
  intro r m hmax
  refine hGreatest r m ⟨hmax.1, ⟨m, hmax.1, rfl⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨z, hz, hxz, hmz⟩ := hDir r x m hx hmax.1
  have hzm : deg r z ≤ deg r m := by
    cases hEM (deg r z ≤ deg r m) with
    | inl h => exact h
    | inr h =>
      exact absurd (hExcess r z m hz hmax.1 (lt_of_le_not_ge hmz h)) (hmax.2 z)
  exact le_trans hxz hzm

/-- Truth goes with intelligibility, and intelligibility with being; so truth
goes with being, both in having and in the comparative. -/
theorem asToBeingSoToTruthFromIntelligibility {E R : Type}
    (Has : E → R → Prop) (MoreIn : R → E → E → Prop) (truth being intel : R)
    (hTruth : TruthOfThingsIsIntelligibility Has MoreIn truth intel)
    (hBeing : IntelligibilityProportionedToBeing Has MoreIn intel being) :
    AsToBeingSoToTruthReading Has MoreIn truth being :=
  ⟨fun x => Iff.trans (hTruth.1 x) (hBeing.1 x),
   fun x y => Iff.trans (hTruth.2 x y) (hBeing.2 x y)⟩

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
  have hOrder : ∀ x y, MoreIn r x y ↔ near y < near x :=
    fun x y => Iff.trans (hCal x y) (lt_transport hMeasure y x)
  refine ⟨?_, hOrder⟩
  obtain ⟨x, y, hxy⟩ := hGrades
  have hx : InAct x r := hMore r x y hxy
  cases hEM (x = p) with
  | inl hxp => exact hxp ▸ hx
  | inr hne => exact hMore r p x ((hOrder p x).2 (hStrict x hne))

/-! ## Controls -/

namespace Controls
open TruthCore.Causality.Round3FourthWay.Control

/-- Unfold the batch vocabulary so that `decide` can evaluate a finite model. -/
local macro "r3unfold" : tactic => `(tactic| (
    try delta TruthCore.Causality.Round3FourthWay.MoreInExceedsDegree
    try delta TruthCore.Causality.Round3FourthWay.NoDegreeBelowNull
    try delta TruthCore.Causality.Round3FourthWay.AboveNullDegreeHasThePerfection
    try delta TruthCore.Causality.Round3FourthWay.DegreeExcessAmongBearersIsMoreIn
    try delta TruthCore.Causality.Round3FourthWay.BearerDegreesDirectedInEveryGenus
    try delta TruthCore.Causality.Round3FourthWay.GradesFoundInBeing
    try delta TruthCore.Causality.Round3FourthWay.AsMuchAsItApproaches
    try delta TruthCore.Causality.Round3FourthWay.MoreInMatchesDegreeEverywhere
    try delta TruthCore.Causality.Round3FourthWay.GodIsThePrimaryOfBeing
    try delta TruthCore.Causality.Round3FourthWay.BearerDegreesComparable
    try delta TruthCore.Causality.Round3FourthWay.TruthOfThingsIsIntelligibility
    try delta TruthCore.Causality.Round3FourthWay.IntelligibilityProportionedToBeing
    try delta TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading
    try delta TruthCore.Causality.DirectEsseRootUniquenessAtBeing.GradesToMaximumAtBeing
    try delta TruthCore.Latin.Aquinas.SummaTheologiae.ApproachToPrimaryReading
    try delta TruthCore.Latin.Aquinas.SummaTheologiae.StrictPrimacyReading
    try delta TruthCore.Case.Catholicism.GodIsMaximalInBeing
    try delta TruthCore.Causality.MaximumDefinitionFork.StrictDegreeCalibration
    try delta TruthCore.Causality.MaximumDefinitionFork.DirectedBearers
    try delta TruthCore.Latin.Aquinas.SummaTheologiae.OrderedToPrimaryAsCauseReading
    try delta TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading
    try delta TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInGenusCausesAllInGenusReading
    try delta TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus
    try delta TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn
    try delta TruthCore.Greek.Aristotle.Metaphysics.AsToBeingSoToTruthReading))

theorem greatest_of_le {B R D : Type} [Preorder D] {InAct : B → R → Prop} {r : R}
    {value : B → D} {m : B} (hm : InAct m r) (h : ∀ x, InAct x r → value x ≤ value m) :
    GreatestDegreeBearer InAct r value m :=
  ⟨hm, ⟨m, hm, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact h x hx⟩

theorem val2_greatest_true : GreatestDegreeBearer all () val2 true :=
  greatest_of_le trivial (fun x _ => by cases x <;> decide)

theorem val2_greatest_eq {m : Bool} (hm : GreatestDegreeBearer all () val2 m) : m = true := by
  cases m with
  | true => rfl
  | false => exact absurd (hm.2.2 ⟨true, trivial, rfl⟩) (by decide)

theorem greatest_fromTrue : GreatestDegreeCausesAllInGenusReading all fromTrue () val2 := by
  intro m hm _ _ _
  exact val2_greatest_eq hm

theorem wf_up : NoInfiniteAscentInBeing up () := by
  have accTrue : Acc (fun y x => up () y x) true :=
    Acc.intro true (fun _ h => Bool.noConfusion h.2)
  have accFalse : Acc (fun y x => up () y x) false :=
    Acc.intro false (fun y h => by obtain ⟨rfl, _⟩ := h; exact accTrue)
  exact ⟨fun b => match b with
    | true => accTrue
    | false => accFalse⟩

theorem moreSuch_omit_hExceed : moreSuch.omit_hExceed := by
  delta moreSuch.omit_hExceed; r3unfold; decide
theorem moreSuch_omit_hNull : moreSuch.omit_hNull := by
  delta moreSuch.omit_hNull; r3unfold; decide
theorem moreSuch_omit_hPos : moreSuch.omit_hPos := by
  delta moreSuch.omit_hPos; r3unfold; decide

theorem gradesAscent_omit_hWF : gradesAscent.omit_hWF := by
  refine ⟨fun hWF => ?_, fun _ _ _ _ => trivial, fun h => ?_⟩
  · exact WellFounded.induction hWF (C := fun _ => False) 0
      (fun x ih => ih (x + 1) (Nat.lt_succ_self x))
  · obtain ⟨n, _, hn⟩ := h ⟨1, 0, Nat.zero_lt_one⟩
    exact hn (n + 1) (Nat.lt_succ_self n)

theorem gradesAscent_omit_hMore : gradesAscent.omit_hMore := by
  refine ⟨wf_up, ?_, ?_⟩ <;> r3unfold <;> decide

theorem gradesApproach_omit_hApproach : gradesApproach.omit_hApproach := by
  delta gradesApproach.omit_hApproach; r3unfold; decide
theorem gradesApproach_omit_hStrict : gradesApproach.omit_hStrict := by
  delta gradesApproach.omit_hStrict; r3unfold; decide

theorem godPrimary_omit_hPrimary : godPrimary.omit_hPrimary := by
  delta godPrimary.omit_hPrimary; r3unfold; decide
theorem godPrimary_omit_hApproach : godPrimary.omit_hApproach := by
  delta godPrimary.omit_hApproach; r3unfold; decide
theorem godPrimary_omit_hStrict : godPrimary.omit_hStrict := by
  delta godPrimary.omit_hStrict; r3unfold; decide

theorem calibration_omit_hApproach : calibration.omit_hApproach := by
  delta calibration.omit_hApproach; r3unfold; decide
theorem calibration_omit_hMeasure : calibration.omit_hMeasure := by
  delta calibration.omit_hMeasure; r3unfold; decide

theorem tf_not_le_ft : ¬ ((1, 0) : Nat × Nat) ≤ (0, 1) := fun h => absurd h.1 (by decide)
theorem ft_not_le_tf : ¬ ((0, 1) : Nat × Nat) ≤ (1, 0) := fun h => absurd h.2 (by decide)

theorem not_directed_incomparable :
    ¬ DirectedBearers (boolFrame (Nat × Nat) all flat noCause incomparableValue) := by
  intro h
  obtain ⟨z, _, h1, h2⟩ := h true false trivial trivial
  cases z with
  | true => exact ft_not_le_tf h2
  | false => exact tf_not_le_ft h1

theorem directed_omit_hComp : directed.omit_hComp := by
  refine ⟨fun h => ?_, not_directed_incomparable⟩
  cases h true false trivial trivial with
  | inl h1 => exact tf_not_le_ft h1
  | inr h2 => exact ft_not_le_tf h2

theorem directed_omit_hTop : directed.omit_hTop := by
  refine ⟨fun ⟨m, _, hm⟩ => ?_, not_directed_incomparable⟩
  cases m with
  | true => exact ft_not_le_tf (hm.2 ⟨false, trivial, rfl⟩)
  | false => exact tf_not_le_ft (hm.2 ⟨true, trivial, rfl⟩)

theorem greatestOrdered_omit_hApproach : greatestOrdered.omit_hApproach := by
  refine ⟨fun h => absurd h.1 (by decide), ?_, ?_, ?_, fun h => ?_⟩
  · r3unfold; decide
  · r3unfold; decide
  · r3unfold; decide
  · have hg : GreatestDegreeBearer optIn () optValue .a :=
      greatest_of_le rfl (fun x hx => by
        cases x
        · exact absurd hx (by decide)
        · decide
        · decide)
    exact absurd (h .a hg .b (by decide) rfl) (by decide)

theorem greatestOrdered_omit_hStrict : greatestOrdered.omit_hStrict := by
  refine ⟨?_, ?_, ?_, ?_, fun h => ?_⟩
  · r3unfold; decide
  · r3unfold; decide
  · r3unfold; decide
  · r3unfold; decide
  · have hg : GreatestDegreeBearer all () zero false :=
      greatest_of_le trivial (fun _ _ => Nat.le_refl 0)
    exact absurd (h false hg true (by decide) trivial) (by decide)

theorem greatestOrdered_omit_hOrdered : greatestOrdered.omit_hOrdered := by
  refine ⟨?_, ?_, ?_, ?_, fun h => h true val2_greatest_true false (by decide) trivial⟩
  · r3unfold; decide
  · r3unfold; decide
  · r3unfold; decide
  · r3unfold; decide

theorem greatestOrdered_omit_hOthers : greatestOrdered.omit_hOthers := by
  refine ⟨?_, ?_, ?_, ?_, fun h => h true val2_greatest_true false (by decide) trivial⟩
  · r3unfold; decide
  · r3unfold; decide
  · r3unfold; decide
  · r3unfold; decide

theorem greatestMaximal_omit_hMax : greatestMaximal.omit_hMax := by
  refine ⟨?_, ?_, ?_, fun h => h true val2_greatest_true false (by decide) trivial⟩
  · r3unfold; decide
  · r3unfold; decide
  · r3unfold; decide

theorem greatestMaximal_omit_hMore : greatestMaximal.omit_hMore := by
  refine ⟨?_, ?_, ?_, fun h => ?_⟩
  · r3unfold; decide
  · r3unfold; decide
  · r3unfold; decide
  · have hg : GreatestDegreeBearer optIn () optLow .a :=
      greatest_of_le rfl (fun x hx => by
        cases x
        · exact absurd hx (by decide)
        · decide
        · decide)
    exact h .a hg .b (by decide) rfl

theorem greatestMaximal_omit_hCal : greatestMaximal.omit_hCal := by
  refine ⟨?_, ?_, ?_, fun h => ?_⟩
  · r3unfold; decide
  · r3unfold; decide
  · r3unfold; decide
  · have hg : GreatestDegreeBearer all () zero true :=
      greatest_of_le trivial (fun _ _ => Nat.le_refl 0)
    exact absurd (h true hg false (by decide) trivial) (by decide)

theorem maximumEvery_omit_hGreatest : maximumEvery.omit_hGreatest := by
  refine ⟨fun h => h () true val2_greatest_true false (by decide) trivial, ?_, ?_, ?_⟩
  · r3unfold; decide
  · r3unfold; decide
  · r3unfold; decide

theorem maximumEvery_omit_hExcess : maximumEvery.omit_hExcess := by
  refine ⟨fun r => ?_, ?_, ?_, ?_⟩
  · cases r; exact greatest_fromTrue
  · r3unfold; decide
  · r3unfold; decide
  · r3unfold; decide

theorem maximumEvery_omit_hDir : maximumEvery.omit_hDir := by
  refine ⟨fun r m hm => ?_, fun r x y _ _ h => ?_, fun h => ?_, ?_⟩
  · exfalso
    cases r
    cases m with
    | true => exact ft_not_le_tf (hm.2.2 ⟨false, trivial, rfl⟩)
    | false => exact tf_not_le_ft (hm.2.2 ⟨true, trivial, rfl⟩)
  · exfalso
    cases r
    cases x <;> cases y
    · exact lt_irrefl _ h
    · exact tf_not_le_ft (le_of_lt h)
    · exact ft_not_le_tf (le_of_lt h)
    · exact lt_irrefl _ h
  · obtain ⟨z, _, h1, h2⟩ := h () true false trivial trivial
    cases z with
    | true => exact ft_not_le_tf h2
    | false => exact tf_not_le_ft h1
  · r3unfold; decide

theorem truthIntel_omit_hTruth : truthIntel.omit_hTruth := by
  delta truthIntel.omit_hTruth; r3unfold; decide
theorem truthIntel_omit_hBeing : truthIntel.omit_hBeing := by
  delta truthIntel.omit_hBeing; r3unfold; decide

theorem approach_omit_hCal : approach.omit_hCal := by
  delta approach.omit_hCal; r3unfold; decide
theorem approach_omit_hMeasure : approach.omit_hMeasure := by
  delta approach.omit_hMeasure; r3unfold; decide
theorem approach_omit_hStrict : approach.omit_hStrict := by
  delta approach.omit_hStrict; r3unfold; decide
theorem approach_omit_hMore : approach.omit_hMore := by
  delta approach.omit_hMore; r3unfold; decide
theorem approach_omit_hGrades : approach.omit_hGrades := by
  delta approach.omit_hGrades; r3unfold; decide

theorem witness_holds : witness := by
  refine ⟨?_, ?_, ?_, ?_, wf_up, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨true, val2_greatest_true⟩, ?_, ?_, ?_, greatest_fromTrue, ?_, ?_, ?_,
    fun r => by cases r; exact greatest_fromTrue, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (r3unfold; decide)

end Controls

/-- The batch controls: every omission model and the joint witness. -/
theorem controls : TruthCore.Causality.Round3FourthWay.Control.Certificate :=
  ⟨Controls.moreSuch_omit_hExceed, Controls.moreSuch_omit_hNull, Controls.moreSuch_omit_hPos,
   Controls.gradesAscent_omit_hWF, Controls.gradesAscent_omit_hMore,
   Controls.gradesApproach_omit_hApproach, Controls.gradesApproach_omit_hStrict,
   Controls.godPrimary_omit_hPrimary, Controls.godPrimary_omit_hApproach,
   Controls.godPrimary_omit_hStrict,
   Controls.calibration_omit_hApproach, Controls.calibration_omit_hMeasure,
   Controls.directed_omit_hComp, Controls.directed_omit_hTop,
   Controls.greatestOrdered_omit_hApproach, Controls.greatestOrdered_omit_hStrict,
   Controls.greatestOrdered_omit_hOrdered, Controls.greatestOrdered_omit_hOthers,
   Controls.greatestMaximal_omit_hMax, Controls.greatestMaximal_omit_hMore,
   Controls.greatestMaximal_omit_hCal,
   Controls.maximumEvery_omit_hGreatest, Controls.maximumEvery_omit_hExcess,
   Controls.maximumEvery_omit_hDir,
   Controls.truthIntel_omit_hTruth, Controls.truthIntel_omit_hBeing,
   Controls.approach_omit_hCal, Controls.approach_omit_hMeasure,
   Controls.approach_omit_hStrict, Controls.approach_omit_hMore,
   Controls.approach_omit_hGrades,
   Controls.witness_holds⟩

end TruthCore.Results.Causality.Round3FourthWay
