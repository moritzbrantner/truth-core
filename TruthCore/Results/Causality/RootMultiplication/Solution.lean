import TruthCore.Causality.RootMultiplication
import TruthCore.Results.Causality.ConstitutiveNatureUniqueness.Solution
namespace TruthCore.Results.Causality.RootMultiplication
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.ConstitutiveNatureUniqueness
open TruthCore.Causality.RootMultiplication
open TruthCore.Causality.RootMultiplication.Control
open TruthCore.Causality.PartFreePlurality

/-- With individuation, the adapter and every-perfection: distinct first movers
have one act profile and different natures, and at-most-one is equivalent to
each nature condition. The equivalences say that, given these three, either
nature condition is not independent of uniqueness. -/
theorem residue {B P R : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop) (InAct : B → R → Prop)
    (suppositum essence : B → P)
    (hIndividual : IndividuatingBasisIsIncommunicableReading suppositum)
    (hNature : FirstMoverSuppositumIsNature Moved Moves suppositum essence)
    (hPerfect : FirstUnmovedMoverHasEveryPerfection Moved Moves InAct) :
    PluralityResidue Moved Moves InAct essence := by
  have same : ∀ f g, IsFirstUnmovedMover Moved Moves f → IsFirstUnmovedMover Moved Moves g →
      SameActProfile InAct f g := fun f g hf hg r =>
    ⟨fun _ => hPerfect g hg r, fun _ => hPerfect f hf r⟩
  have ofNature : ∀ f g, IsFirstUnmovedMover Moved Moves f → IsFirstUnmovedMover Moved Moves g →
      essence f = essence g → f = g := fun f g hf hg h =>
    hIndividual f g ((hNature f hf).trans (h.trans (hNature g hg).symm))
  refine ⟨fun f g hf hg hne => ⟨same f g hf hg, fun h => hne (ofNature f g hf hg h)⟩,
    ⟨fun h f g hf hg _ => congrArg essence (h f g hf hg),
      fun h f g hf hg => ofNature f g hf hg (h f g hf hg (same f g hf hg))⟩,
    ⟨fun h f g hf hg => congrArg essence (h f g hf hg),
      fun h f g hf hg => ofNature f g hf hg (h f g hf hg)⟩⟩

/-- The bridge's proof does not use every-perfection: simplicity and first-being
make first movers unlimited, the bridge gives common nature, and the imported Q11
theorem gives identity. Conditional on the OPEN bridge. -/
theorem uniqueFromUnlimitedNature {B P R : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Body MatterForm Composite : B → Prop) (Prior : B → B → Prop)
    (suppositum essence esse : B → P)
    (hIndividual : IndividuatingBasisIsIncommunicableReading suppositum)
    (hNature : FirstMoverSuppositumIsNature Moved Moves suppositum essence)
    (hSimple : FirstUnmovedMoverIsSimpleReading Moved Moves Body MatterForm Composite essence esse)
    (hFirst : FirstUnmovedMoverIsFirstBeing Moved Moves Prior)
    (hBridge : UnlimitedBeingsShareNature Composite Prior essence esse) :
    AtMostOneFirstUnmovedMover Moved Moves := by
  have unlimited : ∀ f, IsFirstUnmovedMover Moved Moves f →
      ¬ HasLimitingPrinciple Composite Prior essence esse f := by
    intro f hf h
    have hs := hSimple f hf
    rcases h with h | h | ⟨y, hne, hp⟩
    · exact hs.2.2.2 h
    · exact hs.2.2.1 h
    · exact hne (hFirst f hf y hp)
  intro f g hf hg
  have common : ProperGodInstancesHaveCommonNatureReading
      (IsFirstUnmovedMover Moved Moves) essence (essence f) :=
    fun x hx => hBridge x f (unlimited x hx) (unlimited f hf)
  exact (TruthCore.Results.Case.Catholicism.Q11NatureUniqueness.godIsOneFromNature
    (IsFirstUnmovedMover Moved Moves) suppositum essence (essence f)
    hIndividual hNature common f hf g hg).symm

private abbrev lf := TruthCore.Results.Causality.PartFreePlurality.leftFirst
private abbrev rf := TruthCore.Results.Causality.PartFreePlurality.rightFirst
private abbrev isRoot := TruthCore.Results.Causality.PartFreePlurality.firstIsRoot
private abbrev fb := TruthCore.Results.Causality.PartFreePlurality.firstBeing

theorem notAtMostOne : ¬ atMostOne :=
  TruthCore.Results.Causality.PartFreePlurality.notUnique

theorem rootSimple : FirstUnmovedMoverIsSimpleReading moved moves body matterForm composite essence esse :=
  (TruthCore.Results.Causality.PartFreePlurality.simplicity).2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem constantSimple : FirstUnmovedMoverIsSimpleReading moved moves body matterForm composite constant constant :=
  fun x hx => have h := rootSimple x hx; ⟨h.1, h.2.1, fun e => e rfl, h.2.2.2⟩

theorem nature : FirstMoverSuppositumIsNature moved moves suppositum essence := by
  intro x hx
  have hr := isRoot x hx
  cases x <;> first | rfl | exact hr.elim

theorem individual : IndividuatingBasisIsIncommunicableReading suppositum := fun _ _ h => h

theorem limitedIffNotRoot (x : Being) : ¬ limited x ↔ root x := by
  cases x with
  | left =>
    refine ⟨fun _ => trivial, fun _ h => ?_⟩
    rcases h with h | h | ⟨y, _, hp⟩
    · rcases h with ⟨p, hc, _⟩; exact Nat.not_lt_zero _ hc.2
    · exact h rfl
    · exact Nat.not_lt_zero _ hp
  | right =>
    refine ⟨fun _ => trivial, fun _ h => ?_⟩
    rcases h with h | h | ⟨y, _, hp⟩
    · rcases h with ⟨p, hc, _⟩; exact Nat.not_lt_zero _ hc.2
    · exact h rfl
    · exact Nat.not_lt_zero _ hp
  | constituent =>
    exact ⟨fun h => (h (Or.inr (Or.inr ⟨.left, Being.noConfusion, by change 0 < 1; decide⟩))).elim,
      fun h => h.elim⟩
  | instrument =>
    exact ⟨fun h => (h (Or.inr (Or.inr ⟨.left, Being.noConfusion, by change 0 < 2; decide⟩))).elim,
      fun h => h.elim⟩
  | effect =>
    exact ⟨fun h => (h (Or.inr (Or.inr ⟨.left, Being.noConfusion, by change 0 < 3; decide⟩))).elim,
      fun h => h.elim⟩

theorem rootsSameAct : SameActProfile inAct Being.left .right := fun _ => Iff.rfl

theorem survivingRival : SurvivingRival := by
  refine ⟨TruthCore.Results.Causality.ConstitutiveNatureUniqueness.controls, ?_, ?_, limitedIffNotRoot⟩
  · intro h
    exact Being.noConfusion (h .left .right lf rf rootsSameAct)
  · intro h
    exact Being.noConfusion (h .left .right
      ((limitedIffNotRoot .left).mpr trivial) ((limitedIffNotRoot .right).mpr trivial))

theorem omissionControls : OmissionControls := by
  refine ⟨⟨?_, ?_, constantSimple, fb, fun _ _ _ _ => rfl, notAtMostOne⟩,
    ⟨individual, ?_, constantSimple, fb, fun _ _ _ _ => rfl, notAtMostOne⟩,
    ⟨individual, nature, ?_, fb, ?_, notAtMostOne⟩,
    ⟨individual, nature, rootSimple, ?_, ?_, notAtMostOne⟩⟩
  · intro h
    exact Being.noConfusion (h .left .right rfl)
  · intro _ _; rfl
  · intro h
    exact Being.noConfusion (h .right rf)
  · intro h
    exact (h .left lf).2.2.2 trivial
  · intro x _ h
    exact (h (Or.inl trivial)).elim
  · intro h
    exact Being.noConfusion (h .left lf .right Being.noConfusion)
  · intro x _ hx
    refine (hx ?_).elim
    cases x with
    | left => exact Or.inr (Or.inr ⟨.right, Being.noConfusion, Being.noConfusion⟩)
    | right => exact Or.inr (Or.inr ⟨.left, Being.noConfusion, Being.noConfusion⟩)
    | constituent => exact Or.inr (Or.inr ⟨.left, Being.noConfusion, Being.noConfusion⟩)
    | instrument => exact Or.inr (Or.inr ⟨.left, Being.noConfusion, Being.noConfusion⟩)
    | effect => exact Or.inr (Or.inr ⟨.left, Being.noConfusion, Being.noConfusion⟩)

theorem hornWitnesses : HornWitnesses :=
  ⟨lf, rf, Being.noConfusion, fun h => (h .heat).mp trivial,
    ⟨rootsSameAct, rfl⟩, ⟨rootsSameAct, Being.noConfusion⟩⟩

theorem forkCoverage : ForkCoverage := by
  intro B P R InAct essence f g hEM
  rcases hEM (SameActProfile InAct f g) with hs | hs
  · rcases hEM (essence f = essence g) with he | he
    · exact Or.inr (Or.inl ⟨hs, he⟩)
    · exact Or.inr (Or.inr ⟨hs, he⟩)
  · exact Or.inl hs

theorem contentBundleStrict : ContentBundleStrict := by
  refine ⟨?_, fun _ _ _ _ _ => rfl, ?_⟩
  · intro B P R Moved Moves InAct essence content hComplete hAgreement f g hf hg hs
    exact hComplete _ _ fun r => (hAgreement f hf r).trans ((hs r).trans (hAgreement g hg r).symm)
  · intro content h
    exact (h .right rf .heat).mp ((h .left lf .heat).mpr trivial)

open TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint in
theorem onlyG (b : B) (h : IsFirstUnmovedMover movedIn movesIn b) : b = .g := by
  rcases h with ⟨⟨target, r, hm⟩, hu⟩
  cases b with
  | g => rfl
  | f => exact (hu .other trivial).elim
  | x => exact hm.elim
  | c => exact hm.elim

open TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint in
theorem gFirst : IsFirstUnmovedMover movedIn movesIn .g :=
  ⟨⟨.f, .other, trivial⟩, fun _ h => h⟩

open TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint in
theorem bridgeExceedsUniqueness : BridgeExceedsUniqueness := by
  have cUnlimited : ¬ HasLimitingPrinciple (fun _ => False) jointPrior
      (fun a : B => a) (fun a => a) .c := by
    intro h
    rcases h with h | h | ⟨y, _, _, hx⟩
    · exact h
    · exact h rfl
    · rcases hx with hx | hx <;> exact B.noConfusion hx
  have gUnlimited : ¬ HasLimitingPrinciple (fun _ => False) jointPrior
      (fun a : B => a) (fun a => a) .g := by
    intro h
    rcases h with h | h | ⟨y, _, _, hx⟩
    · exact h
    · exact h rfl
    · rcases hx with hx | hx <;> exact B.noConfusion hx
  refine ⟨fun _ _ h => h, fun _ _ => rfl, fun _ _ => ⟨id, id, fun e => e rfl, id⟩, ?_,
    fun a b ha hb => (onlyG a ha).trans (onlyG b hb).symm, gFirst, ?_, cUnlimited, ?_⟩
  · intro a ha y hy
    have hag := onlyG a ha
    subst hag
    rcases hy.2 with h | h <;> exact B.noConfusion h
  · exact fun h => (h.1.elim fun _ ⟨_, hm⟩ => hm)
  · intro h
    exact B.noConfusion (h .c .g cUnlimited gUnlimited)

open TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint in
theorem positiveWitness : PositiveWitness := by
  refine ⟨fun _ _ h => h, fun _ _ => rfl, fun _ _ => ⟨id, id, fun e => e rfl, id⟩, ?_, ?_, gFirst⟩
  · intro a ha y hy
    have hag := onlyG a ha
    subst hag
    exact (hy.2 rfl).elim
  · have limitedAll : ∀ a : B, a ≠ .g →
        HasLimitingPrinciple (fun _ => False) fullPrior (fun a : B => a) (fun a => a) a :=
      fun a ha => Or.inr (Or.inr ⟨.g, fun e => ha e.symm, rfl, ha⟩)
    intro p q hp hq
    have ex : p = .g := by
      cases p with
      | g => rfl
      | f => exact (hp (limitedAll .f B.noConfusion)).elim
      | x => exact (hp (limitedAll .x B.noConfusion)).elim
      | c => exact (hp (limitedAll .c B.noConfusion)).elim
    have ey : q = .g := by
      cases q with
      | g => rfl
      | f => exact (hq (limitedAll .f B.noConfusion)).elim
      | x => exact (hq (limitedAll .x B.noConfusion)).elim
      | c => exact (hq (limitedAll .c B.noConfusion)).elim
    exact ex.trans ey.symm

theorem controls : TruthCore.Causality.RootMultiplication.Control.Certificate :=
  ⟨survivingRival, omissionControls, hornWitnesses, forkCoverage, contentBundleStrict,
    bridgeExceedsUniqueness, positiveWitness⟩

end TruthCore.Results.Causality.RootMultiplication
