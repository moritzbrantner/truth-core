import TruthCore.Causality.ConstitutiveNatureUniqueness
import TruthCore.Results.Case.Catholicism.Q11NatureUniqueness.Solution
import TruthCore.Results.Causality.PartFreePlurality.Solution
namespace TruthCore.Results.Causality.ConstitutiveNatureUniqueness
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.ConstitutiveNatureUniqueness
open TruthCore.Causality.PartFreePlurality

/-- A conditional completion test, with all applicability and constitutive
premises exposed. Common nature is derived, not assumed. -/
theorem checks {B P R : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop) (InAct : B → R → Prop)
    (suppositum essence : B → P) (content : P → R → Prop)
    (hIndividual : IndividuatingBasisIsIncommunicableReading suppositum)
    (hNature : FirstMoverSuppositumIsNature Moved Moves suppositum essence)
    (hPerfect : FirstUnmovedMoverHasEveryPerfection Moved Moves InAct)
    (hComplete : ConstitutiveContentComplete content)
    (hAgreement : FirstMoverContentAgreesWithAct Moved Moves InAct essence content) :
    AtMostOneFirstUnmovedMover Moved Moves := by
  intro f g hf hg
  have common : ProperGodInstancesHaveCommonNatureReading
      (IsFirstUnmovedMover Moved Moves) essence (essence f) := by
    intro x hx
    apply hComplete
    intro r
    exact (hAgreement x hx r).trans
      ⟨fun _ => hPerfect f hf r, fun _ => hPerfect x hx r⟩ |>.trans (hAgreement f hf r).symm
  exact (TruthCore.Results.Case.Catholicism.Q11NatureUniqueness.godIsOneFromNature
    (IsFirstUnmovedMover Moved Moves) suppositum essence (essence f)
    hIndividual hNature common f hf g hg).symm

theorem controls : Control.Certificate := by
  have nature : FirstMoverSuppositumIsNature moved moves suppositum essence := by
    intro x hx
    have hr := TruthCore.Results.Causality.PartFreePlurality.firstIsRoot x hx
    cases x <;> first | rfl | exact hr.elim
  have agreement : FirstMoverContentAgreesWithAct moved moves inAct essence Control.actContent := by
    intro x hx r
    have hr := TruthCore.Results.Causality.PartFreePlurality.firstIsRoot x hx
    cases x <;> first | exact Iff.rfl | exact hr.elim
  have incomplete : ¬ ConstitutiveContentComplete Control.actContent := by
    intro h
    have eq := h Being.left Being.right (fun _ => Iff.rfl)
    exact Being.noConfusion eq
  have complete : ConstitutiveContentComplete Control.separatingContent := by
    intro p q h
    cases p <;> cases q
    all_goals first
      | rfl
      | exact False.elim ((h .esse).mp trivial)
      | exact False.elim ((h .esse).mpr trivial)
      | exact False.elim ((h .drive).mp trivial)
      | exact False.elim ((h .drive).mpr trivial)
      | exact False.elim ((h .heat).mp trivial)
      | exact False.elim ((h .heat).mpr trivial)
  have misaligned : ¬ FirstMoverContentAgreesWithAct moved moves inAct essence Control.separatingContent := by
    intro h
    exact (h .right TruthCore.Results.Causality.PartFreePlurality.rightFirst .heat).mpr trivial
  exact ⟨TruthCore.Results.Causality.PartFreePlurality.jointControl,
    nature, agreement, incomplete, complete, misaligned⟩

open TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint in
/-- Nonvacuity: the existing OneFirstMover.Joint carrier and motion model admit
all five advertised premises together, with an actual first mover and motion.
The content below is assignment data, not a source-derived real definition. -/
theorem premisesJointlySatisfiable :
    ∃ content : TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.B →
      TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.R → Prop,
      let Moved := TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.movedIn
      let Moves := TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.movesIn
      let Act := TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.inAct
      IndividuatingBasisIsIncommunicableReading
        (fun individual : TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.B => individual) ∧
      FirstMoverSuppositumIsNature Moved Moves (fun individual => individual) (fun individual => individual) ∧
      FirstUnmovedMoverHasEveryPerfection Moved Moves Act ∧
      ConstitutiveContentComplete content ∧
      FirstMoverContentAgreesWithAct Moved Moves Act (fun individual => individual) content ∧
      IsFirstUnmovedMover Moved Moves .g := by
  let content : B → R → Prop := B.rec (motive := fun _ => R → Prop)
    (fun _ => True)
    (R.rec (motive := fun _ => Prop) True False)
    (fun _ => False)
    (R.rec (motive := fun _ => Prop) False True)
  have onlyG : ∀ b, IsFirstUnmovedMover movedIn movesIn b → b = .g := by
    intro b ⟨⟨target, r, hm⟩, hu⟩
    cases b with
    | g => rfl
    | f => exact (hu .other trivial).elim
    | x => exact hm.elim
    | c => exact hm.elim
  have complete : ConstitutiveContentComplete content := by
    intro p q h
    cases p <;> cases q
    all_goals first
      | rfl
      | exact False.elim ((h .heat).mp trivial)
      | exact False.elim ((h .heat).mpr trivial)
      | exact False.elim ((h .other).mp trivial)
      | exact False.elim ((h .other).mpr trivial)
  refine ⟨content, (fun _ _ h => h), (fun _ _ => rfl), ?_, complete, ?_, ?_⟩
  · intro b hb r
    have eq := onlyG b hb
    subst b
    trivial
  · intro b hb r
    have eq := onlyG b hb
    subst b
    cases r <;> exact Iff.rfl
  · exact ⟨⟨.f, .other, trivial⟩, fun _ h => h⟩

/-- The actual open differentiation premise, obtained by contrapositive of the
same constitutive identity account. Classical quantifier extraction is explicit;
no every-perfection assumption or uniqueness conclusion is hidden here. -/
theorem differentiate {B P R : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop) (InAct : B → R → Prop)
    (suppositum essence : B → P) (content : P → R → Prop)
    (hIndividual : IndividuatingBasisIsIncommunicableReading suppositum)
    (hNature : FirstMoverSuppositumIsNature Moved Moves suppositum essence)
    (hComplete : ConstitutiveContentComplete content)
    (hAgreement : FirstMoverContentAgreesWithAct Moved Moves InAct essence content)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    PluralFirstMoversWouldDifferInActReading Moved Moves InAct := by
  intro f g hf hg hne
  rcases hEM (∃ r, (InAct f r ∧ ¬ InAct g r) ∨ (InAct g r ∧ ¬ InAct f r)) with h | hn
  · exact h
  · have same : ∀ r, InAct f r ↔ InAct g r := by
      intro r
      constructor
      · intro ha
        rcases hEM (InAct g r) with hb | hb
        · exact hb
        · exact (hn ⟨r, Or.inl ⟨ha, hb⟩⟩).elim
      · intro hb
        rcases hEM (InAct f r) with ha | ha
        · exact ha
        · exact (hn ⟨r, Or.inr ⟨hb, ha⟩⟩).elim
    have natureEq : essence f = essence g := hComplete _ _ (fun r =>
      (hAgreement f hf r).trans ((same r).trans (hAgreement g hg r).symm))
    exact (hne (hIndividual f g ((hNature f hf).trans
      (natureEq.trans (hNature g hg).symm)))).elim
end TruthCore.Results.Causality.ConstitutiveNatureUniqueness
