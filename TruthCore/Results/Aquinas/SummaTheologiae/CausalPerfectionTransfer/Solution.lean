import TruthCore.Case.Catholicism.CausalPerfectionTransfer
import TruthCore.Results.Aquinas.SummaTheologiae.AtMostOneMaximeEns.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article8
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question5.Article1
import TruthCore.Case.Catholicism.StageTwo

namespace TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic.StrengthComparison
open TruthCore.Greek.Aristotle.Metaphysics
theorem implication {Being Respect : Type} [DecidableEq Being]
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    [DecidablePred (CausesAllInGenus InAct CausesIn esse)]
    (h : CauseOfBeingCausesEveryPerfection InAct CausesIn esse) :
    UniversalCauseTransfersPerfections InAct CausesIn esse := by
  intro c _ x r _ hEsse hAct
  exact h c x r hEsse hAct

theorem deltaForward {Being Respect : Type} [DecidableEq Being]
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    [DecidablePred (CausesAllInGenus InAct CausesIn esse)]
    (h : CauseOfBeingCausesEveryPerfection InAct CausesIn esse) :
    ResidualPerfectionTransfer InAct CausesIn esse := by
  exact ⟨fun c _ x r => h c x r, fun c r => h c c r⟩

theorem reconstruction {Being Respect : Type} [DecidableEq Being]
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    [DecidablePred (CausesAllInGenus InAct CausesIn esse)]
    (h : UniversalCauseTransfersPerfections InAct CausesIn esse)
    (hRest : ResidualPerfectionTransfer InAct CausesIn esse) :
    CauseOfBeingCausesEveryPerfection InAct CausesIn esse := by
  intro c x r hEsse hAct
  by_cases hAll : CausesAllInGenus InAct CausesIn esse c
  · by_cases hSame : x = c
    · subst x
      exact hRest.2 c r hEsse hAct
    · exact h c hAll x r hSame hEsse hAct
  · exact hRest.1 c hAll x r hEsse hAct

theorem equivalence {Being Respect : Type} [DecidableEq Being]
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    [DecidablePred (CausesAllInGenus InAct CausesIn esse)] :
    CauseOfBeingCausesEveryPerfection InAct CausesIn esse ↔
      UniversalCauseTransfersPerfections InAct CausesIn esse ∧
      ResidualPerfectionTransfer InAct CausesIn esse := by
  exact ⟨fun h => ⟨implication InAct CausesIn esse h, deltaForward InAct CausesIn esse h⟩,
    fun h => reconstruction InAct CausesIn esse h.1 h.2⟩

attribute [local instance] transferFourForallDecidable

private instance boolForallDecidable (p : Bool → Prop) [DecidablePred p] :
    Decidable (∀ b, p b) := decidable_of_iff (p false ∧ p true) Bool.forall_bool.symm

private instance causeDecidable (b : Bool) (c x : TransferRole) (r : Bool) :
    Decidable (transferCause b c x r) := by
  cases r <;> cases b <;> unfold transferCause <;> infer_instance

private instance moreDecidable (b r : Bool) (c x : TransferRole) :
    Decidable (transferMore b r c x) := by
  unfold transferMore
  infer_instance

private instance backgroundDecidable (b : Bool) : Decidable (TransferModelBackground b) := by
  unfold TransferModelBackground MaximumInGenusCausesAllInGenusReading CausesAllInGenus
    CauseOfQualityInAnotherIsMoreSuchReading PerfectionsOfEffectPreexistInCauseReading
    IsMaximumIn transferAct
  infer_instance

private instance universalTransferDecidable (b : Bool) :
    Decidable (UniversalCauseTransfersPerfections transferAct (transferCause b) false) := by
  unfold UniversalCauseTransfersPerfections CausesAllInGenus transferAct
  infer_instance

theorem separator : ConcurrentTransferSeparates := by
  refine ⟨?_, True.intro, ?_, ?_⟩
  · decide
  · change UniversalCauseTransfersPerfections transferAct (transferCause true) false
    decide
  · intro h
    have bad := h .supporter .recipient true (by unfold transferCause; decide) True.intro
    exact (by unfold transferCause; decide : ¬ transferCause true .supporter .recipient true) bad

theorem rival : SecondaryOnlyTransferSurvives := by
  refine ⟨?_, ?_⟩
  · decide
  · intro h
    have bad := h .source (by unfold CausesAllInGenus transferAct transferCause; decide)
      .recipient true (by decide) (by unfold transferCause; decide) True.intro
    exact (by unfold transferCause; decide : ¬ transferCause false .source .recipient true) bad

/-- The independently supplied universal esse condition in the reduced nominal
interface licenses the restricted bridge. No God predicate occurs in its scope
condition; remoteness and full naming remain separate open premises. -/
theorem reducedDescription {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (ComponentOf PriorSimply : Being → Being → Prop) (God : Being → Prop)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hTransfer : UniversalCauseTransfersPerfections InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFirstBeing : MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf God) :
    GodNamesTheUniqueMaximeEns InAct MoreIn CausesIn esse God := by
  intro m hMax hCauses hOnly
  have hEvery : CausesEveryPerfectionOfOthers InAct CausesIn m :=
    fun x r hOther hAct => hTransfer m hCauses x r hOther
      (hCauses x hOther (hBeing x r hAct)) hAct
  have hRemote : RemoteFromAll ComponentOf m :=
    fun x hComponent => hNoComponent m x hComponent (hFirstBeing m hMax)
  exact hFull m hMax hCauses hEvery hRemote hOnly

/-- A separate full-description application. The genus premise at esse
establishes universal causal scope before naming m; uniqueness reuses the
existing theorem. No witness is created and no God-to-maximum converse inferred. -/
theorem naming {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (ComponentOf PriorSimply : Being → Being → Prop) (God : Being → Prop)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hTransfer : UniversalCauseTransfersPerfections InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFirstBeing : MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf God) :
    MaximeEnsIsGod InAct MoreIn esse God := by
  have hUnique := AtMostOneMaximeEns.atMostOneMaximeEns
    InAct MoreIn CausesIn esse hGenus hCauseMore hEM
  have hReduced := reducedDescription InAct MoreIn CausesIn esse ComponentOf PriorSimply
    God hBeing hTransfer hNoComponent hFirstBeing hFull
  intro m hMax
  exact hReduced m hMax (hGenus esse m hMax) (fun m' hm' => hUnique m' m hm' hMax)

/-- Universal-scope transfer suffices for the original pointwise goodness
application. God-to-maximality remains an explicit antecedent here; it is never
used to justify pre-naming causal scope in the separate naming theorem. -/
theorem goodness {Being Respect : Type}
    (God : Being → Prop) (InAct GoodIn : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hMaximal : GodIsMaximalInBeing God InAct MoreIn esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hGoodness : GoodnessIsActualityReading GoodIn InAct)
    (hTransfer : UniversalCauseTransfersPerfections InAct CausesIn esse) :
    GodIsSupremelyGood God InAct GoodIn CausesIn esse := by
  intro g hg
  have hMax := hMaximal g hg
  have hCauses := hGenus esse g hMax
  refine ⟨(hGoodness g esse).mpr hMax.1, ?_⟩
  intro x r hOther hAct
  exact hTransfer g hCauses x r hOther (hCauses x hOther (hBeing x r hAct)) hAct

theorem scopeSeparator : Separation concurrentTransferSetting := by
  exact separator.2

theorem exactDelta : PerfectionTransferExactDelta := by
  intro Being Respect _ InAct CausesIn esse _
  exact equivalence InAct CausesIn esse

theorem scopeSeparation : ScopeTransferSeparates := by
  exact scopeSeparator

end TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer
