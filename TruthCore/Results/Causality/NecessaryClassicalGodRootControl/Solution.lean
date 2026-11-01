import TruthCore.Causality.NecessaryClassicalGodRootControl
import TruthCore.Results.Causality.RootPositiveIntellectWillControl.Solution
import TruthCore.Results.Causality.NecessaryClassicalGodRoot.Solution
namespace TruthCore.Results.Causality.NecessaryClassicalGodRootControl
open TruthCore.Causality.NecessaryClassicalGodRootControl
open TruthCore.Causality.RootPositiveIntellectWillControl
  (model profile prior component composite matterForm intellect will)
open TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)

private theorem maximumIsSource (x : TransferRole)
    (hx : IsMaximumIn profile.InAct (transferMore true) profile.esse x) : x = .source := by
  cases x with
  | source => rfl
  | supporter =>
    exact (hx.2 .source (by unfold transferMore transferRank; decide)).elim
  | producer =>
    exact (hx.2 .source (by unfold transferMore transferRank; decide)).elim
  | recipient =>
    exact (hx.2 .source (by unfold transferMore transferRank; decide)).elim

private theorem retained (hEM : ExcludedMiddle) : RetainedInputs := by
  have hOld := TruthCore.Results.Causality.RootPositiveIntellectWillControl.checks hEM
  have hMaximum := hOld.2.2.1.1.2.2.2.1
  refine ⟨hOld.2.1, (fun _ _ h => h.elim), (fun _ _ h => h.2),
    (fun _ h => h), (fun _ _ => trivial), ?_, ?_, ?_⟩
  · intro x hx _ _ _ _
    exact maximumIsSource x hx
  · intro x hx
    change x = TransferRole.source at hx
    subst x
    exact hMaximum
  · intro x hSimple hPerfect hGood hOne hInfinite hImmutable hEternal hInt hWill
    exact ⟨hSimple, hPerfect, hGood, hOne, hInfinite, hImmutable, hEternal, hInt, hWill⟩

private theorem sourceWitness (hEM : ExcludedMiddle) : SourceWitness := by
  rcases retained hEM with ⟨hOld, hActPrior, hNotBoth, hInfinity, hEternity, hNaming, hMaximal, hSuffice⟩
  rcases hOld with ⟨hPop, hWhole, hDep, hGenus, hExisting, hEsse, hApproach, hBeing,
    hPreexist, hGoodness, hTransfer, hUniting, hKinds, hPrior, hNoComponent, hIntellect, hWill⟩
  obtain ⟨n, hPositive, hIdentity, hFirst, hMatter, hRemote, hGod, hNine, hField⟩ :=
    TruthCore.Results.Causality.NecessaryClassicalGodRoot.derive
      signature model false profile transferAct potency (transferMore true) prior component
      composite matterForm infinite eternal intellect will hPop hWhole hDep hEM hGenus
      hExisting hEsse hApproach hBeing hPreexist hGoodness hTransfer hUniting hKinds hPrior
      hNoComponent hIntellect hWill hActPrior hNotBoth hInfinity hEternity hNaming hMaximal hSuffice
  have hEq : n = TransferRole.source := hGod
  subst n
  exact ⟨hPositive, hIdentity, hFirst, hMatter, hRemote, rfl, hNine, hField⟩

theorem checks (hEM : ExcludedMiddle) : Control := by
  have hSource := sourceWitness hEM
  have hEndpoint : NecessaryClassicalGodRootAt signature model false profile transferAct potency
      (transferMore true) prior component composite matterForm infinite eternal intellect will :=
    ⟨.source, hSource⟩
  refine ⟨TruthCore.Results.Causality.RootPositiveIntellectWillControl.checks hEM,
    retained hEM, hSource, hEndpoint,
    uniqueClassicalGodExists signature model false profile transferAct potency (transferMore true)
      prior component composite matterForm infinite eternal intellect will hEndpoint,
    ?_, (fun _ _ h => h), (fun _ _ _ => trivial), trivial, trivial,
    (fun _ _ => trivial), ?_, ?_, by decide⟩
  · intro g hg g' hg'
    change g = TransferRole.source at hg
    change g' = TransferRole.source at hg'
    exact hg'.trans hg.symm
  · intro h
    exact TransferRole.noConfusion h
  · change transferCause true .source .producer false
    unfold transferCause
    decide
end TruthCore.Results.Causality.NecessaryClassicalGodRootControl
