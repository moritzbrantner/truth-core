import TruthCore.Causality.RootPositiveIntellectWillControl
import TruthCore.Results.Causality.RootPositiveIntellectWill.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer.Solution
namespace TruthCore.Results.Causality.RootPositiveIntellectWillControl
open TruthCore.Causality.RootPositiveIntellectWillControl
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.ConcreteExistentialSupply (graph)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic (ExcludedMiddle)

private theorem background : TransferModelBackground true :=
  TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer.separator.1
private theorem noIncoming (c : TransferRole) : ¬ transferCause true c .source false := by
  intro h
  change (c = .source ∧ TransferRole.source ≠ .source) ∨
    (c = .supporter ∧ TransferRole.source = .recipient) at h
  rcases h with h | h
  · exact h.2 rfl
  · exact TransferRole.noConfusion h.2
private theorem uniqueSource (x : TransferRole) (hx : ActualRoot model false x) :
    x = .source := by
  cases x with
  | source => rfl
  | supporter =>
    exact (hx.2 .source ⟨trivial, trivial, by
      change transferCause true .source .supporter false
      unfold transferCause
      decide⟩).elim
  | producer =>
    exact (hx.2 .source ⟨trivial, trivial, by
      change transferCause true .source .producer false
      unfold transferCause
      decide⟩).elim
  | recipient =>
    exact (hx.2 .source ⟨trivial, trivial, by
      change transferCause true .source .recipient false
      unfold transferCause
      decide⟩).elim

private theorem retained : RetainedInputs := by
  rcases background with ⟨hGenus, _, hBeing, hPreexist, hMaximum, _, _, _, _⟩
  refine ⟨⟨.source, trivial, trivial⟩, ?_, ?_, hGenus false,
    (fun _ _ => trivial), (fun _ _ _ _ h => ⟨trivial, trivial, h⟩),
    (fun _ => ⟨.source, hMaximum⟩), hBeing, hPreexist, (fun _ _ => Iff.rfl),
    TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer.separator.2.2.1,
    ?_, ?_, (fun _ _ _ h => ⟨trivial, trivial, h⟩), ?_, ?_, (fun _ h => h)⟩
  · intro _ hTrap
    have hSource : (graph model false).Source ⟨.source, trivial, trivial⟩ := by
      rintro ⟨c, hc⟩
      exact noIncoming c.val hc
    exact hTrap.1 ⟨.source, trivial, trivial⟩ trivial hSource
  · intro x _ _ hCont
    obtain ⟨_, v, _, hAbsent⟩ := hCont
    exact (hAbsent trivial).elim
  · intro x hx
    change x = TransferRole.producer at hx
    subst x
    refine ⟨.source, by decide, ?_⟩
    change transferCause true .source .producer false
    unfold transferCause
    decide
  · intro x
    refine ⟨fun h => h, ?_⟩
    intro h
    cases x with
    | source => exact (h rfl).elim
    | supporter => exact (h rfl).elim
    | producer => rfl
    | recipient => exact (h rfl).elim
  · intro c x hc hFirst
    have hcs : c = TransferRole.supporter := hc.1
    subst c
    have hPrior : prior .source .supporter := by unfold prior transferCause; decide
    exact TransferRole.noConfusion (hFirst .source hPrior)
  · intro x hNotMatter hRemote
    cases x with
    | source => exact Or.inl rfl
    | supporter => exact (hRemote .producer ⟨rfl, rfl⟩).elim
    | producer => exact (hNotMatter rfl).elim
    | recipient => exact Or.inr rfl

private theorem sourceWitness (hEM : ExcludedMiddle) : SourceWitness := by
  rcases retained with ⟨hPop, hWhole, hDep, hGenus, hExisting, hEsse, hApproach,
    hBeing, hPreexist, hGoodness, hTransfer, hUniting, hKinds, hPrior,
    hNoComponent, hIntellect, hWill⟩
  obtain ⟨n, hPositive, hGood, hIdentity, hSimple, hFirst, hMatter, hRemote, hInt, hWillN⟩ :=
    TruthCore.Results.Causality.RootPositiveIntellectWill.derive
      model false profile transferAct (transferMore true) prior component composite matterForm
      intellect will hPop hWhole hDep hEM hGenus hExisting hEsse hApproach hBeing
      hPreexist hGoodness hTransfer hUniting hKinds hPrior hNoComponent hIntellect hWill
  have hEq := uniqueSource n hPositive.1
  subst n
  exact ⟨hPositive, hGood, hIdentity, hSimple, hFirst, hMatter, hRemote, hInt, hWillN⟩

theorem checks (hEM : ExcludedMiddle) : Control := by
  have hWitness := sourceWitness hEM
  rcases background with ⟨_, _, _, _, _, _, _, hSupporter, hProducer⟩
  refine ⟨TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer.separator,
    retained, hWitness, ⟨.source, hWitness⟩, rfl, ⟨rfl, rfl⟩, ?_, hSupporter, hProducer, ?_⟩
  · change transferCause true .source .producer false
    unfold transferCause
    decide
  · intro hPosterior
    have bad := hPosterior .supporter .producer ⟨rfl, rfl⟩
    exact (by unfold prior transferCause; decide : ¬ prior .supporter .producer) bad
end TruthCore.Results.Causality.RootPositiveIntellectWillControl
