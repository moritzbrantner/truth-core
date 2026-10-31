import TruthCore.Causality.DirectEsseRootGoodnessOmission
import TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer.Solution
namespace TruthCore.Results.Causality.DirectEsseRootGoodnessOmission
open TruthCore.Causality.DirectEsseRootGoodnessOmission
open TruthCore.Causality.DirectEsseRootPerfectionGoodness
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.ConcreteExistentialSupply (graph)
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)

private theorem background : TransferModelBackground false :=
  TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer.rival.1

private theorem noIncoming (c : TransferRole) : ¬ transferCause false c .source false := by
  intro h
  change (c = .source ∧ TransferRole.source ≠ .source) ∨
    (c = .supporter ∧ TransferRole.source = .recipient) at h
  rcases h with h | h
  · exact h.2 rfl
  · exact TransferRole.noConfusion h.2

private theorem sourceRoot : ActualRoot model false TransferRole.source :=
  ⟨⟨trivial, trivial⟩, fun c h => noIncoming c h.2.2⟩

private theorem uniqueSource (x : TransferRole) (hx : ActualRoot model false x) :
    x = .source := by
  cases x with
  | source => rfl
  | supporter =>
    exact (hx.2 .source ⟨trivial, trivial, by
      change transferCause false .source .supporter false
      unfold transferCause
      decide⟩).elim
  | producer =>
    exact (hx.2 .source ⟨trivial, trivial, by
      change transferCause false .source .producer false
      unfold transferCause
      decide⟩).elim
  | recipient =>
    exact (hx.2 .source ⟨trivial, trivial, by
      change transferCause false .source .recipient false
      unfold transferCause
      decide⟩).elim

private theorem retained : RetainedInputs := by
  rcases background with ⟨hGenus, _, hBeing, hPreexist, hMaximum, _, _, _, _⟩
  refine ⟨⟨.source, trivial, trivial⟩, ?_, ?_, hGenus false,
    (fun _ _ => trivial), (fun _ _ _ _ h => ⟨trivial, trivial, h⟩),
    (fun _ => ⟨.source, hMaximum⟩), hBeing, hPreexist, (fun _ _ => Iff.rfl)⟩
  · intro _ hTrap
    have hSource : (graph model false).Source ⟨.source, trivial, trivial⟩ := by
      rintro ⟨c, hc⟩
      exact noIncoming c.val hc
    exact hTrap.1 ⟨.source, trivial, trivial⟩ trivial hSource
  · intro x _ _ hCont
    obtain ⟨_, v, _, hAbsent⟩ := hCont
    exact (hAbsent trivial).elim

private theorem sourcePerfect : PerfectRootAt model false transferAct
    (transferMore false) false TransferRole.source := by
  rcases background with ⟨_, _, _, _, hMaximum, _, _, _, _⟩
  exact ⟨sourceRoot, (fun _ _ => trivial), uniqueSource, hMaximum,
    (fun _ _ _ => trivial)⟩

private theorem sourceNotSupremelyGood :
    ¬ IsSupremelyGood transferAct transferAct (transferCause false) false TransferRole.source := by
  intro h
  have bad := h.2 .recipient true (by decide) trivial
  exact (by unfold transferCause; decide :
    ¬ transferCause false .source .recipient true) bad

theorem checks (_hEM : ExcludedMiddle) : Control := by
  refine ⟨TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer.rival,
    retained, sourcePerfect, trivial, sourceNotSupremelyGood, ?_⟩
  rintro ⟨n, hPerfect, hGood⟩
  have hEq := uniqueSource n hPerfect.1
  subst n
  exact sourceNotSupremelyGood hGood
end TruthCore.Results.Causality.DirectEsseRootGoodnessOmission
