module

public import TruthCore.Causality.PerfectionTransferGrounding
public import TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer.Solution

/-! A grounded entry into the perfection-transfer support cycle: unrestricted
transfer from universal-scope transfer, nonuniversal transfer, no self-causation of
esse and excluded middle; and its controls. Analyst formulations, attribution
deferred. No premise is established. -/

@[expose] public section

namespace TruthCore.Results.Causality.PerfectionTransferGrounding

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Causality.TermSenseForks
open TruthCore.Causality.PerfectionTransferGrounding
open TruthCore.Causality.PerfectionTransferGrounding.Control
open TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer
open TruthCore.Logic

/-- If c causes x's esse and x is in act in r, then either c causes the esse of
every other actual being or it does not (excluded middle). x is not c, since
nothing causes its own esse. In the first case universal-scope transfer gives that
c causes x's being in act in r; in the second, nonuniversal transfer does. -/
theorem causeOfBeingCausesEveryPerfectionGrounded {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hEM : ExcludedMiddle)
    (hUniv : UniversalCauseTransfersPerfections InAct CausesIn esse)
    (hNon : NonuniversalPerfectionTransfer InAct CausesIn esse)
    (hOwn : NothingCausesItsOwnBeing CausesIn esse) :
    CauseOfBeingCausesEveryPerfection InAct CausesIn esse := by
  intro c x r hEsse hAct
  have hDistinct : x ≠ c := fun hEq => hOwn c (hEq ▸ hEsse)
  rcases hEM (CausesAllInGenus InAct CausesIn esse c) with hAll | hNot
  · exact hUniv c hAll x r hDistinct hEsse hAct
  · exact hNon c hNot x r hEsse hAct

attribute [local instance] transferFourForallDecidable

theorem controls : Control.Controls := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 1: omission of nonuniversal transfer, in the concurrent interpretation
    have hSep := separator
    refine ⟨hSep.1, hSep.2.2.1, ?_, ?_, hSep.2.2.2⟩
    · show ∀ x, ¬ transferCause true x x false
      decide
    · intro h
      have hNot : ¬ CausesAllInGenus transferAct (transferCause true) false .supporter := by
        decide
      have bad := h .supporter hNot .recipient true (by unfold transferCause; decide) True.intro
      exact (by unfold transferCause; decide : ¬ transferCause true .supporter .recipient true) bad
  · -- 2: omission of no self-causation of esse; the residual fails too
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro c _ x _ hne
      exact absurd rfl hne
    · intro c hNot
      exact absurd (fun x hne => absurd rfl hne) hNot
    · intro h
      exact h () rfl
    · intro h
      exact Bool.noConfusion (h () () true rfl True.intro : true = false)
    · intro h
      exact Bool.noConfusion (h.2 () true rfl True.intro : true = false)
  · -- 3: omission of universal-scope transfer
    have hUniversal : CausesAllInGenus boolAct sourceCause false true := by
      intro x hne _
      cases x
      · exact ⟨rfl, rfl, rfl⟩
      · exact absurd rfl hne
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      exact Bool.noConfusion
        (h true hUniversal false true Bool.noConfusion ⟨rfl, rfl, rfl⟩ True.intro).1
    · intro c hNot x r hEsse _
      cases c
      · exact Bool.noConfusion hEsse.2.1
      · exact absurd hUniversal hNot
    · intro x h
      cases x
      · exact Bool.noConfusion h.2.1
      · exact Bool.noConfusion h.2.2
    · intro h
      exact Bool.noConfusion (h true false true ⟨rfl, rfl, rfl⟩ True.intro).1
  · -- 4: nonvacuity with an actual nonuniversal esse edge
    refine ⟨?_, ?_, ?_, ?_, ?_, Or.inr ⟨rfl, rfl⟩⟩
    · intro _ _ _ _ _ hEsse _
      exact hEsse
    · intro _ _ _ _ hEsse _
      exact hEsse
    · intro x h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2 h1
      · exact TransferRole.noConfusion (h1.symm.trans h2)
    · intro _ _ _ hEsse _
      exact hEsse
    · intro h
      rcases h .source TransferRole.noConfusion True.intro with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact TransferRole.noConfusion h1
      · exact TransferRole.noConfusion h2

end TruthCore.Results.Causality.PerfectionTransferGrounding
