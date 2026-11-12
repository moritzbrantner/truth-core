module

public import TruthCore.Case.Catholicism.CausalPerfectionTransfer
public import TruthCore.Causality.TermSenseForks2
public import TruthCore.Logic.ExcludedMiddle

/-! A grounded entry into the perfection-transfer support cycle (#1476, PR #1480)

`STMT-CAUSE-OF-BEING-CAUSES-EVERY-PERFECTION` (`CauseOfBeingCausesEveryPerfection`,
unrestricted transfer) and `STMT-RESIDUAL-PERFECTION-TRANSFER`
(`ResidualPerfectionTransfer`) were proved only from each other: the residual by
projection from the unrestricted principle (result `CAUSAL-PERFECTION-TRANSFER-DELTA-FORWARD`),
and the unrestricted principle from the universal-scope principle
`STMT-UNIVERSAL-CAUSE-TRANSFERS-PERFECTIONS` plus the residual (result
`CAUSAL-PERFECTION-TRANSFER-RECONSTRUCTION`). The residual is by construction the
scope delta of the unrestricted principle over the universal one, so the cycle
had no independent entry.

The residual has two conjuncts: transfer for causes of esse that are not causes of
every other actual being (nonuniversal causes), and transfer for self-effects. This
module isolates the first conjunct as `NonuniversalPerfectionTransfer`. The
self-effect conjunct needs no transfer premise: under the existing open premise
`STMT-NOTHING-CAUSES-ITS-OWN-BEING` (`NothingCausesItsOwnBeing`, no `CausesIn x x esse`)
it is vacuous. The grounded entry derives the unrestricted principle from
universal-scope transfer, nonuniversal transfer, no self-causation of esse and
excluded middle (to decide whether a given cause of esse is universal).

What this does and does not do, stated plainly. It moves the open content of the
cycle onto `NonuniversalPerfectionTransfer`, which is strictly weaker than the
residual (`Control.Controls` part 2) and, given no self-causation of esse, says the
same as it. No premise is established, and no transfer case is defended. A
stronger sufficient alternative, that only a universal cause causes anything's
esse (which would make the nonuniversal case vacuous), is not registered. Analyst
formulation; attribution deferred. -/

@[expose] public section

namespace TruthCore.Causality.PerfectionTransferGrounding

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Causality.TermSenseForks

/-- Open premise, analyst formulation: a cause of a thing's esse that is **not** a
cause of the esse of every other actual being (`¬ CausesAllInGenus … esse c`)
still causes each perfection that thing has in act. Exactly the first conjunct of
`ResidualPerfectionTransfer`. It says nothing about universal causes, so nothing
about a universal cause's self-effects; for a nonuniversal cause it also covers
the case `x = c`. -/
def NonuniversalPerfectionTransfer {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∀ c, ¬ CausesAllInGenus InAct CausesIn esse c →
    ∀ x r, CausesIn c x esse → InAct x r → CausesIn c x r

namespace Control

/-- One being, two respects (false = esse, true = skill); everything is in act. The
being causes its own esse and nothing else. -/
def unitAct (_ : Unit) (_ : Bool) : Prop := True

def selfCause (_ _ : Unit) (r : Bool) : Prop := r = false

/-- Two beings: `true` is a source causing the esse of `false` and nothing else;
everything is in act. -/
def boolAct (_ : Bool) (_ : Bool) : Prop := True

def sourceCause (c x : Bool) (r : Bool) : Prop := r = false ∧ c = true ∧ x = false

/-- The four transfer roles with every perfection transferred: the source causes
every other being in every respect, and the particular supporter causes the
recipient in every respect. -/
def fullCause (c x : TransferRole) (_ : Bool) : Prop :=
  (c = .source ∧ x ≠ .source) ∨ (c = .supporter ∧ x = .recipient)

/-- Omission, strictness and nonvacuity controls for the grounded derivation.

1. Omission of nonuniversal transfer: in the existing four-role concurrent
   interpretation (with its full `TransferModelBackground true`), universal-scope
   transfer holds, nothing causes its own esse, nonuniversal transfer fails (the
   particular supporter causes the recipient's esse but not its skill) and the
   unrestricted principle fails.
2. Omission of no self-causation of esse (and strictness of the conjunct): a single
   being causing only its own esse satisfies universal-scope and nonuniversal
   transfer; it causes its own esse, and both the unrestricted principle and the
   residual fail. So nonuniversal transfer does not entail the residual.
3. Omission of universal-scope transfer: a source causing another's esse but not its
   skill falsifies universal-scope transfer and the unrestricted principle, while
   nonuniversal transfer and no self-causation of esse hold.
4. Nonvacuity: in a four-role interpretation with an actual nonuniversal esse edge
   (the supporter, which is not universal, causes the recipient's esse), all three
   nonlogical premises and the unrestricted principle hold.

Statements about these interpretations only. Excluded middle is a logical
principle, not a model parameter, and is not varied. -/
def Controls : Prop :=
  (TransferModelBackground true ∧
    UniversalCauseTransfersPerfections transferAct (transferCause true) false ∧
    NothingCausesItsOwnBeing (transferCause true) false ∧
    ¬ NonuniversalPerfectionTransfer transferAct (transferCause true) false ∧
    ¬ CauseOfBeingCausesEveryPerfection transferAct (transferCause true) false) ∧
  (UniversalCauseTransfersPerfections unitAct selfCause false ∧
    NonuniversalPerfectionTransfer unitAct selfCause false ∧
    ¬ NothingCausesItsOwnBeing selfCause false ∧
    ¬ CauseOfBeingCausesEveryPerfection unitAct selfCause false ∧
    ¬ ResidualPerfectionTransfer unitAct selfCause false) ∧
  (¬ UniversalCauseTransfersPerfections boolAct sourceCause false ∧
    NonuniversalPerfectionTransfer boolAct sourceCause false ∧
    NothingCausesItsOwnBeing sourceCause false ∧
    ¬ CauseOfBeingCausesEveryPerfection boolAct sourceCause false) ∧
  (UniversalCauseTransfersPerfections transferAct fullCause false ∧
    NonuniversalPerfectionTransfer transferAct fullCause false ∧
    NothingCausesItsOwnBeing fullCause false ∧
    CauseOfBeingCausesEveryPerfection transferAct fullCause false ∧
    ¬ CausesAllInGenus transferAct fullCause false .supporter ∧
    fullCause .supporter .recipient false)

end Control

end TruthCore.Causality.PerfectionTransferGrounding
