module
public import TruthCore.Causality.NamingVeracityBatch1
@[expose] public section
namespace TruthCore.Causality.Power1392
open TruthCore.Case.Catholicism
open TruthCore.Causality.NamingVeracityBatch1
/-- All listed requirements, without a completeness assumption. -/
def AllReq (σ : Signature) (P : Power σ) (x : σ.Being) (t : P.Task) : Prop :=
  ∀ r, P.Requires t r → P.InAct x r
/-- Additional OPEN constraint, absent from the original route. -/
def Safe (σ : Signature) (P : Power σ) : Prop :=
  ∀ x t, P.CanDo x t → P.Consistent t
/-- Metatheoretic compatibility, holding all fields except ability fixed. -/
def Compatibility : Prop := ∀ (σ : Signature) (P : Power σ),
  (∃ ability : σ.Being → P.Task → Prop,
    ActivePowerFollowsAct σ { P with CanDo := ability } ∧
    Safe σ { P with CanDo := ability }) ↔
  ∀ x t, AllReq σ P x t → P.Consistent t
/-- Requires an actual infinite witness, not merely a universal conditional. -/
def WitnessConsequence : Prop := ∀ (σ : Signature) (P : Power σ)
    (Infinite : σ.Being → Prop) (g : σ.Being),
  Infinite g → InfiniteIsUnlimitedAct σ Infinite P →
  ActivePowerFollowsAct σ P → ConsistentTaskRequiresOnlyPossiblePerfections σ P →
  Safe σ P → ∀ t, P.Consistent t ↔ ∀ r, P.Requires t r → P.PossibleAct r
/-- Relative feasibility is an independently supplied predicate, not defined by
ability. Generic coherence only yields relative ability with the extra bridge. -/
def RelativeBridge : Prop := ∀ (σ : Signature) (P : Power σ)
    (feasible : σ.Being → P.Task → Prop) (g : σ.Being),
  (∀ t, feasible g t → P.CanDo g t) →
  (∀ t, P.CanDo g t → feasible g t) →
  ((∀ t, P.Consistent t → P.CanDo g t) ↔
   (∀ t, P.Consistent t → feasible g t))
/-- Structural nonvacuity and relative-scope omission; not possible-world
or divine-nature models. -/
def Controls : Prop :=
  (∃ (σ : Signature) (P : Power σ) (Infinite : σ.Being → Prop) (g : σ.Being),
    Infinite g ∧ InfiniteIsUnlimitedAct σ Infinite P ∧ ActivePowerFollowsAct σ P ∧
    ConsistentTaskRequiresOnlyPossiblePerfections σ P ∧ Safe σ P ∧
    P.Consistent P.revealWithSigns ∧ P.CanDo g P.revealWithSigns) ∧
  (∃ (σ : Signature) (P : Power σ) (feasible : σ.Being → P.Task → Prop) (g : σ.Being),
    (∀ t, feasible g t → P.CanDo g t) ∧
    (∀ t, P.CanDo g t → feasible g t) ∧
    ¬ (∀ t, P.Consistent t → P.CanDo g t))
/-- One required perfection; propositional switches expose each hypothesis. -/
def Scenario (a c k p : Prop) : Power Control.jσ where
  Task := Unit
  revealWithSigns := ()
  Consistent _ := k
  CanDo _ _ := c
  Perfection := Unit
  Requires _ _ := True
  InAct _ _ := a
  PossibleAct _ := p
/-- The retained three assumptions and failure of the biconditional. The omitted
assumption is not required; each explicit witness makes it false. -/
def Omission (omitted : Nat) (a c k p : Prop) : Prop :=
  let P := Scenario a c k p
  (omitted ≠ 0 → InfiniteIsUnlimitedAct Control.jσ (fun _ => True) P) ∧
  (omitted ≠ 1 → ActivePowerFollowsAct Control.jσ P) ∧
  (omitted ≠ 2 → ConsistentTaskRequiresOnlyPossiblePerfections Control.jσ P) ∧
  (omitted ≠ 3 → Safe Control.jσ P) ∧
  ¬ (P.Consistent () ↔ ∀ r, P.Requires () r → P.PossibleAct r)
/-- Actual Infinite witness true remains available in each scenario. -/
def Omissions : Prop :=
  Omission 0 False False False True ∧
  Omission 1 True False False True ∧
  Omission 2 True True True False ∧
  Omission 3 True True False True
/-- Exact conditional scope results and structural controls. -/
def Certificate : Prop := Compatibility ∧ WitnessConsequence ∧ RelativeBridge ∧ Controls ∧ Omissions
end TruthCore.Causality.Power1392
