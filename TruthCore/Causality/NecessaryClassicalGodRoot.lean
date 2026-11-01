import TruthCore.Causality.RootPositiveIntellectWill
import TruthCore.Case.Catholicism.StagesOneTwo
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityEternity

/-! Conditional shared-root naming/attribute composition. Existing infinity,
eternity, nominal naming and classical-field adapters remain explicit open
interfaces; no source interpretation or philosophical truth is established. -/
namespace TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.DirectEsseRootPerfectionGoodness
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

/-- ONE actual selected necessary root retains maximum/perfection, represented
identity, firstness, matter-form exclusion and remoteness. This SAME witness is
God under the explicit nominal interface, is the one God under IsTheOneGod,
has the exact nine case predicates and the primitive signature field. Selected
root uniqueness is not uniqueness of all necessary individuals. Global dictionary,
causal/cognitive, infinity and eternity applicability remain independently OPEN. -/
def NecessaryClassicalGodRootAt {W P R : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being P R)
    (GoodIn InPotency : σ.Being → R → Prop) (MoreIn : R → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop) : Prop :=
  ∃ n, PerfectRootAt m w p.InAct MoreIn p.esse n ∧
    p.esseOf n = p.essenceOf n ∧ IsFirstBeing PriorSimply n ∧
    ¬ MatterForm n ∧ RemoteFromAll ComponentOf n ∧ σ.IsGod n ∧
    NineClassicalAttributes (IsSimple Composite) (IsPerfect p.InAct)
      (IsSupremelyGood p.InAct GoodIn p.CausesIn p.esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill n ∧
    σ.HasClassicalAttributes n

/-- Structural projection only; the naming and primitive-field interfaces have
already been supplied to obtain the endpoint. No new philosophical inference. -/
theorem uniqueClassicalGodExists {W P R : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being P R)
    (GoodIn InPotency : σ.Being → R → Prop) (MoreIn : R → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (h : NecessaryClassicalGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill) : UniqueClassicalGodExists σ := by
  obtain ⟨n, _, _, _, _, _, hGod, hNine, hField⟩ := h
  exact ⟨n, hGod, hNine.2.2.2.1, hField⟩
end TruthCore.Causality.NecessaryClassicalGodRoot
