module

public import TruthCore.Causality.NecessaryClassicalGodRoot

/-! Structural projection (assembly), no new philosophical inference: the
witness of `NecessaryClassicalGodRootAt` satisfies `σ.IsGod`, so the working
root `GodExists σ.IsGod` holds for the same signature and the same GOD_4
predicate. It connects the stage-two act-of-being and attribute composition to
the working root; it closes the root only if its premise is closed
(invariant 16). Uniqueness, the attributes and necessity are discarded. -/

@[expose] public section

namespace TruthCore.Results.Causality.NecessaryClassicalGodRootGodExists
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

theorem godExists {W P R : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being P R)
    (GoodIn InPotency : σ.Being → R → Prop) (MoreIn : R → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (h : NecessaryClassicalGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill) : GodExists σ.IsGod := by
  obtain ⟨n, -, -, -, -, -, hGod, -⟩ := h
  exact ⟨n, hGod⟩

end TruthCore.Results.Causality.NecessaryClassicalGodRootGodExists
