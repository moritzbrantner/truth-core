import TruthCore.Causality.ActualUnderivedEssenceEsse
import TruthCore.Results.Causality.UnderivedEssenceEsse.Solution
namespace TruthCore.Results.Causality.ActualUnderivedEssenceEsse
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.ActualUnderivedEssenceEsse
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.UnderivedNonComposite
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4

/-- Reuse the constructive lifting theorem on the constant-world gated actual
relation. This introduces no modal reflexivity or cross-world constraint on R. -/
theorem actual_source_not_not {W B : Type} (m : Ontic W B)
    (R : W → B → B → Prop) (w : W) (hNecessary : NecessaryBeing m w)
    (hWF : ActualNecessaryWellFounded m R w)
    (hLocal : ActualNoContingent m R w) :
    ¬¬ ∃ n, m.ExistsAt w n ∧ NecessaryAt m w n ∧
      ∀ c, m.ExistsAt w c → ¬ R w c n := by
  let G : W → B → B → Prop := fun _ => ActualNecessarySupport m R w
  have hGWF : WellFoundedPresentEsseSupport m G w :=
    Subrelation.wf (fun {_ _} h => h.2) hWF
  have hLift : NecessaryPredecessorLifting m G w := by
    intro _ c n _ _ h
    exact ⟨h.1, h.2.2.1, h⟩
  have hNN := not_not_underived_of_lifting m G w hNecessary hGWF hLift
  intro hNone
  apply hNN
  rintro ⟨n, hn, hNec, hNo⟩
  apply hNone
  refine ⟨n, hn, hNec, ?_⟩
  intro c hc hR
  exact hNo w c hc ⟨hLocal c n hc hNec hR, hNec, hc, hR⟩

/-- The q3 core needs only actual absence of support. Explicit EM selects the
source and eliminates double-negated identity for that same source. -/
theorem checks {W B P A : Type} (m : Ontic W B)
    (R : W → B → B → Prop) (w : W) (p : Profile B P A)
    (hNecessary : NecessaryBeing m w)
    (hWF : ActualNecessaryWellFounded m R w)
    (hLocal : ActualNoContingent m R w)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hInAct : ExistingInActAt m p.InAct p.esse w)
    (hPresent : UnitingCausesPresent m p.CausesIn p.esse w)
    (hTyped : ActualEsseCausesSupportAt m R p.CausesIn p.esse w)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p) :
    ActualUnderivedEssenceIdentity m R w p := by
  have hNN := actual_source_not_not m R w hNecessary hWF hLocal
  have hSource : ∃ n, m.ExistsAt w n ∧ NecessaryAt m w n ∧
      ∀ c, m.ExistsAt w c → ¬ R w c n := by
    cases hEM _ with
    | inl h => exact h
    | inr h => exact False.elim (hNN h)
  obtain ⟨n, hn, hNec, hNo⟩ := hSource
  refine ⟨n, hn, hNec, hNo, ?_⟩
  exact TruthCore.Results.Causality.UnderivedEssenceEsse.actual_identity_direct
    m R w p n hn hNo hEM hInAct hPresent hTyped hExhaustive hNoSelfCause

/-- Reuse the rotating interpretation: local premises coexist with failure of
all-world underivedness. This witnesses scope strictness, not metaphysical possibility. -/
theorem rotating_strictness :
    let m := TruthCore.Models.NecessarilyUnderived.rotating
    let R := TruthCore.Models.NecessarilyUnderived.rotatingSupport
    NecessaryBeing m false ∧ ActualNecessaryWellFounded m R false ∧
    ActualNoContingent m R false ∧ ¬ NecessarilyUnderived m R false := by
  refine ⟨TruthCore.Models.NecessarilyUnderived.rotatingNecessary, ?_, ?_,
    TruthCore.Models.NecessarilyUnderived.rotatingNoUnderived⟩
  · exact Subrelation.wf (fun {_ _} h => h.2.2)
      TruthCore.Models.NecessarilyUnderived.rotatingActualWellFounded
  · intro c n hc hn hR
    exact TruthCore.Models.NecessarilyUnderived.rotatingNoContingentGround false c n hc hn hR
end TruthCore.Results.Causality.ActualUnderivedEssenceEsse
