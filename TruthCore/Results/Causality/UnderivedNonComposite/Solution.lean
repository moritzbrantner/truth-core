import TruthCore.Causality.UnderivedNonComposite
import TruthCore.Results.Causality.UnderivedCommonSource.Solution
namespace TruthCore.Results.Causality.UnderivedNonComposite
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NamedPotentialCauser
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Causality.SourceForest
open TruthCore.Causality.UnderivedCommonSource
open TruthCore.Causality.UnderivedNonComposite
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Same-witness connection, retaining all eight #636 premises. Three explicit
additional premises are q.3's uniting-cause reading and the two open interfaces.
No maximality, first-being, or cause-comparison assumption is introduced. -/
theorem from_union {W B P : Type} (m : Ontic W B)
    (R : W → B → B → Prop) (w : W)
    (Composite : B → Prop) (CausesIn : B → B → P → Prop) (esse : P)
    (hNecessary : NecessaryBeing m w)
    (hReflexive : ActualReflexive m w)
    (hNoContingent : NoContingentGroundOfNecessary m R w)
    (hUnionWF : WellFoundedUnionNecessarySupport m R w)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hMap : ActualCauseSupportsEsse m R w)
    (hConnected : WeaklyConnected (actualGraph m w))
    (hConfluent : UpstreamConfluent (actualGraph m w))
    (hUniting : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hPresent : UnitingCausesPresent m CausesIn esse w)
    (hActual : UnitingCausesAreActual m CausesIn esse w) :
    CommonUnderivedNonComposite m R w Composite := by
  obtain ⟨n, hNamed, hSource⟩ :=
    TruthCore.Results.Causality.UnderivedCommonSource.causal_from_union
      m R w hNecessary hReflexive hNoContingent hUnionWF hEM hMap hConnected hConfluent
  refine ⟨n, hNamed, hSource, ?_⟩
  intro hComp
  obtain ⟨c, hc, hCause⟩ := hUniting n hComp
  have hExists := hPresent c n hNamed.1 hc hCause
  obtain ⟨hn, hRoot, _⟩ := hSource
  exact hRoot ⟨⟨c, hExists⟩, hActual c n hExists hn hc hCause⟩

theorem omission_controls : InterfaceOmissionControls := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact ⟨true, by cases x <;> simp_all [fixtureComposite], rfl, hx⟩
  · refine ⟨⟨rfl, ?_, ?_⟩, ?_, rfl, ?_, ?_⟩
    · intro v _; rfl
    · intro v c hc h; exact Bool.noConfusion (hc.symm.trans h.1)
    · refine ⟨rfl, ?_, ?_⟩
      · rintro ⟨c, h⟩; exact Bool.noConfusion (c.property.symm.trans h.1)
      · intro s _; exact s.property
    · intro c x _ _ _ h; exact h
    · intro h; exact Bool.noConfusion (h true false rfl (by decide) ⟨rfl, rfl⟩)
  · refine ⟨⟨True.intro, ?_, ?_⟩, ?_, rfl, ?_, ?_⟩
    · intro v _; trivial
    · intro v c _ h; exact Bool.noConfusion h.2
    · refine ⟨True.intro, ?_, ?_⟩
      · rintro ⟨c, h⟩; exact Bool.noConfusion h.2
      · intro s hs
        cases h : s.val with
        | false => rfl
        | true => exact False.elim (hs ⟨⟨false, True.intro⟩, rfl, h⟩)
    · intro c x _ _ _; trivial
    · intro h
      exact Bool.noConfusion (h true false True.intro True.intro (by decide) ⟨rfl, rfl⟩).1
end TruthCore.Results.Causality.UnderivedNonComposite
