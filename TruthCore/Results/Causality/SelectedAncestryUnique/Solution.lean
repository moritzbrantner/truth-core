module
public import TruthCore.Results.Causality.SelectedAncestry.Solution
public import TruthCore.Results.Causality.UniqueRootPerfection.Solution
public import TruthCore.Causality.SelectedAncestryUniqueControl
public import TruthCore.Causality.DirectEsseRootRoute
@[expose] public section
namespace TruthCore.Results.Causality.SelectedAncestryUnique
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.SelectedAncestry
open TruthCore.Causality.NecessaryRootUniqueness
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.DirectEsseRootRoute
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Causality.SelectedAncestryUniqueControl
/-- One selected necessary ancestor becomes the unique actual concrete root
under the explicit fixed-esse interfaces. No global foundation is inferred. -/
theorem uniqueRoot {W B R : Type} (m : Profile W B) (w : W) (selected : B)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hAncestor : NecessaryRootAncestor m w selected)
    (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hApproach : GradesToMaximumAtBeing InAct MoreIn esse) :
    UniqueNecessaryActualRootAt m w := by
  obtain ⟨n, hCone, hn, hNoParent⟩ := hAncestor
  have hr : ActualRoot m w n := ⟨hCone.1, hNoParent⟩
  let act : B → Unit → Prop := fun x _ => InAct x esse
  let more : Unit → B → B → Prop := fun _ y x => MoreIn esse y x
  let cause : B → B → Unit → Prop := fun c x _ => CausesIn c x esse
  obtain ⟨y, hy⟩ := maximumExistsOfExistingRoot m w act more () n hr
    hExisting (fun _ => hApproach) hEM
  have hyn := maximumEqualsRoot m w act more cause () n hr hEM
    (fun _ => hGenus) hExisting hEsse y hy
  refine ⟨n, hr, hn, ?_⟩
  intro x hx
  have hyx := maximumEqualsRoot m w act more cause () x hx hEM
    (fun _ => hGenus) hExisting hEsse y hy
  exact hyx.symm.trans hyn
theorem controls : TruthCore.Causality.SelectedAncestryUniqueControl.Certificate := by
  unfold TruthCore.Causality.SelectedAncestryUniqueControl.Certificate
  constructor
  · exact ⟨(), ⟨⟨trivial, trivial⟩, Relation.ReflTransGen.refl⟩,
      (fun _ _ => trivial), fun _ h => h.2.2⟩
  · constructor
    · intro n hn x hne hx
      exact False.elim (hne (Subsingleton.elim x n))
    · constructor
      · intro x hx; trivial
      · constructor
        · intro c x hne hx hc; exact hc.elim
        · constructor
          · intro h; obtain ⟨x, y, h⟩ := h; exact h.elim
          · constructor
            · exact ⟨false, ⟨⟨trivial, trivial⟩, Relation.ReflTransGen.refl⟩,
                (fun _ _ => trivial), fun _ h => h.2.2⟩
            · constructor
              · intro h
                obtain ⟨n, hr, hn, hu⟩ := h
                cases n
                · have h := hu true ⟨⟨trivial, trivial⟩, fun _ h => h.2.2⟩; cases h
                · have h := hu false ⟨⟨trivial, trivial⟩, fun _ h => h.2.2⟩; cases h
              · constructor
                · constructor
                  · simp [policies, empty, act, more, cause,
                      MaximumInBeingCausesAllBeingsReading, ExistingInActAt,
                      EsseCauseIsActualConcreteGround, GradesToMaximumAtBeing,
                      IsMaximumIn, CausesAllInGenus]
                  · constructor
                    · rintro ⟨n, h, _⟩; exact h.1.2.elim
                    · rintro ⟨n, h, _⟩; exact h.1.2.elim
                · simp [full, act, more, cause,
                    MaximumInBeingCausesAllBeingsReading, ExistingInActAt,
                    EsseCauseIsActualConcreteGround, GradesToMaximumAtBeing,
                    IsMaximumIn, CausesAllInGenus]
end TruthCore.Results.Causality.SelectedAncestryUnique
