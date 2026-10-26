import TruthCore.Case.Catholicism.StageOne.CausalFinitism
import TruthCore.Results.Bridges.PerSeRegressFiniteGrounding.Solution
import TruthCore.Results.Causality.FiniteGroundingHasSource.Solution

namespace TruthCore.Results.Case.Catholicism.CausalFinitism
open TruthCore.Case.Catholicism.StageOne.CausalFinitism
open TruthCore.Latin.Aquinas.SummaTheologiae
/-- Finite distinct ancestry and loop exclusion imply the existing per se
accessibility reading, provided each per se edge belongs to that causal relation.
All three premises remain philosophically open; no source attribution is made. -/
theorem perSeNoRegressOfFiniteAncestry {Being : Type}
    (cause perSe : Being → Being → Prop)
    (finiteHistory : FiniteDistinctAncestry cause)
    (noLoops : NoCausalLoops cause)
    (included : PerSeLinksIncluded cause perSe) :
    NoInfinitePerSeEfficientCauseSeriesReading perSe := by
  let : IsStrictOrder Being (Relation.TransGen cause) :=
    { irrefl := noLoops
      trans := fun _ _ _ h₁ h₂ => h₁.trans h₂ }
  have causeAcc : ∀ x, Acc cause x := by
    intro x
    have historyWF := (finiteHistory x).wellFoundedOn (r := Relation.TransGen cause)
    have historyCauseWF := historyWF.mono
      (fun _ _ h => Relation.TransGen.single h) (Set.Subset.refl _)
    exact ((Set.WellFoundedOn.acc_iff_wellFoundedOn (r := cause) (a := x)).out 1 3).mpr historyCauseWF
  intro x
  exact (Subrelation.wf (fun h => included h) ⟨causeAcc⟩).apply x

/-- Finite distinct ancestry alone permits a self-loop. -/
theorem needsNoLoops :
    ∃ (cause perSe : Unit → Unit → Prop),
      FiniteDistinctAncestry cause ∧ PerSeLinksIncluded cause perSe ∧
        ¬ NoInfinitePerSeEfficientCauseSeriesReading perSe := by
  refine ⟨(fun _ _ => True), (fun _ _ => True), ?_, ?_, ?_⟩
  · intro x
    exact Set.toFinite _
  · intro y x h
    exact h
  · intro h
    have impossible : ∀ x : Unit, Acc (fun _ _ : Unit => True) x → False := by
      intro x hx
      induction hx with
      | intro x _ ih => exact ih x trivial
    exact impossible () (h ())

/-- A strict infinite ascent of naturals is loop-free but not accessible;
loop exclusion and edge inclusion cannot replace finite ancestry. -/
theorem needsFiniteAncestry :
    ∃ (cause perSe : Nat → Nat → Prop),
      NoCausalLoops cause ∧ PerSeLinksIncluded cause perSe ∧
        ¬ NoInfinitePerSeEfficientCauseSeriesReading perSe := by
  let r : Nat → Nat → Prop := fun y x => x < y
  refine ⟨r, r, ?_, ?_, ?_⟩
  · intro x hx
    have decrease : ∀ {a b}, Relation.TransGen r a b → b < a := by
      intro a b h
      induction h with
      | single h => exact h
      | tail _ h ih => exact Nat.lt_trans h ih
    exact Nat.lt_irrefl x (decrease hx)
  · intro y x h
    exact h
  · intro h
    have impossible : ∀ x, Acc r x → False := by
      intro x hx
      induction hx with
      | intro x _ ih => exact ih (x + 1) (Nat.lt_succ_self x)
    exact impossible 0 (h 0)

/-- A finite empty history says nothing about an unrelated per se self-loop. -/
theorem needsInclusion :
    ∃ (cause perSe : Unit → Unit → Prop),
      FiniteDistinctAncestry cause ∧ NoCausalLoops cause ∧
        ¬ NoInfinitePerSeEfficientCauseSeriesReading perSe := by
  refine ⟨(fun _ _ => False), (fun _ _ => True), ?_, ?_, ?_⟩
  · intro x
    exact Set.toFinite _
  · intro x hx
    cases hx with
    | single h => exact h
    | tail _ h => exact h
  · intro h
    have impossible : ∀ x : Unit, Acc (fun _ _ : Unit => True) x → False := by
      intro x hx
      induction hx with
      | intro x _ ih => exact ih x trivial
    exact impossible () (h ())

/-- Compose the new accessibility result with the existing finite-grounding
and regress-to-finite-path results. The source can depend on the target and is
uncaused only with respect to the supplied per se relation. -/
theorem finitePathsOfFiniteAncestry {Being : Type}
    (cause perSe : Being → Being → Prop)
    (finiteHistory : FiniteDistinctAncestry cause)
    (noLoops : NoCausalLoops cause)
    (included : PerSeLinksIncluded cause perSe) :
    TruthCore.Bridges.EveryBeingHasFinitePerSePathToUncaused perSe := by
  exact TruthCore.Results.Bridges.PerSeRegressFiniteGrounding.everyBeingHasFinitePerSePathToUncausedOfNoRegress
    perSe (perSeNoRegressOfFiniteAncestry cause perSe finiteHistory noLoops included)
    Classical.em TruthCore.Results.Causality.FiniteGroundingHasSource.finiteGroundingHasSource

end TruthCore.Results.Case.Catholicism.CausalFinitism
