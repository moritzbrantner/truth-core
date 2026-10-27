import TruthCore.Causality.NecessaryConcreteRoot

/-!
# #487: independent finite omission controls

The two Bool worlds are complete alternative histories and the Bool (or
Bool×Bool) bearers have rigid identity. A model being constructible in Lean
does not show that its history is metaphysically possible. These finite
controls test the exact assumption profile of `ConcreteRootCoreInconsistent`;
they do not equate temporal beginnings, causation and existential grounding.
-/

namespace TruthCore.Causality.NecessaryConcreteRootModels

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessaryConcreteRoot

def concreteAll {E : Type} : E → Prop := fun _ => True

/-- A named type and closed carrier constants for finite-model registration. -/
abbrev BoolPair : Type := Bool × Bool
def pair00 : BoolPair := (false, false)
def pair01 : BoolPair := (false, true)
def pair10 : BoolPair := (true, false)
def pair11 : BoolPair := (true, true)

/-- Exact finite enumeration of the two-world model's four rigid candidates. -/
theorem enumerateBoolPair : ∀ x : BoolPair,
    x = pair00 ∨ x = pair01 ∨ x = pair10 ∨ x = pair11 := by
  intro ⟨a, b⟩
  cases a with
  | false =>
    cases b with
    | false => exact Or.inl rfl
    | true => exact Or.inr (Or.inl rfl)
  | true =>
    cases b with
    | false => exact Or.inr (Or.inr (Or.inl rfl))
    | true => exact Or.inr (Or.inr (Or.inr rfl))

/-- Alternating-world model from #435/#445, restricted to no causal edges.
Both histories are populated, but each bearer is absent from the other. -/
def alternating : Ontic Bool Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun w x => x = w
  Causes := fun _ _ _ => False

private theorem alternatingWF :
    WellFounded (ActualConcreteCausesAt alternating concreteAll false) := by
  refine ⟨fun x => ?_⟩
  apply Acc.intro
  intro y h
  exact False.elim h

/-- Drop universal contingent dependence while retaining population,
well-foundedness, all-actual-contingency and failure of a necessary bearer. -/
def OmitDependence : Prop :=
  (∃ x, concreteAll x ∧ alternating.ExistsAt false x) ∧
  WellFounded (ActualConcreteCausesAt alternating concreteAll false) ∧
  AllActualConcreteContingent alternating concreteAll false ∧
  ¬ ContingentConcreteDependenceAt alternating concreteAll false ∧
  ¬ NecessaryConcreteAt alternating concreteAll false

theorem omitDependence : OmitDependence := by
  unfold OmitDependence
  refine ⟨?_, alternatingWF, ?_, ?_, ?_⟩
  · exact ⟨false, True.intro, rfl⟩
  · unfold AllActualConcreteContingent ContingentAt alternating concreteAll
    decide
  · unfold ContingentConcreteDependenceAt ContingentAt alternating concreteAll
    decide
  · unfold NecessaryConcreteAt NecessaryAt alternating concreteAll
    decide

/-- Each history contains TWO distinct contingent concreta; its local
causal relation has the two-node cycle (w,false) ↔ (w,true). -/
def cyclic : Ontic Bool BoolPair where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun w x => x.1 = w
  Causes := fun w y x => y.1 = w ∧ x.1 = w ∧ y.2 ≠ x.2

private theorem cyclicNotWF :
    ¬ WellFounded (ActualConcreteCausesAt cyclic concreteAll false) := by
  intro hWF
  have bad : ∀ x : ActualConcrete cyclic concreteAll false,
      Acc (ActualConcreteCausesAt cyclic concreteAll false) x → False := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      let y : ActualConcrete cyclic concreteAll false :=
        ⟨(false, !x.val.2), ⟨True.intro, rfl⟩⟩
      have hy : ActualConcreteCausesAt cyclic concreteAll false y x := by
        change (false = false) ∧ (x.val.1 = false) ∧ ((!x.val.2) ≠ x.val.2)
        refine ⟨rfl, x.property.2, ?_⟩
        cases x.val.2 <;> decide
      exact ih y hy
  exact bad ⟨(false, false), ⟨True.intro, rfl⟩⟩
    (hWF.apply ⟨(false, false), ⟨True.intro, rfl⟩⟩)

/-- Drop well-foundedness while retaining actual population, root-inclusive
dependence and all-contingency; the cycle supplies each concrete predecessor. -/
def OmitWellFoundedness : Prop :=
  (∃ x, concreteAll x ∧ cyclic.ExistsAt false x) ∧
  ContingentConcreteDependenceAt cyclic concreteAll false ∧
  AllActualConcreteContingent cyclic concreteAll false ∧
  ¬ WellFounded (ActualConcreteCausesAt cyclic concreteAll false) ∧
  ¬ NecessaryConcreteAt cyclic concreteAll false

theorem omitWellFoundedness : OmitWellFoundedness := by
  unfold OmitWellFoundedness
  refine ⟨?_, ?_, ?_, cyclicNotWF, ?_⟩
  · exact ⟨(false, false), True.intro, rfl⟩
  · intro x _ hx _
    refine ⟨(false, !x.2), True.intro, rfl, ?_⟩
    change (false = false) ∧ (x.1 = false) ∧ ((!x.2) ≠ x.2)
    refine ⟨rfl, hx, ?_⟩
    cases x.2 <;> decide
  · intro x _ hx
    rcases x with ⟨a, b⟩
    cases a with
    | false =>
      refine ⟨rfl, ⟨true, True.intro, ?_⟩⟩
      change ¬ (false = true)
      intro h
      cases h
    | true =>
      change true = false at hx
      cases hx
  · rintro ⟨x, _, hx, hn⟩
    have ht := hn true True.intro
    change x.1 = false at hx
    change x.1 = true at ht
    have contradiction : false = true := hx.symm.trans ht
    cases contradiction

/-- An empty existence extension at every history is different from an
empty world type. Bool still supplies two world labels. -/
def empty : Ontic Bool Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => False
  Causes := fun _ _ _ => False

private theorem emptyWF :
    WellFounded (ActualConcreteCausesAt empty concreteAll false) := by
  refine ⟨fun x => ?_⟩
  apply Acc.intro
  intro y h
  exact False.elim h

/-- Drop actual concrete population. Dependence and well-foundedness then
hold vacuously, without any concrete necessary existent. -/
def OmitPopulation : Prop :=
  ¬ (∃ x, concreteAll x ∧ empty.ExistsAt false x) ∧
  WellFounded (ActualConcreteCausesAt empty concreteAll false) ∧
  ContingentConcreteDependenceAt empty concreteAll false ∧
  AllActualConcreteContingent empty concreteAll false ∧
  ¬ NecessaryConcreteAt empty concreteAll false

theorem omitPopulation : OmitPopulation := by
  unfold OmitPopulation
  refine ⟨?_, emptyWF, ?_, ?_, ?_⟩
  · unfold empty concreteAll
    decide
  · unfold ContingentConcreteDependenceAt ContingentAt empty concreteAll
    decide
  · unfold AllActualConcreteContingent ContingentAt empty concreteAll
    decide
  · unfold NecessaryConcreteAt NecessaryAt empty concreteAll
    decide

/-- A constant bearer demonstrates the fourth deletion for minimality of
the *inconsistent core*: all four positive assumptions survive when the
negation of the necessary-bearer conclusion is omitted. -/
def stable : Ontic Bool Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := fun _ _ _ => False

private theorem stableWF :
    WellFounded (ActualConcreteCausesAt stable concreteAll false) := by
  refine ⟨fun x => ?_⟩
  apply Acc.intro
  intro y h
  exact False.elim h

def OmitAllContingent : Prop :=
  (∃ x, concreteAll x ∧ stable.ExistsAt false x) ∧
  WellFounded (ActualConcreteCausesAt stable concreteAll false) ∧
  ContingentConcreteDependenceAt stable concreteAll false ∧
  ¬ AllActualConcreteContingent stable concreteAll false ∧
  NecessaryConcreteAt stable concreteAll false

theorem omitAllContingent : OmitAllContingent := by
  unfold OmitAllContingent
  refine ⟨?_, stableWF, ?_, ?_, ?_⟩
  · exact ⟨false, True.intro, True.intro⟩
  · unfold ContingentConcreteDependenceAt ContingentAt stable concreteAll
    decide
  · unfold AllActualConcreteContingent ContingentAt stable concreteAll
    decide
  · exact ⟨false, True.intro, True.intro, fun _ _ => True.intro⟩

/-- The only predecessor of the actual concrete false bearer is an existing
but *abstract* true bearer. Counting such a witness as an immediate cause
weakens, and fails to imply, the typed concrete-dependence principle. -/
def abstractPredecessor : Ontic Bool Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun w _ => w = false
  Causes := fun _ y x => y = true ∧ x = false

def onlyFalseConcrete : Bool → Prop := fun x => x = false

def WeakUntypedDependenceAt {W E : Type} (m : Ontic W E)
    (concrete : E → Prop) (w : W) : Prop :=
  ∀ x, concrete x → m.ExistsAt w x → ContingentAt m w x →
    ∃ y, m.ExistsAt w y ∧ m.Causes w y x

private theorem abstractWF :
    WellFounded (ActualConcreteCausesAt abstractPredecessor onlyFalseConcrete false) := by
  refine ⟨fun x => ?_⟩
  apply Acc.intro
  intro y h
  have hy : y.val = false := y.property.1
  have hCause : y.val = true := h.1
  cases hy.symm.trans hCause

/-- Concreteness is load-bearing: even a *present* abstract predecessor can
satisfy untyped dependence and leave all actual concreta contingent. -/
def OmitConcretePredecessor : Prop :=
  (∃ x, onlyFalseConcrete x ∧ abstractPredecessor.ExistsAt false x) ∧
  WellFounded (ActualConcreteCausesAt abstractPredecessor onlyFalseConcrete false) ∧
  WeakUntypedDependenceAt abstractPredecessor onlyFalseConcrete false ∧
  ¬ ContingentConcreteDependenceAt abstractPredecessor onlyFalseConcrete false ∧
  ¬ NecessaryConcreteAt abstractPredecessor onlyFalseConcrete false

theorem omitConcretePredecessor : OmitConcretePredecessor := by
  unfold OmitConcretePredecessor
  refine ⟨?_, abstractWF, ?_, ?_, ?_⟩
  · exact ⟨false, rfl, rfl⟩
  · unfold WeakUntypedDependenceAt ContingentAt abstractPredecessor onlyFalseConcrete
    decide
  · unfold ContingentConcreteDependenceAt ContingentAt abstractPredecessor onlyFalseConcrete
    decide
  · unfold NecessaryConcreteAt NecessaryAt abstractPredecessor onlyFalseConcrete
    decide

/-- Restrict access to identity, although both histories remain inhabited
and have different rigid bearers. The actual bearer at false is necessary
relative to its accessible histories, but absent from the inaccessible true
history. Thus the global conclusion is not implied without the bridge. -/
def isolatedHistories : Ontic Bool Bool where
  frame := ⟨fun w v => w = v⟩
  ExistsAt := fun w x => x = w
  Causes := fun _ _ _ => False

private theorem isolatedWF :
    WellFounded (ActualConcreteCausesAt isolatedHistories concreteAll false) := by
  refine ⟨fun x => ?_⟩
  apply Acc.intro
  intro y h
  exact False.elim h

def OmitUniversalAccessibility : Prop :=
  PopulatedConcreteAt isolatedHistories concreteAll false ∧
  WellFoundedConcreteAt isolatedHistories concreteAll false ∧
  ContingentConcreteDependenceAt isolatedHistories concreteAll false ∧
  NecessaryConcreteAt isolatedHistories concreteAll false ∧
  ¬ UniversalAccessibilityAt isolatedHistories false ∧
  ¬ EveryWorldConcreteAt isolatedHistories concreteAll false

theorem omitUniversalAccessibility : OmitUniversalAccessibility := by
  unfold OmitUniversalAccessibility
  refine ⟨?_, isolatedWF, ?_, ?_, ?_, ?_⟩
  · exact ⟨false, True.intro, rfl⟩
  · unfold ContingentConcreteDependenceAt ContingentAt isolatedHistories concreteAll
    decide
  · unfold NecessaryConcreteAt NecessaryAt isolatedHistories concreteAll
    decide
  · unfold UniversalAccessibilityAt isolatedHistories
    decide
  · unfold EveryWorldConcreteAt isolatedHistories concreteAll
    decide

/-! Direct component certificates for the existing finite-model registry. -/

theorem alternatingPopulated : PopulatedConcreteAt alternating concreteAll false :=
  omitDependence.1

theorem alternatingWellFounded : WellFoundedConcreteAt alternating concreteAll false :=
  omitDependence.2.1

theorem alternatingAllContingent :
    AllActualConcreteContingent alternating concreteAll false :=
  omitDependence.2.2.1

theorem alternatingNoDependence :
    ¬ ContingentConcreteDependenceAt alternating concreteAll false :=
  omitDependence.2.2.2.1

theorem cyclicPopulated : PopulatedConcreteAt cyclic concreteAll false :=
  omitWellFoundedness.1

theorem cyclicDependence : ContingentConcreteDependenceAt cyclic concreteAll false :=
  omitWellFoundedness.2.1

theorem cyclicAllContingent : AllActualConcreteContingent cyclic concreteAll false :=
  omitWellFoundedness.2.2.1

theorem cyclicNotWellFounded : ¬ WellFoundedConcreteAt cyclic concreteAll false :=
  omitWellFoundedness.2.2.2.1

theorem emptyNotPopulated : ¬ PopulatedConcreteAt empty concreteAll false :=
  omitPopulation.1

theorem emptyWellFounded : WellFoundedConcreteAt empty concreteAll false :=
  omitPopulation.2.1

theorem emptyDependence : ContingentConcreteDependenceAt empty concreteAll false :=
  omitPopulation.2.2.1

theorem emptyAllContingent : AllActualConcreteContingent empty concreteAll false :=
  omitPopulation.2.2.2.1

theorem stablePopulated : PopulatedConcreteAt stable concreteAll false :=
  omitAllContingent.1

theorem stableWellFounded : WellFoundedConcreteAt stable concreteAll false :=
  omitAllContingent.2.1

theorem stableDependence : ContingentConcreteDependenceAt stable concreteAll false :=
  omitAllContingent.2.2.1

theorem stableNotAllContingent : ¬ AllActualConcreteContingent stable concreteAll false :=
  omitAllContingent.2.2.2.1

theorem abstractPopulated : PopulatedConcreteAt abstractPredecessor onlyFalseConcrete false :=
  omitConcretePredecessor.1

theorem abstractWellFounded :
    WellFoundedConcreteAt abstractPredecessor onlyFalseConcrete false :=
  omitConcretePredecessor.2.1

theorem abstractNoTypedDependence :
    ¬ ContingentConcreteDependenceAt abstractPredecessor onlyFalseConcrete false :=
  omitConcretePredecessor.2.2.2.1

theorem isolatedPopulated : PopulatedConcreteAt isolatedHistories concreteAll false :=
  omitUniversalAccessibility.1

theorem isolatedWellFounded : WellFoundedConcreteAt isolatedHistories concreteAll false :=
  omitUniversalAccessibility.2.1

theorem isolatedDependence :
    ContingentConcreteDependenceAt isolatedHistories concreteAll false :=
  omitUniversalAccessibility.2.2.1

theorem isolatedNoUniversalAccessibility :
    ¬ UniversalAccessibilityAt isolatedHistories false :=
  omitUniversalAccessibility.2.2.2.2.1

theorem isolatedNoGlobalConcrete :
    ¬ EveryWorldConcreteAt isolatedHistories concreteAll false :=
  omitUniversalAccessibility.2.2.2.2.2

/-- Six independent finite controls. The first four certify deletion
minimality of the four-member contradictory core; the other two prevent
confusing abstract predecessors and unrestricted global accessibility. -/
def OmissionMatrix : Prop :=
  OmitDependence ∧ OmitWellFoundedness ∧ OmitPopulation ∧
    OmitAllContingent ∧ OmitConcretePredecessor ∧ OmitUniversalAccessibility

theorem omissionMatrix : OmissionMatrix := by
  exact ⟨omitDependence, omitWellFoundedness, omitPopulation,
    omitAllContingent, omitConcretePredecessor, omitUniversalAccessibility⟩

end TruthCore.Causality.NecessaryConcreteRootModels
