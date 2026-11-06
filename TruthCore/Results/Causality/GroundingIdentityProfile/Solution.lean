module

public import TruthCore.Causality.GroundingIdentityProfile

@[expose] public section

namespace TruthCore.Results.Causality.GroundingIdentityProfile
open TruthCore.Causality.GroundingIdentityProfile
open TruthCore.Causality.BruteFoundationDoubling
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.CounterpartNecessity

/-- Each existing source coordinate has exactly one existing tagged representative
at each world; the correspondence is not a bijection on the whole roster. -/
theorem sameLocalData (s : LocalState B) : SameLocalData s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w x hx
    refine ⟨(w, x.2), ⟨⟨rfl, hx.2⟩, rfl⟩, ?_⟩
    intro z hz
    exact Prod.ext hz.1.1 hz.2.symm
  · intro w y hy
    refine ⟨(false, y.2), ⟨⟨rfl, hy.2⟩, rfl⟩, ?_⟩
    intro z hz
    exact Prod.ext hz.1.1 hz.2
  · intro w x y _ _ heq
    change s.concrete x.2 ↔ s.concrete y.2
    rw [heq]
  · intro w a b x y ha hb hx hy hax hby
    have edge : (rigid s).grounds w a b ↔ (doubled s).grounds w x y := by
      constructor
      · intro h
        exact ⟨hx.1, hy.1, hax ▸ hby ▸ h.2.2⟩
      · intro h
        exact ⟨ha.1, hb.1, hax.symm ▸ hby.symm ▸ h.2.2⟩
    exact ⟨edge, edge⟩

theorem total (s : LocalState B) : Total (doubled s).ontic (counterparts s) := by
  intro w x hx v _
  exact ⟨(v, x.2), ⟨rfl, hx.2⟩, hx, ⟨rfl, hx.2⟩, rfl⟩

theorem unique (s : LocalState B) : Unique (doubled s).ontic (counterparts s) := by
  intro w x v y z hy hz hxy hxz
  exact Prod.ext (hy.1.trans hz.1.symm) (hxy.2.2.symm.trans hxz.2.2)

theorem injective (s : LocalState B) : Injective (doubled s).ontic (counterparts s) := by
  intro w x z v y hx hz _ hxy hzy
  exact Prod.ext (hx.1.trans hz.1.symm) (hxy.2.2.trans hzy.2.2.symm)

/-- Exact composition at every middle world. The backward direction constructs
an existing middle representative, which seriality alone would not identify. -/
theorem composition (s : LocalState B) (w v u : Bool) (x z : Bool × B) :
    (∃ y, counterparts s w x v y ∧ counterparts s v y u z) ↔
      counterparts s w x u z := by
  constructor
  · rintro ⟨y, hxy, hyz⟩
    exact ⟨hxy.1, hyz.2.1, hxy.2.2.trans hyz.2.2⟩
  · intro hxz
    have middle : (doubled s).ontic.ExistsAt v (v, x.2) := ⟨rfl, hxz.1.2⟩
    exact ⟨(v, x.2), ⟨hxz.1, middle, rfl⟩, ⟨middle, hxz.2.1, hxz.2.2⟩⟩

/-- The new necessary witness follows from the fixed-tag assignment and source
population, without assuming necessary existence or an identity bridge. -/
theorem rigidNecessary (s : LocalState B)
    (population : ∃ b, s.concrete b ∧ s.existsAt b) :
    NecessaryConcreteAt (rigid s) false := by
  rcases population with ⟨b, hc, he⟩
  exact ⟨(false, b), hc, ⟨rfl, he⟩, fun _ _ => ⟨rfl, he⟩⟩

theorem comparison (s : LocalState B) (noninitial : B → Prop)
    (population : ∃ b, s.concrete b ∧ s.existsAt b)
    (wf : WellFounded s.grounds)
    (sound : ∀ y x, s.grounds y x → s.existsAt y ∧ s.existsAt x ∧ y ≠ x)
    (coverage : NoninitialCovered s noninitial) : Comparison s noninitial := by
  have oldPopulation := doublesPopulation s population
  have oldWF := doublesWellFounded s wf
  have oldSound := doublesGroundSound s sound
  have oldCoverage := doublesNoninitialCoverage s noninitial coverage
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, sameLocalData s,
    total s, unique s, injective s, ?_, ?_, composition s, ?_, ?_,
    rigidNecessary s population, doubledHasNoNecessary s⟩
  · exact ⟨fun _ => oldPopulation false, fun _ => oldWF false,
      fun _ => oldSound false, fun _ => oldCoverage false⟩
  · exact ⟨oldPopulation, oldWF, oldSound, oldCoverage⟩
  · intro w v y hy
    exact ⟨(w, y.2), ⟨rfl, hy.2⟩, ⟨rfl, hy.2⟩, hy, rfl⟩
  · intro w x hx
    exact ⟨hx, hx, rfl⟩
  · intro b hb
    exact ⟨⟨rfl, hb⟩, total s false (false, b) ⟨rfl, hb⟩⟩
  · intro bridge
    rcases population with ⟨b, _, hb⟩
    have bad : (false, b) = (true, b) :=
      bridge false (false, b) true (true, b) ⟨⟨rfl, hb⟩, ⟨rfl, hb⟩, rfl⟩
    have impossible : false = true := congrArg Prod.fst bad
    cases impossible

theorem certificate : Certificate := by
  refine ⟨fun _ s n population wf sound coverage =>
    comparison s n population wf sound coverage, ?_⟩
  rcases exampleSourceConditions with ⟨population, wf, sound, coverage⟩
  have edge := (copiedEdgeIff exampleSource false (false, false) (false, true)).mpr
    exampleSourceHasLink
  exact ⟨comparison exampleSource (fun x => x.2 = true) population wf sound coverage,
    edge, edge⟩

end TruthCore.Results.Causality.GroundingIdentityProfile
