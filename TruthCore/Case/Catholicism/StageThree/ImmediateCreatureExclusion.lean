module

public import TruthCore.Case.Catholicism.StageThree.FoundingDefinitions

/-!
# Full immediate founding, as distinct from direct calibration

The strong rival excludes every creature or envoy supplying the constitutive
founding act, not merely the commissioned Jesus event. The explicit profile
keeps creaturehood independent of `IsGod` and of the named Jesus. `SuppliesAct`
is a primitive: x supplies the act constituting c as founded by principal g.
It excludes mere authorization, witnessing, later teaching and maintenance.
`Direct` means g's own constitutive act establishes c. Ordinary charter-making
is an analogy, not evidence about divine institutions. All three relations
remain interpretation inputs; no structural law or applicability to history
is asserted. In particular mandate holding does not imply act supply, and an
act in a mandate is not definitionally identified with an act of its principal.
-/

@[expose] public section

namespace TruthCore.Case.Catholicism.StageThree.ImmediateCreatureExclusion

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingDefinitions

/-- Open semantic inputs absent from Signature; no identity or nature axiom. -/
structure Profile (σ : Signature) where
  Direct : σ.Being → σ.Society → Prop
  IsCreature : σ.Being → Prop
  SuppliesAct : σ.Being → σ.Being → σ.Society → Prop

/-- Full old rival sense, at a principal and society. No Jesus restriction. -/
def ImmediateWithoutCreature (σ : Signature) (A : Agency σ) (P : Profile σ)
    (g : σ.Being) (c : σ.Society) : Prop :=
  P.Direct g c ∧ ∀ x, (P.IsCreature x ∨ A.HoldsMandate x g) → ¬ P.SuppliesAct x g c

/-- Full exclusion retains the own-act requirement. -/
theorem directOfImmediate (σ : Signature) (A : Agency σ) (P : Profile σ)
    (g : σ.Being) (c : σ.Society) (h : ImmediateWithoutCreature σ A P g c) :
    P.Direct g c := h.1

/-- Any creature's constitutive contribution defeats the full reading. -/
theorem creatureDefeatsImmediate (σ : Signature) (A : Agency σ) (P : Profile σ)
    (x g : σ.Being) (c : σ.Society) (hx : P.IsCreature x)
    (hs : P.SuppliesAct x g c) : ¬ ImmediateWithoutCreature σ A P g c :=
  fun h => h.2 x (Or.inl hx) hs

/-- An envoy's act defeats it without a creaturehood or Jesus identity premise. -/
theorem envoyDefeatsImmediate (σ : Signature) (A : Agency σ) (P : Profile σ)
    (x g : σ.Being) (c : σ.Society) (hx : A.HoldsMandate x g)
    (hs : P.SuppliesAct x g c) : ¬ ImmediateWithoutCreature σ A P g c :=
  fun h => h.2 x (Or.inr hx) hs

/-- Nonvacuity: actual God, direct founding and creatures, with no creature
supplying the act. This is only a schema interpretation. -/
theorem jointControl :
    ∃ σ : Signature, ∃ A : Agency σ, ∃ P : Profile σ, ∃ g c,
      σ.IsGod g ∧ (∃ x, P.IsCreature x) ∧ ImmediateWithoutCreature σ A P g c := by
  refine ⟨modelSig True, modelAgency True (fun p => p) False False False,
    ⟨fun _ _ => True, fun x => x = false, fun _ _ _ => False⟩,
    true, (), rfl, ⟨false, rfl⟩, trivial, ?_⟩
  intro _ _ h
  exact h

/-- Even the old Jesus-fragment exclusion plus minimal direct calibration
can coexist with a creature supplying an act. It therefore misses full exclusion. -/
theorem fragmentInsufficient :
    ∃ σ : Signature, ∃ A : Agency σ, ∃ P : Profile σ, ∃ g c,
      σ.IsGod g ∧ ExclusiveImmediateReading σ A P.Direct ∧
      ¬ ImmediateWithoutCreature σ A P g c := by
  refine ⟨modelSig True, modelAgency True (fun p => p) False False False,
    ⟨fun _ _ => True, fun x => x = false, fun _ _ _ => True⟩,
    true, (), rfl, ⟨?_, ?_⟩, ?_⟩
  · intro _ _ _
    exact Iff.rfl
  · intro _ _ _ he
    exact he.1.elim
  · intro h
    exact h.2 false (Or.inl rfl) trivial

end TruthCore.Case.Catholicism.StageThree.ImmediateCreatureExclusion
