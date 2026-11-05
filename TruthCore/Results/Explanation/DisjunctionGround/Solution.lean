module

public import TruthCore.Explanation.DisjunctionGround

@[expose] public section

namespace TruthCore.Results.Explanation.DisjunctionGround
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.DisjunctionGround
open TruthCore.German.Kant.CosmologicalInference

variable {W B F : Type}

/-! ## General theorems -/

theorem uniform_local (A : Arena W B F) (a : W) (d : F)
    (h : UniformGround A a d) : LocallyGrounded A a d := by
  obtain ⟨r, hr⟩ := h
  exact fun v hv => ⟨r, hr v hv⟩

theorem local_necessary (A : Arena W B F) (a : W) (d : F) (hf : Factive A)
    (h : LocallyGrounded A a d) :
    TruthCore.Explanation.StoppingPoints.NecessaryFact A a d := by
  intro v hv
  obtain ⟨r, hr⟩ := h v hv
  exact (hf v r d hr).2

theorem local_population (A : Arena W B F) (a : W) (d : F) (hf : Factive A)
    (hc : Coherent A) (hi : InstanceGrounding A d) (h : LocallyGrounded A a d) :
    ∀ v, Access A a v → ∃ x, A.ontic.ExistsAt v x := by
  intro v hv
  obtain ⟨r, hr⟩ := h v hv
  obtain ⟨x, rfl⟩ := hi v r hr
  exact ⟨x, (hc v x).1 (hf v _ d hr).1⟩

theorem uniform_necessary (A : Arena W B F) (a : W) (d : F) (hf : Factive A)
    (hc : Coherent A) (hi : InstanceGrounding A d) (ha : Access A a a)
    (h : UniformGround A a d) : NecessaryBeing A.ontic a := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨x, rfl⟩ := hi a r (hr a ha)
  have hx : NecessaryAt A.ontic a x := fun v hv => (hc v x).1 (hf v _ d (hr v hv)).1
  exact ⟨x, hx a ha, hx⟩

theorem uniform_fork (A : Arena W B F) (a : W) (d : F)
    (em : TruthCore.Logic.ExcludedMiddle) (hf : Factive A) (hc : Coherent A)
    (ha : Access A a a) (h : UniformGround A a d) :
    (∃ r, (∀ v, Access A a v → A.explains v r d) ∧ ¬ ∃ x, r = A.exist x) ∨
      NecessaryBeing A.ontic a := by
  obtain ⟨r, hr⟩ := h
  cases em (∃ x, r = A.exist x) with
  | inl hx =>
    obtain ⟨x, rfl⟩ := hx
    have hn : NecessaryAt A.ontic a x := fun v hv => (hc v x).1 (hf v _ d (hr v hv)).1
    exact Or.inr ⟨x, hn a ha, hn⟩
  | inr hx => exact Or.inl ⟨r, hr, hx⟩

/-! ## Shared model lemmas -/

theorem alternating_no_necessary (acc : Bool → Bool → Prop) (hacc : ∀ v, acc false v)
    (holds : Bool → DFact → Prop) (ex : Bool → DFact → DFact → Prop) :
    ¬ NecessaryBeing (mk acc alternating holds ex).ontic false := by
  rintro ⟨x, _, hx⟩
  cases x with
  | false => exact Bool.noConfusion (hx true (hacc true))
  | true => exact Bool.noConfusion (hx false (hacc false))

theorem exist_ne_law (x : Bool) : DFact.law ≠ DFact.exist x := fun h => DFact.noConfusion h

theorem existReason_instance (pick : Bool → Bool → Prop) :
    ∀ v r f, existReason pick v r f → f = DFact.some → ∃ x, r = DFact.exist x := by
  intro v r f h _
  cases r with
  | exist x => exact ⟨x, rfl⟩
  | some => exact h.elim
  | law => exact h.elim

/-! ## Models -/

theorem truthmakers_facts :
    Factive truthmakers ∧ Coherent truthmakers ∧ InstanceGrounding truthmakers .some ∧
    Access truthmakers false false ∧ ExistentialFact truthmakers .some ∧
    LocallyGrounded truthmakers false .some ∧
    TruthCore.Explanation.StoppingPoints.NecessaryFact truthmakers false .some ∧
    Necessitating truthmakers ∧ Contingent truthmakers false (.exist false) ∧
    ¬ UniformGround truthmakers false .some ∧ ¬ NecessaryBeing truthmakers.ontic false := by
  refine ⟨?_, ?_, ?_, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w r f h
    cases r with
    | exist x => cases f with
      | some => exact ⟨h, trivial⟩
      | exist _ => exact h.elim
      | law => exact h.elim
    | some => exact h.elim
    | law => exact h.elim
  · intro w x; exact Iff.rfl
  · intro v r h; exact existReason_instance _ v r _ h rfl
  · intro v; exact ⟨fun _ => ⟨v, rfl⟩, fun _ => trivial⟩
  · intro v _; exact ⟨.exist v, rfl⟩
  · intro v _; exact trivial
  · intro w r f h v _ _
    cases r with
    | exist x => cases f with
      | some => exact trivial
      | exist _ => exact h.elim
      | law => exact h.elim
    | some => exact h.elim
    | law => exact h.elim
  · exact ⟨rfl, true, trivial, Bool.noConfusion⟩
  · rintro ⟨r, hr⟩
    cases r with
    | exist x =>
      have h0 : x = false := hr false trivial
      have h1 : x = true := hr true trivial
      exact Bool.noConfusion (h0.symm.trans h1)
    | some => exact hr false trivial
    | law => exact hr false trivial
  · exact alternating_no_necessary _ (fun _ => trivial) _ _

theorem lawGround_facts :
    Factive lawGround ∧ Coherent lawGround ∧ ¬ InstanceGrounding lawGround .some ∧
    Access lawGround false false ∧ ExistentialFact lawGround .some ∧
    UniformGround lawGround false .some ∧
    TruthCore.Explanation.StoppingPoints.NecessaryFact lawGround false .law ∧
    Necessitating lawGround ∧ Contingent lawGround false (.exist false) ∧
    (∀ w y x, ¬ lawGround.ontic.Causes w y x) ∧ ¬ NecessaryBeing lawGround.ontic false := by
  refine ⟨?_, ?_, ?_, trivial, ?_, ⟨.law, fun _ _ => trivial⟩, fun _ _ => rfl, ?_, ?_,
    fun _ _ _ h => h, ?_⟩
  · intro w r f h
    cases r with
    | law => cases f with
      | some => exact ⟨rfl, trivial⟩
      | exist _ => exact h.elim
      | law => exact h.elim
    | some => exact h.elim
    | exist _ => exact h.elim
  · intro w x; exact Iff.rfl
  · intro h
    obtain ⟨x, hx⟩ := h false .law trivial
    exact exist_ne_law x hx
  · intro v; exact ⟨fun _ => ⟨v, rfl⟩, fun _ => trivial⟩
  · intro w r f h v _ _
    cases r with
    | law => cases f with
      | some => exact trivial
      | exist _ => exact h.elim
      | law => exact h.elim
    | some => exact h.elim
    | exist _ => exact h.elim
  · exact ⟨rfl, true, trivial, Bool.noConfusion⟩
  · exact alternating_no_necessary _ (fun _ => trivial) _ _

theorem nonfactive_facts :
    ¬ Factive nonfactive ∧ Coherent nonfactive ∧ InstanceGrounding nonfactive .some ∧
    Access nonfactive false false ∧ UniformGround nonfactive false .some ∧
    ¬ NecessaryBeing nonfactive.ontic false := by
  refine ⟨?_, fun _ _ => Iff.rfl, fun v r h => existReason_instance _ v r _ h rfl, trivial,
    ⟨.exist false, fun _ _ => rfl⟩, alternating_no_necessary _ (fun _ => trivial) _ _⟩
  intro h
  exact Bool.noConfusion (h true (.exist false) .some rfl).1

theorem incoherent_facts :
    Factive incoherent ∧ ¬ Coherent incoherent ∧ InstanceGrounding incoherent .some ∧
    Access incoherent false false ∧ UniformGround incoherent false .some ∧
    ¬ NecessaryBeing incoherent.ontic false := by
  refine ⟨?_, ?_, fun v r h => existReason_instance _ v r _ h rfl, trivial,
    ⟨.exist false, fun _ _ => rfl⟩, alternating_no_necessary _ (fun _ => trivial) _ _⟩
  · intro w r f h
    cases r with
    | exist x => cases f with
      | some => exact ⟨trivial, trivial⟩
      | exist _ => exact h.elim
      | law => exact h.elim
    | some => exact h.elim
    | law => exact h.elim
  · intro h
    exact Bool.noConfusion ((h true false).1 trivial)

theorem unseenActual_facts :
    Factive unseenActual ∧ Coherent unseenActual ∧ InstanceGrounding unseenActual .some ∧
    ¬ Access unseenActual false false ∧ UniformGround unseenActual false .some ∧
    NecessaryAt unseenActual.ontic false true ∧
    ¬ NecessaryBeing unseenActual.ontic false := by
  refine ⟨?_, fun _ _ => Iff.rfl, fun v r h => existReason_instance _ v r _ h rfl,
    fun h => Bool.noConfusion h, ⟨.exist true, fun v hv => ⟨hv, rfl⟩⟩,
    fun v hv => ⟨hv, rfl⟩, ?_⟩
  · intro w r f h
    cases r with
    | exist x => cases f with
      | some => exact ⟨h, h.1⟩
      | exist _ => exact h.elim
      | law => exact h.elim
    | some => exact h.elim
    | law => exact h.elim
  · rintro ⟨x, hx, _⟩
    exact Bool.noConfusion hx.1

theorem fixedBearer_facts :
    Factive fixedBearer ∧ Coherent fixedBearer ∧ InstanceGrounding fixedBearer .some ∧
    Access fixedBearer false false ∧ ExistentialFact fixedBearer .some ∧
    UniformGround fixedBearer false .some ∧ NecessaryBeing fixedBearer.ontic false ∧
    ContingentAt fixedBearer.ontic false false ∧
    (∀ w y x, ¬ fixedBearer.ontic.Causes w y x) := by
  refine ⟨?_, fun _ _ => Iff.rfl, fun v r h => existReason_instance _ v r _ h rfl, trivial,
    fun v => ⟨fun _ => ⟨true, Or.inl rfl⟩, fun _ => trivial⟩,
    ⟨.exist true, fun _ _ => rfl⟩, ⟨true, Or.inl rfl, fun _ _ => Or.inl rfl⟩,
    ⟨Or.inr rfl, true, trivial, ?_⟩, fun _ _ _ h => h⟩
  · intro w r f h
    cases r with
    | exist x => cases f with
      | some => exact ⟨Or.inl h, trivial⟩
      | exist _ => exact h.elim
      | law => exact h.elim
    | some => exact h.elim
    | law => exact h.elim
  · intro h
    cases h with
    | inl h => exact Bool.noConfusion h
    | inr h => exact Bool.noConfusion h

/-! ## Certificate -/

theorem disjunctionGroundMap : DisjunctionGroundMap :=
  ⟨fun _ _ _ A a d => uniform_local A a d,
   fun _ _ _ A a d => local_necessary A a d,
   fun _ _ _ A a d => local_population A a d,
   fun _ _ _ A a d => uniform_necessary A a d,
   fun _ _ _ A a d => uniform_fork A a d,
   truthmakers_facts, lawGround_facts, nonfactive_facts, incoherent_facts,
   unseenActual_facts, fixedBearer_facts⟩

end TruthCore.Results.Explanation.DisjunctionGround
