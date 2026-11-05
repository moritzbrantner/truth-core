module

public import TruthCore.Explanation.TruthmakerTheories
public import TruthCore.Results.Explanation.DisjunctionGround.Solution

@[expose] public section
namespace TruthCore.Results.Explanation.TruthmakerTheories
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.DisjunctionGround
open TruthCore.Explanation.TruthmakerTheories
open TruthCore.German.Kant.CosmologicalInference
variable {W B F : Type}

theorem uniformNecessary (A : Arena W B F) (M : Making W B F) (a : W) (f : F)
    (hi : WorldImmanent A M) (ha : Access A a a)
    (hu : UniformMaker A M a f) : NecessaryBeing A.ontic a := by
  obtain ⟨b, hb⟩ := hu
  exact ⟨b, hi a b f (hb a ha), fun v hv => hi v b f (hb v hv)⟩

theorem localSound : Sound truthmakers localMaking := by
  constructor
  · rintro w b f ⟨rfl, hf⟩
    rcases hf with rfl | rfl
    · exact trivial
    · exact rfl
  · rintro w b f ⟨h, _⟩
    exact h

theorem localMax : Maximalist truthmakers localMaking := by
  refine ⟨localSound, ?_⟩
  intro w f _ hf
  cases f with
  | exist x => exact ⟨x, hf, Or.inr rfl⟩
  | some => exact ⟨w, rfl, Or.inl rfl⟩
  | law => exact (Bool.noConfusion hf)

theorem localNecessitates : MakerNecessitation truthmakers localMaking := by
  rintro w b f ⟨_, hf⟩ v _ hv
  rcases hf with rfl | rfl
  · exact trivial
  · exact hv

theorem restrictedSound : Sound truthmakers restrictedMaking := by
  constructor
  · rintro w b f ⟨hb, hf⟩
    exact localSound.1 w b f ⟨hb, Or.inr hf⟩
  · rintro w b f ⟨hb, _⟩; exact hb

theorem restrictedCoverage :
    Restricted truthmakers restrictedMaking (ExistenceScope truthmakers) := by
  refine ⟨restrictedSound, ?_⟩
  rintro w f ⟨b, rfl⟩ hf
  exact ⟨b, hf, rfl⟩

theorem noSound (A : Arena W B F) : Sound A noMaking := by
  exact ⟨fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩

theorem fixedSound : Sound fixedBearer fixedMaking := by
  constructor
  · rintro w b f ⟨hb, hf⟩
    rcases hf with rfl | rfl
    · exact trivial
    · exact hb
  · rintro w b f ⟨hb, _⟩; exact hb

theorem fixedMax : Maximalist fixedBearer fixedMaking := by
  refine ⟨fixedSound, ?_⟩
  intro w f _ hf
  cases f with
  | exist x => exact ⟨x, hf, Or.inr rfl⟩
  | some => exact ⟨true, Or.inl rfl, Or.inl rfl⟩
  | law => exact hf.elim

theorem fixedNecessitates : MakerNecessitation fixedBearer fixedMaking := by
  rintro w b f ⟨_, hf⟩ v _ hv
  rcases hf with rfl | rfl
  · exact trivial
  · exact hv

theorem switchingMax : Maximalist fixedBearer switchingFixedMaking := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro w b f ⟨hb, hf⟩
    rcases hf with ⟨rfl, _⟩ | rfl
    · exact trivial
    · exact hb
  · rintro w b f ⟨hb, _⟩; exact hb
  · intro w f _ hf
    cases f with
    | exist x => exact ⟨x, hf, Or.inr rfl⟩
    | some => exact ⟨w, Or.inr rfl, Or.inl ⟨rfl, rfl⟩⟩
    | law => exact hf.elim

theorem switchingNoUniform : ¬ UniformMaker fixedBearer switchingFixedMaking false .some := by
  rintro ⟨b, hb⟩
  have eqw : ∀ w, b = w := by
    intro w
    rcases (hb w trivial).2 with h | h
    · exact h.2
    · exact DFact.noConfusion h
  exact Bool.noConfusion ((eqw false).symm.trans (eqw true))

theorem theoryMap : TheoryMap := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W B F A M scope h
    exact ⟨⟨h.1, fun w f _ hf => h.2 w f trivial hf⟩, h.1⟩
  · intro W B F A hf hc
    exact ⟨fun w b f h => (hf w (A.exist b) f h).2,
      fun w b f h => (hc w b).1 (hf w (A.exist b) f h).1⟩
  · exact fun W B F A M a f hi ha hu => uniformNecessary A M a f hi ha hu
  · intro W B F A M a f hm hn v hv
    exact hm.2 v f trivial (hn v hv)
  · refine ⟨localMax, localNecessitates, fun v _ => ⟨v, rfl, Or.inl rfl⟩, ?_,
      TruthCore.Results.Explanation.DisjunctionGround.truthmakers_facts.2.2.2.2.2.2.2.2.2.2⟩
    intro hu
    exact TruthCore.Results.Explanation.DisjunctionGround.truthmakers_facts.2.2.2.2.2.2.2.2.2.2
      (uniformNecessary truthmakers localMaking false .some localSound.2 trivial hu)
  · refine ⟨restrictedCoverage, ⟨.exist false, ⟨false, rfl⟩, rfl,
      false, rfl, rfl⟩, trivial, ?_⟩
    rintro ⟨b, ⟨_, h⟩, _⟩; exact DFact.noConfusion h
  · refine ⟨noSound truthmakers, localSound, ⟨false, .some, rfl, Or.inl rfl⟩, ?_⟩
    intro h; obtain ⟨_, hb⟩ := h false trivial; exact hb
  · exact ⟨fixedMax, fixedNecessitates, ⟨true, fun _ _ => ⟨Or.inl rfl, Or.inl rfl⟩⟩,
      TruthCore.Results.Explanation.DisjunctionGround.fixedBearer_facts.2.2.2.2.2.2.1,
      TruthCore.Results.Explanation.DisjunctionGround.fixedBearer_facts.2.2.2.2.2.2.2.2⟩
  · exact ⟨switchingMax, TruthCore.Results.Explanation.DisjunctionGround.fixedBearer_facts.2.2.2.2.2.2.1, switchingNoUniform⟩
  · refine ⟨TruthCore.Results.Explanation.DisjunctionGround.lawGround_facts.2.2.2.2.2.1, ?_⟩
    intro M hi hu
    exact TruthCore.Results.Explanation.DisjunctionGround.lawGround_facts.2.2.2.2.2.2.2.2.2.2
      (uniformNecessary lawGround M false .some hi trivial hu)

theorem negativeEmpty : EmptyFact negativeArena .empty := by
  intro w
  cases w with
  | false => exact ⟨fun h => Bool.noConfusion h,
      fun h => (h () rfl).elim⟩
  | true => exact ⟨fun _ _ h => Bool.noConfusion h, fun _ => rfl⟩

theorem negativeRestricted :
    Restricted negativeArena negativeMaking (ExistenceScope negativeArena) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro w b f ⟨hw, rfl⟩; exact hw
  · rintro w b f ⟨hw, _⟩; exact hw
  · rintro w f ⟨b, rfl⟩ hf
    exact ⟨b, hf, rfl⟩

theorem negativeMap : NegativeMap := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W B F A M w f he hf ht hi
    obtain ⟨b, hb⟩ := ht hf
    exact (he w).1 hf b (hi w b f hb)
  · refine ⟨negativeEmpty, fun _ _ => Iff.rfl, negativeRestricted,
      ⟨.positive, ⟨(), rfl⟩, rfl, (), rfl, rfl⟩, rfl, ?_⟩
    intro hm
    obtain ⟨_, hw, _⟩ := hm.2 true .empty trivial rfl
    exact Bool.noConfusion hw
  · exact ⟨Bool.noConfusion, fun h => False.elim (Bool.noConfusion h : False), noSound negativeArena⟩
  · refine ⟨rfl, noSound negativeArena, ?_⟩
    intro h; obtain ⟨_, hb⟩ := h rfl; exact hb
  · refine ⟨rfl, fun _ => ⟨(), rfl, rfl⟩, ?_, ?_⟩
    · rintro w b f ⟨hw, rfl⟩; exact hw
    · intro hi
      exact Bool.noConfusion (hi true () .empty ⟨rfl, rfl⟩)
  · exact ⟨⟨⟨fun _ _ _ _ => trivial, fun _ _ _ _ => trivial⟩,
      fun _ _ _ _ => ⟨(), trivial⟩⟩,
      fun _ => ⟨fun _ _ h => h, fun _ => trivial⟩,
      fun _ h => h, ⟨(), trivial, trivial⟩,
      fun h => h () () .empty trivial⟩

end TruthCore.Results.Explanation.TruthmakerTheories
