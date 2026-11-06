module

public import TruthCore.Logic.FitchKnowability

@[expose] public section

namespace TruthCore.Results.Logic.FitchKnowability
open TruthCore.Modal TruthCore.Logic.FitchKnowability

/-- The laws apply at the possible knower, avoiding any local necessitation. -/
theorem mooreUnknowable {W : Type} (c : Context W) (p : W → Prop)
    (laws : RelevantLaws c p) : MooreUnknowable c p := by
  rintro ⟨v, access, known⟩
  exact ((laws v access).1 known).2 ((laws v access).2 known)

/-- Constructive reductio proves only double-negated knowledge. -/
theorem doubleNegatedKnowledge {W : Type} (c : Context W) (p : W → Prop)
    (laws : RelevantLaws c p) (hInstance : MooreInstance c p) :
    DoubleNegatedKnowledge c p := by
  intro truth unknown
  exact mooreUnknowable c p laws (hInstance ⟨truth, unknown⟩)

/-- Relevant stability is an explicit premise, never an ambient classical tactic. -/
theorem stabilityUpgrade {W : Type} (c : Context W) (p : W → Prop)
    (double : DoubleNegatedKnowledge c p) (stable : KnowledgeStable c p) :
    TruthKnown c p := by
  intro truth
  exact stable (double truth)

/-- Restricted knowability needs the Moore content in its domain. -/
theorem restrictedInstance {W : Type} (c : Context W) (C : (W → Prop) → Prop)
    (p : W → Prop) (knowable : RestrictedKnowability c C)
    (admissible : MooreAdmissible c C p) : MooreInstance c p :=
  knowable (Moore c p) admissible

/-- All-content global laws specialize to the weak accessed-world core. -/
theorem relevantFromGlobal {W : Type} (c : Context W) (p : W → Prop)
    (laws : GlobalLaws c) : RelevantLaws c p := by
  intro v _
  exact ⟨laws.1 _ v, fun h => (laws.2 p (fun w => ¬ c.knows p w) v h).1⟩

local instance : NeZero 4 := ⟨Nat.noConfusion⟩

private abbrev atom := survivorAtom
private abbrev epistemic := survivorEpistemic
private abbrev context := survivorContext

private theorem eRefl : Reflexive epistemic := fun _ => Or.inr rfl
private theorem eSymm : Symmetric epistemic := by
  intro u v h
  rcases h with ⟨hu, hv⟩ | h
  · exact Or.inl ⟨hv, hu⟩
  · exact Or.inr h.symm
private theorem eTrans : Transitive epistemic := by
  intro u v w huv hvw
  rcases huv with ⟨hu, hv⟩ | h
  · rcases hvw with ⟨_, hw⟩ | h
    · exact Or.inl ⟨hu, hw⟩
    · cases h
      exact Or.inl ⟨hu, hv⟩
  · cases h
    exact hvw

/-- Relational knowledge supplies factivity and extraction, rather than flags. -/
private theorem globalLaws : GlobalLaws context := by
  constructor
  · intro q w h
    exact axiomT_valid epistemic eRefl (.atom ()) (fun v (_ : Unit) => q v) w h
  · intro p q w h
    exact ⟨fun v hv => (h v hv).1, fun v hv => (h v hv).2⟩

private theorem invariantBooleanClosed : BooleanClosed (AtomInvariant atom) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _
    exact Iff.rfl
  · intro _ _ _
    exact Iff.rfl
  · intro p q hp hq u v h
    exact and_congr (hp u v h) (hq u v h)
  · intro p q hp hq u v h
    exact or_congr (hp u v h) (hq u v h)
  · intro p hp u v h
    exact not_congr (hp u v h)

private theorem zeroAtom : atom 0 := Or.inl rfl
private theorem twoAtom : atom 2 := Or.inr rfl
private theorem threeNotAtom : ¬ atom 3 := by
  unfold atom survivorAtom
  decide
private theorem oneNotAtom : ¬ atom 1 := by
  unfold atom survivorAtom
  decide

private theorem endpointKnown (q : Fin 4 → Prop) (e : Fin 4)
    (bound : 2 ≤ e.val) (truth : q e) : context.knows q e := by
  intro v hv
  rcases hv with ⟨he, _⟩ | he
  · exact False.elim (Nat.not_lt_of_ge bound he)
  · cases he
    exact truth

private theorem globalEquivalence : GlobalRestrictedEquivalence context (AtomInvariant atom) := by
  intro q invariant w
  constructor
  · intro truth
    by_cases h : w = 0 ∨ w = 2
    · refine ⟨2, ⟨fun _ => twoAtom, fun _ => h⟩, ?_⟩
      exact endpointKnown q 2 (by decide)
        ((invariant w 2 ⟨fun _ => twoAtom, fun _ => h⟩).mp truth)
    · refine ⟨3, ⟨fun hw => (h hw).elim, fun ht => (threeNotAtom ht).elim⟩, ?_⟩
      exact endpointKnown q 3 (by decide)
        ((invariant w 3 ⟨fun hw => (h hw).elim, fun ht => (threeNotAtom ht).elim⟩).mp truth)
  · rintro ⟨v, access, known⟩
    exact (invariant w v access).mpr (globalLaws.1 q v known)

private theorem actualUnknown : Moore context atom context.actual := by
  refine ⟨zeroAtom, ?_⟩
  intro known
  exact oneNotAtom (known 1 (Or.inl ⟨by decide, by decide⟩))

/-- Four-world S5 survivor, including Boolean closure, global biconditional
restricted knowability and actual ignorance. E is explicitly not contained in R. -/
theorem restrictedSurvivor : RestrictedSurvivor := by
  refine ⟨rfl, eRefl, eSymm, eTrans,
    (fun _ => Iff.rfl), (fun _ _ h => h.symm), (fun _ _ _ h₁ h₂ => h₁.trans h₂),
    globalLaws, invariantBooleanClosed, (fun _ _ h => h), globalEquivalence,
    actualUnknown, ?_, ?_⟩
  · intro admissible
    have m2 := (admissible 0 2 ⟨fun _ => twoAtom, fun _ => zeroAtom⟩).mp actualUnknown
    exact m2.2 (endpointKnown atom 2 (by decide) twoAtom)
  · intro subset
    have bad := subset 0 1 (Or.inl ⟨by decide, by decide⟩)
    exact oneNotAtom (bad.mp zeroAtom)

end TruthCore.Results.Logic.FitchKnowability
