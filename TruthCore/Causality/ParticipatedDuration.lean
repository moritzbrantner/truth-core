module

public import TruthCore.Causality.EndlessTemporalDuration

/-! ETERNITY_AND_STABLE_DURATION_2, the owner-selected disjunctive extended use.
The contextual duration scale and standard, stability of being/operation, and
reception from God are explicit interpretation inputs. They do not identify
proper eternity or supply the measure accounts of time and aevum. -/

@[expose] public section
namespace TruthCore.Causality.ParticipatedDuration

/-- The aspect in which stability is received; these are not new eternity senses. -/
inductive Aspect where
  | being
  | operation

/-- Stability and reception retain their philosophical interpretation as open
primitives. Stability means stable being or stable operation, respectively;
reception means that very aspect is received from God, not merely caused by
some being. No equation with whole-life state constancy is imposed. -/
structure Profile (Time Magnitude : Type) where
  present : Time → Prop
  duration : Magnitude
  contextualStandard : Magnitude
  stable : Aspect → Prop
  receivedFromGod : Aspect → Prop

/-- Never ceasing after presence begins: nonempty, without a final present
moment, and present at every later admitted moment. No beginninglessness or
total order is required. The supplied order/presence applicability stays open. -/
def NeverCeasing {Time : Type} [Preorder Time] (present : Time → Prop) : Prop :=
  EndlessTemporalDuration.FutureUnending present ∧
    ∀ t, present t → ∀ later, t ≤ later → present later

/-- One extended sense with THREE alternatives, not three jointly necessary
conditions. Long duration compares a nonempty duration to the supplied standard;
participation requires stability AND reception in the SAME selected aspect.
No other branch is required, and proper Eternal is an independent predicate. -/
def Extended {Time Magnitude : Type} [Preorder Time] [LT Magnitude]
    (p : Profile Time Magnitude) : Prop :=
  NeverCeasing p.present ∨
    ((∃ t, p.present t) ∧ p.contextualStandard < p.duration) ∨
    ((∃ t, p.present t) ∧ ∃ a, p.stable a ∧ p.receivedFromGod a)

/-- Populated unending duration, below the contextual threshold and without
participation: the first branch alone suffices. -/
def unending : Profile Nat Nat :=
  ⟨fun _ => True, 0, 1, fun _ => False, fun _ => False⟩

/-- A finite duration can exceed its contextual standard with no participation. -/
def longFinite : Profile Nat Nat :=
  ⟨fun t => t ≤ 2, 2, 1, fun _ => False, fun _ => False⟩

/-- A short finite duration with stable operation received from God. Stable
being is not required. Neither of the first two branches holds. -/
def participated : Profile Nat Nat :=
  ⟨fun t => t ≤ 2, 0, 1, (· = .operation), (· = .operation)⟩

/-- Stability and reception in DIFFERENT aspects do not establish participation. -/
def mismatched : Profile Nat Nat :=
  { participated with receivedFromGod := (· = .being) }

/-- Controls independently exercise all alternatives and a failed conjunction.
These are formal interpretation witnesses, not source or reality certificates. -/
theorem branchControls :
    (Extended unending ∧ ¬ unending.contextualStandard < unending.duration ∧
      ¬ ∃ a, unending.stable a ∧ unending.receivedFromGod a) ∧
    (Extended longFinite ∧ ¬ NeverCeasing longFinite.present ∧
      ¬ ∃ a, longFinite.stable a ∧ longFinite.receivedFromGod a) ∧
    (Extended participated ∧ ¬ NeverCeasing participated.present ∧
      ¬ participated.contextualStandard < participated.duration) ∧
    ¬ Extended mismatched := by
  have hEnd : ¬ NeverCeasing (fun t : Nat => t ≤ 2) := by
    intro h
    exact EndlessTemporalDuration.endpointFails _ 2 (by decide)
      (fun _ ht hlt => Nat.not_lt_of_ge ht hlt) h.1
  refine ⟨⟨?_, by decide, ?_⟩, ⟨?_, hEnd, ?_⟩,
    ⟨?_, hEnd, by decide⟩, ?_⟩
  · exact Or.inl ⟨⟨⟨0, trivial⟩, fun t _ => ⟨t + 1, Nat.lt_succ_self t, trivial⟩⟩,
      fun _ _ _ _ => trivial⟩
  · rintro ⟨a, h, _⟩; exact h
  · exact Or.inr (Or.inl ⟨⟨0, (show (0 : Nat) ≤ 2 by decide)⟩, by decide⟩)
  · rintro ⟨a, h, _⟩; exact h
  · exact Or.inr (Or.inr ⟨⟨0, (show (0 : Nat) ≤ 2 by decide)⟩, .operation, rfl, rfl⟩)
  · intro h
    rcases h with hn | hl | ⟨_, a, hs, hr⟩
    · exact hEnd hn
    · exact (by decide : ¬ (1 : Nat) < 0) hl.2
    · cases a <;> cases hs <;> cases hr

/-- Stability alone and reception alone are insufficient for the third branch.
A strict contextual threshold also matters to the finite long-duration witness. -/
theorem omissions :
    ¬ Extended { participated with receivedFromGod := fun _ => False } ∧
    ¬ Extended { participated with stable := fun _ => False } ∧
    ¬ Extended { longFinite with contextualStandard := 2 } := by
  have hEnd : ¬ NeverCeasing (fun t : Nat => t ≤ 2) := by
    intro h
    exact EndlessTemporalDuration.endpointFails _ 2 (by decide)
      (fun _ ht hlt => Nat.not_lt_of_ge ht hlt) h.1
  constructor
  · rintro (hn | hl | ⟨_, a, _, hr⟩)
    · exact hEnd hn
    · exact (by decide : ¬ (1 : Nat) < 0) hl.2
    · exact hr
  constructor
  · rintro (hn | hl | ⟨_, a, hs, _⟩)
    · exact hEnd hn
    · exact (by decide : ¬ (1 : Nat) < 0) hl.2
    · exact hs
  · rintro (hn | hl | ⟨_, a, hs, _⟩)
    · exact hEnd hn
    · exact (by decide : ¬ (2 : Nat) < 2) hl.2
    · exact hs

/-- Empty presence cannot pass any branch, even with positive primitive flags
and a magnitude exceeding the standard. -/
theorem emptyFails (duration standard : Nat) (stable received : Aspect → Prop) :
    ¬ Extended (⟨fun _ : Nat => False, duration, standard, stable, received⟩) := by
  rintro (h | ⟨⟨_, h⟩, _⟩ | ⟨⟨_, h⟩, _⟩)
  · exact EndlessTemporalDuration.emptyFails h.1
  · exact h
  · exact h

/-- Even the three positive witnesses fail an independently interpreted proper
eternity predicate. There is no implicit extended-to-proper recognition. -/
theorem properRecognitionNotForced :
    ∃ proper : Profile Nat Nat → Prop,
      Extended unending ∧ Extended longFinite ∧ Extended participated ∧
      ¬ proper unending ∧ ¬ proper longFinite ∧ ¬ proper participated := by
  exact ⟨fun _ => False, branchControls.1.1, branchControls.2.1.1,
    branchControls.2.2.1.1, id, id, id⟩

end TruthCore.Causality.ParticipatedDuration
