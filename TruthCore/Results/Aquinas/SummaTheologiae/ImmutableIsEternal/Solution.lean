import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.BoethianEternity
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityEternity
namespace TruthCore.Results.Aquinas.SummaTheologiae.ImmutableIsEternal
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- ST I q.10 a.1 co. with q.9 a.1 co.: what is in potency in no respect has
neither beginning nor end of life and no succession in it, since either would be
a change, and whatever is changed in any way is in some way in potency. -/
theorem pureActInterminableTotaSimul {Being Respect Time State : Type} [LT Time]
    (InPotency : Being → Respect → Prop)
    (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State)
    (hChange : ChangeRequiresPotencyReading InPotency LivesAt lifeStateAt) :
    ∀ x, PureAct InPotency x →
      Interminable LivesAt x ∧ TotaSimul LivesAt lifeStateAt x := by
  intro x hx
  refine ⟨fun hBegins => ?_, fun hSucc => ?_⟩
  · obtain ⟨r, hr⟩ := hChange x (Or.inl hBegins)
    exact hx r hr
  · obtain ⟨r, hr⟩ := hChange x (Or.inr hSucc)
    exact hx r hr

/-- STMT-IMMUTABLE-IS-ETERNAL with Boethian eternity for its `Eternal` parameter:
whatever is in potency in no respect possesses life interminably and all at once,
from the q.9 a.1 change principle and the open premise that pure act lives. -/
theorem immutableIsEternal {Being Respect Time State : Type} [LT Time]
    (InPotency : Being → Respect → Prop)
    (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State)
    (hChange : ChangeRequiresPotencyReading InPotency LivesAt lifeStateAt)
    (hLife : PureActLivesReading InPotency LivesAt) :
    ImmutableIsEternalReading InPotency (BoethianEternal LivesAt lifeStateAt) := by
  intro x hx
  have hMarks := pureActInterminableTotaSimul InPotency LivesAt lifeStateAt hChange x hx
  exact ⟨hLife x hx, hMarks.1, hMarks.2⟩

/-! ### Controls: each premise is needed

All models have one being `()`, one respect, no potency (so the being is pure
act), and two times `false < true` (core's order on `Bool`). They are formal
non-entailment witnesses, not historical or theological counterworlds. -/

/-- Without the change principle: a pure-act being that lives at both times
with different life-states (successive operation) satisfies the life premise
and is not Boethian-eternal. -/
theorem changePrincipleNeeded :
    ¬ ∀ (Being Respect Time State : Type) [LT Time]
      (InPotency : Being → Respect → Prop)
      (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State),
      PureActLivesReading InPotency LivesAt →
      ImmutableIsEternalReading InPotency (BoethianEternal LivesAt lifeStateAt) := by
  intro h
  have hEternal := @h Unit Unit Bool Bool _ (fun _ _ => False) (fun _ _ => True)
    (fun _ t => t) (fun _ _ => ⟨false, trivial⟩) () (fun _ hr => hr)
  exact hEternal.2.2 ⟨false, true, by decide, trivial, trivial, Bool.noConfusion⟩

/-- Without the life premise: an immutable being that never lives (as a number is
immutable but not living, q.10 a.1 ad 2) satisfies the change principle
vacuously and is not Boethian-eternal. -/
theorem lifePremiseNeeded :
    ¬ ∀ (Being Respect Time State : Type) [LT Time]
      (InPotency : Being → Respect → Prop)
      (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State),
      ChangeRequiresPotencyReading InPotency LivesAt lifeStateAt →
      ImmutableIsEternalReading InPotency (BoethianEternal LivesAt lifeStateAt) := by
  intro h
  have hChange : ChangeRequiresPotencyReading (Respect := Unit)
      (fun (_ : Unit) _ => False) (fun (_ : Unit) (_ : Bool) => False)
      (fun (_ : Unit) (_ : Bool) => ()) := by
    intro x hVar
    rcases hVar with ⟨_, _, _, hIff⟩ | ⟨_, _, _, hLive, _, _⟩
    · exact absurd (Iff.intro (fun h => h) (fun h => h)) hIff
    · exact hLive.elim
  obtain ⟨⟨_, hLives⟩, _, _⟩ := @h Unit Unit Bool Unit _ (fun _ _ => False)
    (fun _ _ => False) (fun _ _ => ()) hChange () (fun _ hr => hr)
  exact hLives

/-- A change principle restricted to succession of life-states (not beginning or
ceasing to live) does not suffice: a pure-act being that begins to live and keeps
one constant life-state satisfies it and the life premise, yet its life has a
beginning. So the change principle must count beginning to live as a change. -/
theorem successionOnlyPrincipleInsufficient :
    ¬ ∀ (Being Respect Time State : Type) [LT Time]
      (InPotency : Being → Respect → Prop)
      (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State),
      (∀ x, LifeHasSuccession LivesAt lifeStateAt x → ∃ r, InPotency x r) →
      PureActLivesReading InPotency LivesAt →
      ImmutableIsEternalReading InPotency (BoethianEternal LivesAt lifeStateAt) := by
  intro h
  have hSucc : ∀ x : Unit, LifeHasSuccession
      (fun (_ : Unit) (t : Bool) => t = true) (fun (_ : Unit) (_ : Bool) => ()) x →
        ∃ _ : Unit, False := by
    intro x ⟨_, _, _, _, _, hNe⟩
    exact absurd rfl hNe
  obtain ⟨_, hInterminable, _⟩ := @h Unit Unit Bool Unit _ (fun _ _ => False)
    (fun _ t => t = true) (fun _ _ => ()) hSucc (fun _ _ => ⟨true, rfl⟩) ()
    (fun _ hr => hr)
  exact hInterminable ⟨false, true, by decide, fun hIff => Bool.noConfusion (hIff.2 rfl)⟩

/-- Joint model: both premises hold and some being is pure act, so the derivation
is not vacuous; the pure-act being lives at both times in one constant state. -/
theorem premisesJointlySatisfiable :
    ∃ (Being Respect Time State : Type) (_ : LT Time)
      (InPotency : Being → Respect → Prop)
      (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State),
      ChangeRequiresPotencyReading InPotency LivesAt lifeStateAt ∧
      PureActLivesReading InPotency LivesAt ∧
      (∃ x, PureAct InPotency x) := by
  refine ⟨Unit, Unit, Bool, Unit, inferInstance, fun _ _ => False, fun _ _ => True,
    fun _ _ => (), ?_, fun _ _ => ⟨false, trivial⟩, ⟨(), fun _ hr => hr⟩⟩
  intro x hVar
  rcases hVar with ⟨_, _, _, hIff⟩ | ⟨_, _, _, _, _, hNe⟩
  · exact absurd (Iff.intro (fun _ => trivial) (fun _ => trivial)) hIff
  · exact absurd rfl hNe

end TruthCore.Results.Aquinas.SummaTheologiae.ImmutableIsEternal
