import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.BoethianEternity
namespace TruthCore.Results.Aquinas.SummaTheologiae.ImmutableIsBoethianEternal
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- ST I q.10 a.1 co. with q.9 a.1 co.: what is in potency in no respect has
neither beginning nor end of life and no succession in it, since each would put
it in potency in some respect. -/
theorem pureActInterminableTotaSimul {Being Respect Time State : Type} [LT Time]
    (InPotency : Being → Respect → Prop)
    (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State)
    (hSuccession : SuccessionRequiresPotencyReading InPotency LivesAt lifeStateAt)
    (hBoundary : LifeBoundaryRequiresPotencyReading InPotency LivesAt) :
    ∀ x, PureAct InPotency x →
      Interminable LivesAt x ∧ TotaSimul LivesAt lifeStateAt x := by
  intro x hx
  refine ⟨fun hBegins => ?_, fun hSucc => ?_⟩
  · obtain ⟨r, hr⟩ := hBoundary x hBegins
    exact hx r hr
  · obtain ⟨r, hr⟩ := hSuccession x hSucc
    exact hx r hr

/-- Whatever is in potency in no respect is Boethian-eternal: it possesses life
interminably and all at once. From the q.9 a.1 succession principle, the open
boundary premise and the open premise that pure act lives. This is the typed
specialization, not the primitive-`Eternal` statement the root routes use. -/
theorem immutableIsBoethianEternal {Being Respect Time State : Type} [LT Time]
    (InPotency : Being → Respect → Prop)
    (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State)
    (hSuccession : SuccessionRequiresPotencyReading InPotency LivesAt lifeStateAt)
    (hBoundary : LifeBoundaryRequiresPotencyReading InPotency LivesAt)
    (hLife : PureActLivesReading InPotency LivesAt) :
    ImmutableIsBoethianEternalReading InPotency LivesAt lifeStateAt := by
  intro x hx
  have hMarks :=
    pureActInterminableTotaSimul InPotency LivesAt lifeStateAt hSuccession hBoundary x hx
  exact ⟨hLife x hx, hMarks.1, hMarks.2⟩

/-! ### Controls: each premise is needed

All models have one being `()`, one respect, no potency (so the being is pure
act), and two times `false < true` (core's order on `Bool`). They are formal
non-entailment witnesses, not historical or theological counterworlds. -/

/-- Without the succession premise: a pure-act being that lives at both times
with different life-states (successive operation) satisfies the boundary and life
premises and is not Boethian-eternal. -/
theorem successionPremiseNeeded :
    ¬ ∀ (Being Respect Time State : Type) [LT Time]
      (InPotency : Being → Respect → Prop)
      (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State),
      LifeBoundaryRequiresPotencyReading InPotency LivesAt →
      PureActLivesReading InPotency LivesAt →
      ImmutableIsBoethianEternalReading InPotency LivesAt lifeStateAt := by
  intro h
  have hBoundary : LifeBoundaryRequiresPotencyReading (Respect := Unit)
      (fun (_ : Unit) _ => False) (fun (_ : Unit) (_ : Bool) => True) := by
    intro x ⟨_, _, _, hIff⟩
    exact absurd (Iff.intro (fun _ => trivial) (fun _ => trivial)) hIff
  have hEternal := @h Unit Unit Bool Bool _ (fun _ _ => False) (fun _ _ => True)
    (fun _ t => t) hBoundary (fun _ _ => ⟨false, trivial⟩) () (fun _ hr => hr)
  exact hEternal.2.2 ⟨false, true, by decide, trivial, trivial, Bool.noConfusion⟩

/-- Without the boundary premise: a pure-act being that begins to live and keeps
one constant life-state satisfies the succession and life premises, yet its life
has a beginning. -/
theorem boundaryPremiseNeeded :
    ¬ ∀ (Being Respect Time State : Type) [LT Time]
      (InPotency : Being → Respect → Prop)
      (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State),
      SuccessionRequiresPotencyReading InPotency LivesAt lifeStateAt →
      PureActLivesReading InPotency LivesAt →
      ImmutableIsBoethianEternalReading InPotency LivesAt lifeStateAt := by
  intro h
  have hSucc : SuccessionRequiresPotencyReading (Respect := Unit)
      (fun (_ : Unit) _ => False) (fun (_ : Unit) (t : Bool) => t = true)
      (fun (_ : Unit) (_ : Bool) => ()) := by
    intro x ⟨_, _, _, _, _, hNe⟩
    exact absurd rfl hNe
  obtain ⟨_, hInterminable, _⟩ := @h Unit Unit Bool Unit _ (fun _ _ => False)
    (fun _ t => t = true) (fun _ _ => ()) hSucc (fun _ _ => ⟨true, rfl⟩) ()
    (fun _ hr => hr)
  exact hInterminable ⟨false, true, by decide, fun hIff => Bool.noConfusion (hIff.2 rfl)⟩

/-- Without the life premise: an immutable being that never lives (as a number is
immutable but not living, q.10 a.1 ad 2) satisfies the succession and boundary
premises vacuously and is not Boethian-eternal. -/
theorem lifePremiseNeeded :
    ¬ ∀ (Being Respect Time State : Type) [LT Time]
      (InPotency : Being → Respect → Prop)
      (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State),
      SuccessionRequiresPotencyReading InPotency LivesAt lifeStateAt →
      LifeBoundaryRequiresPotencyReading InPotency LivesAt →
      ImmutableIsBoethianEternalReading InPotency LivesAt lifeStateAt := by
  intro h
  have hSucc : SuccessionRequiresPotencyReading (Respect := Unit)
      (fun (_ : Unit) _ => False) (fun (_ : Unit) (_ : Bool) => False)
      (fun (_ : Unit) (_ : Bool) => ()) := by
    intro x ⟨_, _, _, hLive, _, _⟩
    exact hLive.elim
  have hBoundary : LifeBoundaryRequiresPotencyReading (Respect := Unit)
      (fun (_ : Unit) _ => False) (fun (_ : Unit) (_ : Bool) => False) := by
    intro x ⟨_, _, _, hIff⟩
    exact absurd (Iff.intro (fun h => h) (fun h => h)) hIff
  obtain ⟨⟨_, hLives⟩, _, _⟩ := @h Unit Unit Bool Unit _ (fun _ _ => False)
    (fun _ _ => False) (fun _ _ => ()) hSucc hBoundary () (fun _ hr => hr)
  exact hLives

/-- Joint model: all three premises hold and some being is pure act, so the
derivation is not vacuous; the pure-act being lives at both times in one
constant state. -/
theorem premisesJointlySatisfiable :
    ∃ (Being Respect Time State : Type) (_ : LT Time)
      (InPotency : Being → Respect → Prop)
      (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State),
      SuccessionRequiresPotencyReading InPotency LivesAt lifeStateAt ∧
      LifeBoundaryRequiresPotencyReading InPotency LivesAt ∧
      PureActLivesReading InPotency LivesAt ∧
      (∃ x, PureAct InPotency x) := by
  refine ⟨Unit, Unit, Bool, Unit, inferInstance, fun _ _ => False, fun _ _ => True,
    fun _ _ => (), ?_, ?_, fun _ _ => ⟨false, trivial⟩, ⟨(), fun _ hr => hr⟩⟩
  · intro x ⟨_, _, _, _, _, hNe⟩
    exact absurd rfl hNe
  · intro x ⟨_, _, _, hIff⟩
    exact absurd (Iff.intro (fun _ => trivial) (fun _ => trivial)) hIff

end TruthCore.Results.Aquinas.SummaTheologiae.ImmutableIsBoethianEternal
