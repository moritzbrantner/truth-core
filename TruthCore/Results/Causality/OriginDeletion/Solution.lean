module

public import TruthCore.Causality.OriginDeletion
public import TruthCore.Results.Causality.InertEmptiness.Solution
public import TruthCore.Results.Causality.OriginToleranceIdentity.Solution

@[expose] public section

namespace TruthCore.Results.Causality.OriginDeletion
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.OriginDeletion
open TruthCore.Causality.OriginToleranceIdentity (OriginInterface OriginDeterminesAccess NearIsTolerance OriginPlenitude VariedOriginAt)
open TruthCore.Causality.InertEmptiness (EmptinessStaysEmpty PossiblyContingentsAbsentThenPresent)
open TruthCore.Causality.CountTemporalNecessity (HistoryPresenceActual)
open TruthCore.Causality.ToleranceOriginRival.Control (Origin tolerance)
open TruthCore.Modal.TemporalHistory (History)

/-- Presence-to-existence, inert emptiness and a possible contingent-free past
at `w` refute deletion at the worlds accessible from `w`: the witness history
`v` has a concrete individual necessary relative to `v`
(`InertEmptiness.earlierNecessary`), which deletion at `v` would remove. No
frame condition is used. -/
theorem accessibleDeletionExcluded {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (w : W)
    (hPresence : HistoryPresenceActual h)
    (hInert : EmptinessStaysEmpty h Concrete)
    (hPossible : PossiblyContingentsAbsentThenPresent h Concrete w) :
    NoAccessibleDeletion h.ontic Concrete w := by
  intro hDel
  obtain ⟨v, hwv, hBegins⟩ := hPossible
  obtain ⟨c, hc, hExists, hNecessary⟩ :=
    TruthCore.Results.Causality.InertEmptiness.earlierNecessary h Concrete v hPresence hInert hBegins
  obtain ⟨u, hvu, hAbsent⟩ := hDel v hwv c hc hExists
  exact hAbsent (hNecessary u hvu)

/-- If access is exactly shared-origin closeness, origin-compatible deletion
gives deletion at every world. Only the "if" half of origin-determined access
is used: a world lacking `x` whose shared individuals keep near origins is
accessible, whatever `x`'s own origin. -/
theorem originDeletion (m : Ontic W B) (Concrete : B → Prop) (I : OriginInterface W B O)
    (hAccess : OriginDeterminesAccess m I)
    (hCompatible : OriginCompatibleDeletion m Concrete I) :
    WorldwiseDeletion m Concrete := by
  intro v x hx hxv
  obtain ⟨u, hAbsent, hNear⟩ := hCompatible v x hx hxv
  exact ⟨u, (hAccess v u).2 hNear, hAbsent⟩

/-- Conversely, under origin-determined access deletion at every world gives
origin-compatible deletion. Only the "only if" half is used. -/
theorem deletionOriginCompatible (m : Ontic W B) (Concrete : B → Prop)
    (I : OriginInterface W B O)
    (hAccess : OriginDeterminesAccess m I)
    (hDeletion : WorldwiseDeletion m Concrete) :
    OriginCompatibleDeletion m Concrete I := by
  intro v x hx hxv
  obtain ⟨u, hvu, hAbsent⟩ := hDeletion v x hx hxv
  exact ⟨u, hAbsent, (hAccess v u).1 hvu⟩

/-- Origin-determined access and a world with no individuals give deletion at
every world: the empty world shares no individual with any world, so by the
"if" half it is accessible from every world. -/
theorem emptyWorldDeletion (m : Ontic W B) (Concrete : B → Prop) (I : OriginInterface W B O)
    (hAccess : OriginDeterminesAccess m I) (hEmpty : EmptyWorld m) :
    WorldwiseDeletion m Concrete := by
  obtain ⟨e, he⟩ := hEmpty
  exact originDeletion m Concrete I hAccess fun _ x _ _ =>
    ⟨e, he x, fun y _ hy => (he y hy).elim⟩

/-- Deletion in the three finite models, by case analysis. -/
theorem deletionControls : Control.Certificate := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x _ _
    cases x
    · exact ⟨TruthCore.Causality.OriginToleranceIdentity.Control.World.bMinus, by
        simp [TruthCore.Causality.OriginToleranceIdentity.Control.faithful, TruthCore.Causality.OriginToleranceIdentity.Control.far],
        by simp [TruthCore.Causality.OriginToleranceIdentity.Control.faithful, TruthCore.Causality.OriginToleranceIdentity.Control.exists']⟩
    · exact ⟨TruthCore.Causality.OriginToleranceIdentity.Control.World.aMinus, by
        simp [TruthCore.Causality.OriginToleranceIdentity.Control.faithful, TruthCore.Causality.OriginToleranceIdentity.Control.far],
        by simp [TruthCore.Causality.OriginToleranceIdentity.Control.faithful, TruthCore.Causality.OriginToleranceIdentity.Control.exists']⟩
  · intro hDel
    obtain ⟨u, hu, hAbsent⟩ := hDel true trivial trivial
    cases u <;> simp [TruthCore.Causality.OriginToleranceIdentity.Control.faithful, TruthCore.Causality.OriginToleranceIdentity.Control.far,
      TruthCore.Causality.OriginToleranceIdentity.Control.exists'] at hu hAbsent
  · intro hAcc
    obtain ⟨u, hu, hAbsent⟩ := hAcc TruthCore.Causality.OriginToleranceIdentity.Control.World.plus
      (by simp [TruthCore.Causality.OriginToleranceIdentity.Control.faithful, TruthCore.Causality.OriginToleranceIdentity.Control.far])
      true trivial trivial
    cases u <;> simp [TruthCore.Causality.OriginToleranceIdentity.Control.faithful, TruthCore.Causality.OriginToleranceIdentity.Control.far,
      TruthCore.Causality.OriginToleranceIdentity.Control.exists'] at hu hAbsent
  · intro hDel
    obtain ⟨_, _, hAbsent⟩ := hDel () trivial trivial
    exact hAbsent trivial
  · intro o; cases o <;> simp [Control.interface, tolerance]
  · intro o o'; cases o <;> cases o' <;> simp [Control.interface, tolerance]
  · intro u v
    cases u <;> cases v <;>
      simp [Control.withEmpty, Control.far, Control.exists', Control.interface,
        Control.originOf, tolerance, Bool.forall_bool]
  · intro u x _ hx o ho
    let wit : Bool → Origin → Control.World
      | false, Origin.minus => Control.World.aMinus
      | false, Origin.actual => Control.World.actual
      | false, Origin.plus => Control.World.plus
      | true, Origin.minus => Control.World.bMinus
      | true, Origin.actual => Control.World.actual
      | true, Origin.plus => Control.World.bPlus
    refine ⟨wit x o, ?_⟩
    cases u <;> cases x <;> cases o <;>
      simp_all [wit, Control.withEmpty, Control.far, Control.exists', Control.interface,
        Control.originOf, tolerance]
  · exact ⟨false, trivial, trivial, Control.World.aMinus, Control.World.plus,
      by simp [Control.withEmpty, Control.far], by simp [Control.withEmpty, Control.far],
      rfl, trivial, by simp [Control.interface, Control.originOf, tolerance]⟩
  · intro v x _ _
    exact ⟨Control.World.empty, fun h => h, fun y _ hy => hy.elim⟩
  · intro v x _ _
    exact ⟨Control.World.empty, by cases v <;> simp [Control.withEmpty, Control.far],
      fun h => h⟩

end TruthCore.Results.Causality.OriginDeletion
