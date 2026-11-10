import TruthCore.Causality.OriginDeletion
import TruthCore.Results.Causality.InertEmptiness.Solution
import TruthCore.Results.Causality.OriginToleranceIdentity.Solution

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
  sorry

/-- If access is exactly shared-origin closeness, origin-compatible deletion
gives deletion at every world. Only the "if" half of origin-determined access
is used: a world lacking `x` whose shared individuals keep near origins is
accessible, whatever `x`'s own origin. -/
theorem originDeletion (m : Ontic W B) (Concrete : B → Prop) (I : OriginInterface W B O)
    (hAccess : OriginDeterminesAccess m I)
    (hCompatible : OriginCompatibleDeletion m Concrete I) :
    WorldwiseDeletion m Concrete := by
  sorry

/-- Conversely, under origin-determined access deletion at every world gives
origin-compatible deletion. Only the "only if" half is used. -/
theorem deletionOriginCompatible (m : Ontic W B) (Concrete : B → Prop)
    (I : OriginInterface W B O)
    (hAccess : OriginDeterminesAccess m I)
    (hDeletion : WorldwiseDeletion m Concrete) :
    OriginCompatibleDeletion m Concrete I := by
  sorry

/-- Origin-determined access and a world with no individuals give deletion at
every world: the empty world shares no individual with any world, so by the
"if" half it is accessible from every world. -/
theorem emptyWorldDeletion (m : Ontic W B) (Concrete : B → Prop) (I : OriginInterface W B O)
    (hAccess : OriginDeterminesAccess m I) (hEmpty : EmptyWorld m) :
    WorldwiseDeletion m Concrete := by
  sorry

/-- Origin-determined access, a world with no individuals and Arrival A's
presence-to-existence, inert emptiness and possible contingent-free past at `w`
are jointly inconsistent; stated as: the other four exclude an empty world.
Composes `emptyWorldDeletion` and `accessibleDeletionExcluded`. -/
theorem emptyWorldArrivalInconsistent {W B T O : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (I : OriginInterface W B O) (w : W)
    (hAccess : OriginDeterminesAccess h.ontic I)
    (hPresence : HistoryPresenceActual h)
    (hInert : EmptinessStaysEmpty h Concrete)
    (hPossible : PossiblyContingentsAbsentThenPresent h Concrete w) :
    NoEmptyWorld h.ontic := by
  sorry

/-- Deletion in the three finite models, by case analysis. -/
theorem deletionControls : Control.Certificate := by
  sorry

end TruthCore.Results.Causality.OriginDeletion
