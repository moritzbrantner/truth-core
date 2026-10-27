import TruthCore.Models.FiniteSupport
import TruthCore.Alternatives.Inertia

/-! Named finite interpretations and closed certificates for the inertia bridge
(#497). Registration tests formal consequence only; it does not establish
physical or metaphysical possibility. Each removal model of
`INERTIAL-OBJECTION-YIELDS-RIVAL` corresponds to a recorded reply:

* `StateReading`: the state reading. Body `false` perseveres in uniform motion
  `false` by itself alone and is not moved in it; body `true` changes state in
  respect `true` and is moved there by `false`, which impresses a force on it.
  Newton's Def. III-IV and Lex I, the persevering body, the mover bridge, no
  self-motion, a mover for whatever is moved and something moved all hold; the
  becoming reading fails.
* `OtherSustainer`: the medium or impetus reply (Aquinas, *In Phys.* VIII,
  lect. 22; Garrigou-Lagrange 1914, p. 253). Body `false` perseveres and is moved
  by `true`, which it also perseveres by; Newton's "by inertia alone" fails.
* `DivineMover`: Garrigou-Lagrange's reply (1914, pp. 760-761). Body `false`
  perseveres by itself alone and is moved by `true`, which it does not persevere
  by; the mover bridge fails.
* `SelfMover`: the inherent force read as a self-mover. The one body moves
  itself; no self-motion fails.
* `NoPersevering`: nothing perseveres in uniform motion and nothing is moved;
  only the persevering body fails.
* `RivalSurvives`: the one body perseveres, is moved and has no mover. The whole
  bundle and no self-motion hold, so the inertial rival holds and the mover
  premise fails. -/
namespace TruthCore.Models.Inertia
open TruthCore.Models.FiniteSupport

structure Model (Being Respect : Type) where
  MovedIn : Being → Respect → Prop
  MovesIn : Being → Being → Respect → Prop
  UniformLocalMotion : Respect → Prop
  Perseveres : Being → Respect → Prop
  PerseveresBy : Being → Being → Respect → Prop
  ChangesState : Being → Prop
  ImpressesForceOn : Being → Being → Prop

namespace StateReading
def model : Model Bool Bool where
  MovedIn := fun x r => x = true ∧ r = true
  MovesIn := fun y x r => y = false ∧ x = true ∧ r = true
  UniformLocalMotion := fun r => r = false
  Perseveres := fun x r => x = false ∧ r = false
  PerseveresBy := fun y x _ => y = x
  ChangesState := fun x => x = true
  ImpressesForceOn := fun y x => y = false ∧ x = true

theorem evaluation0 : @TruthCore.Alternatives.Inertia.PerseveranceByInherentForceAloneReading Bool Bool model.UniformLocalMotion model.Perseveres model.PerseveresBy :=
  fun _ _ _ _ _ h => h

theorem evaluation1 : @TruthCore.Alternatives.Inertia.SomeBodyPerseveresInUniformMotionReading Bool Bool model.UniformLocalMotion model.Perseveres :=
  ⟨false, false, rfl, rfl, rfl⟩

theorem evaluation2 : @TruthCore.Alternatives.Inertia.MoverOfPerseveringBodyAccountsForPerseveranceReading Bool Bool model.MovesIn model.UniformLocalMotion model.Perseveres model.PerseveresBy :=
  fun _ _ _ hUniform _ hMoves => Bool.noConfusion (hUniform.symm.trans hMoves.2.2)

theorem evaluation3 : ¬ (@TruthCore.Alternatives.Inertia.UniformPerseveranceIsBeingMovedReading Bool Bool model.MovedIn model.UniformLocalMotion model.Perseveres) :=
  fun h => Bool.noConfusion (h false false rfl ⟨rfl, rfl⟩).1

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.NothingMovesItselfInSameRespectReading Bool Bool model.MovedIn model.MovesIn :=
  fun _ _ hMoved hSelf => Bool.noConfusion (hSelf.1.symm.trans hMoved.1)

theorem evaluation5 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading Bool Bool model.MovedIn model.MovesIn :=
  fun _ _ hMoved => ⟨false, rfl, hMoved.1, hMoved.2⟩

theorem evaluation6 : ¬ (@TruthCore.Alternatives.ActPotencyRegress.UniformMotionWithoutMoverReading Bool Bool model.MovedIn model.MovesIn model.UniformLocalMotion) :=
  fun ⟨_, _, hUniform, hMoved, _⟩ => Bool.noConfusion (hUniform.symm.trans hMoved.2)

theorem evaluation7 : @TruthCore.Alternatives.Inertia.UniformPerseveranceIsNotBeingMovedReading Bool Bool model.MovedIn model.UniformLocalMotion model.Perseveres :=
  fun _ _ _ hPerseveres hMoved => Bool.noConfusion (hPerseveres.1.symm.trans hMoved.1)

theorem evaluation8 : @TruthCore.Alternatives.ActPotencyRegress.ChangeOfStateOnlyByImpressedForceReading Bool model.ChangesState model.ImpressesForceOn :=
  fun _ hChanges => ⟨false, rfl, hChanges⟩

theorem evaluation9 : @TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading Bool Bool model.MovedIn :=
  ⟨true, true, rfl, rfl⟩
end StateReading

namespace OtherSustainer
def model : Model Bool Unit where
  MovedIn := fun x _ => x = false
  MovesIn := fun y x _ => y = true ∧ x = false
  UniformLocalMotion := fun _ => True
  Perseveres := fun x _ => x = false
  PerseveresBy := fun y x _ => y = true ∧ x = false
  ChangesState := fun _ => False
  ImpressesForceOn := fun _ _ => False

theorem evaluation0 : ¬ (@TruthCore.Alternatives.Inertia.PerseveranceByInherentForceAloneReading Bool Unit model.UniformLocalMotion model.Perseveres model.PerseveresBy) :=
  fun h => Bool.noConfusion (h false () true trivial rfl ⟨rfl, rfl⟩)

theorem evaluation1 : @TruthCore.Alternatives.Inertia.SomeBodyPerseveresInUniformMotionReading Bool Unit model.UniformLocalMotion model.Perseveres :=
  ⟨false, (), trivial, rfl⟩

theorem evaluation2 : @TruthCore.Alternatives.Inertia.MoverOfPerseveringBodyAccountsForPerseveranceReading Bool Unit model.MovesIn model.UniformLocalMotion model.Perseveres model.PerseveresBy :=
  fun _ _ _ _ _ hMoves => hMoves

theorem evaluation3 : @TruthCore.Alternatives.Inertia.UniformPerseveranceIsBeingMovedReading Bool Unit model.MovedIn model.UniformLocalMotion model.Perseveres :=
  fun _ _ _ hPerseveres => hPerseveres

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.NothingMovesItselfInSameRespectReading Bool Unit model.MovedIn model.MovesIn :=
  fun _ _ _ hSelf => Bool.noConfusion (hSelf.1.symm.trans hSelf.2)

theorem evaluation5 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading Bool Unit model.MovedIn model.MovesIn :=
  fun _ _ hMoved => ⟨true, rfl, hMoved⟩

theorem evaluation6 : ¬ (@TruthCore.Alternatives.ActPotencyRegress.UniformMotionWithoutMoverReading Bool Unit model.MovedIn model.MovesIn model.UniformLocalMotion) :=
  fun ⟨_, _, _, hMoved, hNoMover⟩ => hNoMover true ⟨rfl, hMoved⟩
end OtherSustainer

namespace DivineMover
def model : Model Bool Unit where
  MovedIn := fun x _ => x = false
  MovesIn := fun y x _ => y = true ∧ x = false
  UniformLocalMotion := fun _ => True
  Perseveres := fun x _ => x = false
  PerseveresBy := fun y x _ => y = x
  ChangesState := fun _ => False
  ImpressesForceOn := fun _ _ => False

theorem evaluation0 : @TruthCore.Alternatives.Inertia.PerseveranceByInherentForceAloneReading Bool Unit model.UniformLocalMotion model.Perseveres model.PerseveresBy :=
  fun _ _ _ _ _ h => h

theorem evaluation1 : @TruthCore.Alternatives.Inertia.SomeBodyPerseveresInUniformMotionReading Bool Unit model.UniformLocalMotion model.Perseveres :=
  ⟨false, (), trivial, rfl⟩

theorem evaluation2 : ¬ (@TruthCore.Alternatives.Inertia.MoverOfPerseveringBodyAccountsForPerseveranceReading Bool Unit model.MovesIn model.UniformLocalMotion model.Perseveres model.PerseveresBy) :=
  fun h => Bool.noConfusion (h true false () trivial rfl ⟨rfl, rfl⟩)

theorem evaluation3 : @TruthCore.Alternatives.Inertia.UniformPerseveranceIsBeingMovedReading Bool Unit model.MovedIn model.UniformLocalMotion model.Perseveres :=
  fun _ _ _ hPerseveres => hPerseveres

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.NothingMovesItselfInSameRespectReading Bool Unit model.MovedIn model.MovesIn :=
  fun _ _ _ hSelf => Bool.noConfusion (hSelf.1.symm.trans hSelf.2)

theorem evaluation5 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading Bool Unit model.MovedIn model.MovesIn :=
  fun _ _ hMoved => ⟨true, rfl, hMoved⟩

theorem evaluation6 : ¬ (@TruthCore.Alternatives.ActPotencyRegress.UniformMotionWithoutMoverReading Bool Unit model.MovedIn model.MovesIn model.UniformLocalMotion) :=
  fun ⟨_, _, _, hMoved, hNoMover⟩ => hNoMover true ⟨rfl, hMoved⟩
end DivineMover

namespace SelfMover
def model : Model Unit Unit where
  MovedIn := fun _ _ => True
  MovesIn := fun _ _ _ => True
  UniformLocalMotion := fun _ => True
  Perseveres := fun _ _ => True
  PerseveresBy := fun _ _ _ => True
  ChangesState := fun _ => False
  ImpressesForceOn := fun _ _ => False

theorem evaluation0 : @TruthCore.Alternatives.Inertia.PerseveranceByInherentForceAloneReading Unit Unit model.UniformLocalMotion model.Perseveres model.PerseveresBy :=
  fun x _ y _ _ _ => (enumerateUnit y).trans (enumerateUnit x).symm

theorem evaluation1 : @TruthCore.Alternatives.Inertia.SomeBodyPerseveresInUniformMotionReading Unit Unit model.UniformLocalMotion model.Perseveres :=
  ⟨(), (), trivial, trivial⟩

theorem evaluation2 : @TruthCore.Alternatives.Inertia.MoverOfPerseveringBodyAccountsForPerseveranceReading Unit Unit model.MovesIn model.UniformLocalMotion model.Perseveres model.PerseveresBy :=
  fun _ _ _ _ _ _ => trivial

theorem evaluation3 : @TruthCore.Alternatives.Inertia.UniformPerseveranceIsBeingMovedReading Unit Unit model.MovedIn model.UniformLocalMotion model.Perseveres :=
  fun _ _ _ _ => trivial

theorem evaluation4 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.NothingMovesItselfInSameRespectReading Unit Unit model.MovedIn model.MovesIn) :=
  fun h => h () () trivial trivial

theorem evaluation5 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading Unit Unit model.MovedIn model.MovesIn :=
  fun x _ _ => ⟨x, trivial⟩

theorem evaluation6 : ¬ (@TruthCore.Alternatives.ActPotencyRegress.UniformMotionWithoutMoverReading Unit Unit model.MovedIn model.MovesIn model.UniformLocalMotion) :=
  fun ⟨x, _, _, _, hNoMover⟩ => hNoMover x trivial
end SelfMover

namespace NoPersevering
def model : Model Unit Unit where
  MovedIn := fun _ _ => False
  MovesIn := fun _ _ _ => False
  UniformLocalMotion := fun _ => True
  Perseveres := fun _ _ => False
  PerseveresBy := fun _ _ _ => False
  ChangesState := fun _ => False
  ImpressesForceOn := fun _ _ => False

theorem evaluation0 : @TruthCore.Alternatives.Inertia.PerseveranceByInherentForceAloneReading Unit Unit model.UniformLocalMotion model.Perseveres model.PerseveresBy :=
  fun _ _ _ _ hPerseveres _ => hPerseveres.elim

theorem evaluation1 : ¬ (@TruthCore.Alternatives.Inertia.SomeBodyPerseveresInUniformMotionReading Unit Unit model.UniformLocalMotion model.Perseveres) :=
  fun ⟨_, _, _, hPerseveres⟩ => hPerseveres

theorem evaluation2 : @TruthCore.Alternatives.Inertia.MoverOfPerseveringBodyAccountsForPerseveranceReading Unit Unit model.MovesIn model.UniformLocalMotion model.Perseveres model.PerseveresBy :=
  fun _ _ _ _ hPerseveres _ => hPerseveres.elim

theorem evaluation3 : @TruthCore.Alternatives.Inertia.UniformPerseveranceIsBeingMovedReading Unit Unit model.MovedIn model.UniformLocalMotion model.Perseveres :=
  fun _ _ _ hPerseveres => hPerseveres.elim

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.NothingMovesItselfInSameRespectReading Unit Unit model.MovedIn model.MovesIn :=
  fun _ _ hMoved _ => hMoved

theorem evaluation5 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading Unit Unit model.MovedIn model.MovesIn :=
  fun _ _ hMoved => hMoved.elim

theorem evaluation6 : ¬ (@TruthCore.Alternatives.ActPotencyRegress.UniformMotionWithoutMoverReading Unit Unit model.MovedIn model.MovesIn model.UniformLocalMotion) :=
  fun ⟨_, _, _, hMoved, _⟩ => hMoved
end NoPersevering

namespace RivalSurvives
def model : Model Unit Unit where
  MovedIn := fun _ _ => True
  MovesIn := fun _ _ _ => False
  UniformLocalMotion := fun _ => True
  Perseveres := fun _ _ => True
  PerseveresBy := fun _ _ _ => True
  ChangesState := fun _ => False
  ImpressesForceOn := fun _ _ => False

theorem evaluation0 : @TruthCore.Alternatives.Inertia.PerseveranceByInherentForceAloneReading Unit Unit model.UniformLocalMotion model.Perseveres model.PerseveresBy :=
  fun x _ y _ _ _ => (enumerateUnit y).trans (enumerateUnit x).symm

theorem evaluation1 : @TruthCore.Alternatives.Inertia.SomeBodyPerseveresInUniformMotionReading Unit Unit model.UniformLocalMotion model.Perseveres :=
  ⟨(), (), trivial, trivial⟩

theorem evaluation2 : @TruthCore.Alternatives.Inertia.MoverOfPerseveringBodyAccountsForPerseveranceReading Unit Unit model.MovesIn model.UniformLocalMotion model.Perseveres model.PerseveresBy :=
  fun _ _ _ _ _ hMoves => hMoves.elim

theorem evaluation3 : @TruthCore.Alternatives.Inertia.UniformPerseveranceIsBeingMovedReading Unit Unit model.MovedIn model.UniformLocalMotion model.Perseveres :=
  fun _ _ _ _ => trivial

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.NothingMovesItselfInSameRespectReading Unit Unit model.MovedIn model.MovesIn :=
  fun _ _ _ hSelf => hSelf

theorem evaluation5 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading Unit Unit model.MovedIn model.MovesIn) :=
  fun h => (h () () trivial).elim fun _ hMoves => hMoves

theorem evaluation6 : @TruthCore.Alternatives.ActPotencyRegress.UniformMotionWithoutMoverReading Unit Unit model.MovedIn model.MovesIn model.UniformLocalMotion :=
  ⟨(), (), trivial, trivial, fun _ hMoves => hMoves⟩
end RivalSurvives

end TruthCore.Models.Inertia
