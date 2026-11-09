module
public import TruthCore.Causality.PerAccidensResponses
@[expose] public section
namespace TruthCore.Results.Causality.PerAccidensResponses
open TruthCore.Causality.PerAccidensResponses

theorem exerciseCapacity (s : State) (h : Exercise s) : Capacity s :=
  (s.execution.get h).property

theorem allExerciseCapacity {B T I C : Type} [Preorder T] (p : Profile B T I C)
    (h : AllExercise p) : AllCapacity p := by
  intro k y x edge
  exact ⟨(h k y x edge).1, fun i hi => exerciseCapacity _ ((h k y x edge).2 i hi)⟩

theorem someExerciseCapacity {B T I C : Type} [Preorder T] (p : Profile B T I C)
    (h : SomeExercise p) : SomeCapacity p := by
  intro k y x edge
  obtain ⟨base, i, hi, he⟩ := h k y x edge
  exact ⟨base, i, hi, exerciseCapacity _ he⟩

theorem allSomeCapacity {B T I C : Type} [Preorder T] (p : Profile B T I C)
    (h : AvailableAllCapacity p) : AvailableSomeCapacity p := by
  refine ⟨h.1, ?_⟩
  intro k y x edge
  obtain ⟨i, hi⟩ := h.1 k y x edge
  exact ⟨(h.2 k y x edge).1, i, hi, (h.2 k y x edge).2 i hi⟩

theorem allSomeExercise {B T I C : Type} [Preorder T] (p : Profile B T I C)
    (h : AvailableAllExercise p) : AvailableSomeExercise p := by
  refine ⟨h.1, ?_⟩
  intro k y x edge
  obtain ⟨i, hi⟩ := h.1 k y x edge
  exact ⟨(h.2 k y x edge).1, i, hi, (h.2 k y x edge).2 i hi⟩

private theorem admissibleSample (good bad : State) (n : Nat) (b : Bool) :
    Admissible (sample good bad) (some (n+1)) (some n) (some (n+1), b) := by
  simp [Admissible, sample]
  omega

private theorem someSample (good bad : State) (h : Exercise good) :
    SomeExercise (sample good bad) := by
  intro k y x edge
  obtain ⟨n, rfl, rfl⟩ := edge
  exact ⟨rfl, (some (n+1), true), admissibleSample good bad n true, by simpa [sample] using h⟩

theorem controls : Controls := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨someSample acting unable rfl, ?_⟩,
    ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro k y x edge
    obtain ⟨n, rfl, rfl⟩ := edge
    exact ⟨(some (n+1), true), admissibleSample acting acting n true⟩
  · intro k y x edge
    obtain ⟨n, rfl, rfl⟩ := edge
    refine ⟨rfl, fun i hi => ?_⟩
    have hr : i.1 = some (n+1) := hi.2.2.2.1
    change Exercise (if i.1 = none then unable else if i.2 then acting else acting)
    rw [ite_eq_right (by rw [hr]; exact Option.some_ne_none _)]
    cases i.2 <;> rfl
  · intro k y x edge
    obtain ⟨n, rfl, rfl⟩ := edge
    refine ⟨rfl, fun i hi => ?_⟩
    have hr : i.1 = some (n+1) := hi.2.2.2.1
    simp [sample, Capacity, ready, hr]
  · intro h
    obtain ⟨_, i, _, he⟩ := h .generation (some 1) (some 0) ⟨0, rfl, rfl⟩
    change Exercise (if i.1 = none then unable else if i.2 then ready else ready) at he
    split at he
    · simp [Exercise, unable] at he
    · simp only [ite_self] at he
      simp [Exercise, ready] at he
  · intro h
    have hc := (h .generation (some 1) (some 0) ⟨0, rfl, rfl⟩).2
      (some 1, false) (admissibleSample acting unable 0 false)
    simp [sample, Capacity, unable] at hc
  · intro k y x edge
    exact ⟨rfl, fun i => nomatch i⟩
  · intro h
    obtain ⟨_, i, _⟩ := h .generation (some 1) (some 0) ⟨0, rfl, rfl⟩
    exact nomatch i
  · intro h
    obtain ⟨i, _⟩ := h .generation (some 1) (some 0) ⟨0, rfl, rfl⟩
    exact nomatch i
  · intro k n
    exact ⟨n, rfl, rfl⟩
  · intro n
    exact ⟨some (n+1), n, rfl, rfl⟩
  · simp [sample, Admissible, Capacity, unable]
end TruthCore.Results.Causality.PerAccidensResponses
