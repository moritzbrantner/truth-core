module
public import TruthCore.Causality.MotionMoverFork
@[expose] public section
namespace TruthCore.Results.Causality.MotionMoverFork
open TruthCore.Causality.MotionMoverFork
open TruthCore.Greek.Aristotle.Physics.Typed
open TruthCore.Latin.Aquinas.SummaTheologiae

theorem anotherGivesSomething {B R : Type} (moves : B → B → R → Prop) :
    AnotherGivesSomething moves := by
  intro x r h
  cases h with
  | intro y _ hm => exact .intro y hm

theorem physicalGivesBroad {B R : Type} (physical : R → Prop) (moved : B → R → Prop) :
    PhysicalGivesBroad physical moved := by
  intro x r h
  cases h with
  | intro _ hm => exact .intro hm

theorem anotherAnyGivesSomethingAny {B R : Type} (moves : B → B → R → Prop) :
    AnotherAnyGivesSomethingAny moves := by
  intro x h
  cases h with
  | intro h =>
    obtain ⟨y, r, _, hm⟩ := h
    exact ⟨r, .intro y hm⟩

theorem moverFork {B R : Type} (moves accidental : B → B → R → Prop)
    (h : AccidentalHasPerSeMover moves accidental) : MoverForkSound moves accidental := by
  intro s x r hm
  cases s with
  | something => exact ⟨r, hm⟩
  | another => exact anotherAnyGivesSomethingAny moves x hm
  | accidental => exact ⟨r, h x r hm⟩

theorem broadFromPhysicalAndResidual {B R : Type} (physical residual : R → Prop)
    (moved : B → R → Prop) (moves : B → B → R → Prop)
    (hp : EveryPhysicalMotionHasAPerSeMoverReading physical moved moves)
    (hr : ResidualHasMover residual moved moves)
    (hc : MotionCoverage physical residual moved) : ReducedOnlyByAMoverReading moved moves := by
  intro x r hm
  cases hc x r hm with
  | inl h => exact hp x r h hm
  | inr h => exact hr x r h hm

theorem motionFork {B R : Type} (physical residual : R → Prop)
    (moved : B → R → Prop) (moves : B → B → R → Prop)
    (hp : EveryPhysicalMotionHasAPerSeMoverReading physical moved moves)
    (hr : ResidualHasMover residual moved moves)
    (hc : MotionCoverage physical residual moved) : MotionForkSound physical moved moves := by
  intro s x r hm
  cases s with
  | broad =>
    cases hm with
    | intro hm => exact broadFromPhysicalAndResidual physical residual moved moves hp hr hc x r hm
  | physical =>
    cases hm with
    | intro h hm => exact hp x r h hm

theorem controls : Controls := by
  constructor
  · refine ⟨(· = false), (· = true), (fun _ _ => True), (fun _ _ _ => True), ?_⟩
    refine ⟨?_, ?_, ?_, ?_, True.intro, True.intro, rfl, rfl⟩
    · intro x r _; cases r with
      | false => exact Or.inl rfl
      | true => exact Or.inr rfl
    · intro r h; cases r with
      | false => exact Bool.noConfusion h.2
      | true => exact Bool.noConfusion h.1
    · intro x r _ _; exact ⟨(), True.intro⟩
    · intro x r _ _; exact ⟨(), True.intro⟩
  constructor
  · refine ⟨(fun _ => True), (fun _ => False), (fun _ _ => True), (fun _ _ _ => False), ?_, ?_, ?_⟩
    · intro x r _; exact Or.inl True.intro
    · intro x r h; exact False.elim h
    · intro h; obtain ⟨_, hm⟩ := h () () True.intro; exact hm
  constructor
  · refine ⟨(fun _ => False), (fun _ => False), (fun _ _ => True), (fun _ _ _ => False), ?_, ?_, ?_⟩
    · intro x r h; exact False.elim h
    · intro x r h; exact False.elim h
    · intro h; obtain ⟨_, hm⟩ := h () () True.intro; exact hm
  constructor
  · refine ⟨(fun _ => False), (fun _ => True), (fun _ _ => True), (fun _ _ _ => False), ?_, ?_, ?_⟩
    · intro x r _; exact Or.inr True.intro
    · intro x r h; exact False.elim h
    · intro h; obtain ⟨_, hm⟩ := h () () True.intro; exact hm
  constructor
  · refine ⟨.intro () True.intro, ?_⟩
    intro h; cases h with
    | intro y hn _ => exact hn (Subsingleton.elim _ _)
  constructor
  · refine ⟨.intro () True.intro, ?_⟩
    intro h; cases h with
    | intro y hm => exact hm
  constructor
  · exact ⟨⟨.another, rfl⟩, fun s t hs ht => hs.trans ht.symm⟩
  constructor
  · exact ⟨⟨.broad, rfl⟩, fun s t hs ht => hs.trans ht.symm⟩
  constructor
  · refine ⟨.intro True.intro, ?_⟩
    intro h; cases h with
    | intro hp _ => exact hp
  · intro x r _; exact .intro () True.intro
end TruthCore.Results.Causality.MotionMoverFork
