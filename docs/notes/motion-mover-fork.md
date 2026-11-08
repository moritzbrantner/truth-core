# Motion/mover fork: bounded investigation

Target: `STMT-NOTHING-REDUCED-TO-ACT-EXCEPT-BY-A-MOVER`, on the first-mover route.
Analyst formulations; attribution deferred. This records development experiments,
not a certified batch or a premise discharge.

## Reuse and result boundaries

The existing Physics VIII.4 literal/per-se separation and its omission model
already reject deriving a per-se mover from the literal per-accidens disjunction.
See `ATTEMPT-PHYSICS-VIII4-LITERAL-PER-SE` and `docs/typed-physics.md`.
`STMT-EVERY-PHYSICAL-MOTION-HAS-A-PER-SE-MOVER` is guarded by physical respects;
`STMT-EVERY-MOVED-THING-HAS-SOME-MOVER` drops the same-respect requirement.
Neither is silently identified with the broad prima-via premise.

Four small proof experiments below were accepted without diagnostics by the
coordinator's Lean preview at clean `fb544e6f425e89b1193cf4c9baa3b0825640d7b6`.
They have not passed binding, Comparator, NanoDa or final build gates, and are
not registered results. No source attribution or real-world applicability follows.

1. A distinct mover in some respect supplies a mover in some respect.
2. The converse fails on a singleton self-link. This does **not** refute the
   distinct-part analysis of an animal's self-motion: that requires representing
   the parts, absent from this singleton model.
3. Physical coverage plus explicit residual coverage and a physical/nonphysical
   case split yields the broad mover premise. The residual premise remains OPEN;
   this is a scope decomposition, not independent support for movers.
4. Physical-only coverage can hold while broad reduction has no mover: the
   countermodel has one moved subject, a nonphysical respect, and no mover links.
   It is nonvacuous for broad reduction and vacuous for physical motion, exactly
   the scope gap being tested.

An inertial state must not be identified with passage from potency to act merely
because the word motion occurs. A model of uniform motion without a sustaining
mover only challenges a premise whose selected meaning includes that state.
No inertial-state/change bridge is proved here. Per-accidens moving remains a
separate primitive and supplies no per-se link without an explicit premise.

## Remaining encoding and connection

The two owned disambiguations still need meaning-bearing distinct sense types,
typed choice with Other, open coverage and exclusivity statements, branch results
and the joint theorem. The experiment below is intentionally insufficient for
that migration: it does not replace the existing primitive `MovedIn` declarations
with completed definitions or settle the causal interpretation. The next batch
should reuse the physical branch, add an explicit nonphysical branch rather than
assert that all reduction is physical, and keep any bridge back to the existing
root signature open. Test omission of the residual branch and physical branch
with actual moved witnesses. The singleton witness only tests distinctness.

## Reproducible development artifact

This exact full content was submitted twice through `scripts/agent_lean.py` at
`Scratch/motion/MotionMoverFork.lean`, session `parallel-round`. The first version
omitted `physicalOnlyInsufficient`; the second is below. Second content SHA-256:
`d1d55b2b19e3683c712646c4636cf8cd466f19c30fe408cb5f458760a31cb600`.
The shared preview remained clean at the revision above. It is development evidence
only; extract the block to a temporary Lean file to repeat diagnostics.

```lean
import TruthCore.Greek.Aristotle.Physics.Typed.Motion
open TruthCore.Greek.Aristotle.Physics.Typed
open TruthCore.Latin.Aquinas.SummaTheologiae
namespace MotionMoverForkExperiment
-- A distinct mover in some respect supplies a mover in some respect.
theorem anotherGivesSomething {B R : Type} (moves : B → B → R → Prop)
    (x : B) (h : MovedByAnother moves x) : ∃ y r, moves y x r := by
  obtain ⟨y, r, _, hm⟩ := h
  exact ⟨y, r, hm⟩
-- A singleton self-link refutes the converse. It does not claim that real
-- animals have no distinct moving parts.
theorem selfLinkNotAnother :
    (∃ y r : Unit, (fun (_ _ _ : Unit) => True) y () r) ∧
    ¬ MovedByAnother (fun (_ _ _ : Unit) => True) () := by
  constructor
  · exact ⟨(), (), True.intro⟩
  · rintro ⟨y, r, hne, _⟩
    exact hne (Subsingleton.elim _ _)
-- Physical coverage alone need not extend to broad reduction; the missing
-- branch must be supplied explicitly rather than identifying the two senses.
theorem physicalAndResidual {B R : Type} (physical : R → Prop)
    (moved : B → R → Prop) (moves : B → B → R → Prop)
    (hp : EveryPhysicalMotionHasAPerSeMoverReading physical moved moves)
    (hr : ∀ x r, moved x r → ¬ physical r → ∃ y, moves y x r)
    (hc : ∀ x r, moved x r → physical r ∨ ¬ physical r) :
    ReducedOnlyByAMoverReading moved moves := by
  intro x r hm
  cases hc x r hm with
  | inl h => exact hp x r h hm
  | inr h => exact hr x r hm h
-- A nonphysical reduction with no mover satisfies the physical restriction.
theorem physicalOnlyInsufficient :
    EveryPhysicalMotionHasAPerSeMoverReading (fun (_ : Unit) => False)
      (fun _ _ : Unit => True) (fun _ _ _ : Unit => False) ∧
    ¬ ReducedOnlyByAMoverReading (fun _ _ : Unit => True)
      (fun _ _ _ : Unit => False) := by
  constructor
  · intro x r hp
    exact False.elim hp
  · intro h
    obtain ⟨y, hy⟩ := h () () True.intro
    exact hy
end MotionMoverForkExperiment
```

## Setup and service experiment

The supplied isolated checkout is a Git worktree without `.lake`. The documented
`prepare-worker.py` refuses worktrees, so no cold build, dependency copy or owner
checkout mutation was attempted. A standalone warm canonical clone is needed
before producing the requested certified batch; the coordinator retains setup
ownership. No heavy jobs remain running.

The UUID corpus query succeeded with revision/input binding. The legacy-ID query
returned `no corpus record with id STMT-EVERY-PHYSICAL-MOTION-HAS-A-PER-SE-MOVER`;
use the UUID `6882f4cf-2869-5fe2-ae79-b1dfd6f88026` with this endpoint. The CLI dossier
accepts the legacy alias. Two full edits used the same persistent preview session:
service elaboration was 1.527s then 0.206s, with no diagnostics. Retain the service
for proof development; revise alias handling. These are two incremental edits,
not a benchmark against CLI compilation or final verification.

Convention source revision: `625cb04ca568aebc8d45c90033e107a05e9bd2a0`.
