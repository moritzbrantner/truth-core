module

/-!
Question-relative actual physical coverage, COMPLETE_PHYSICAL_INFORMATION_2.
Analyst interpretation of the existing definition, attribution deferred.

`Fact` indexes independently specified physical questions about the selected
subject; `holds f w` gives their truth across the FULL candidate domain `W`.
`relevant f` selects questions relevant to the fixed subject/question, including
questions false at actuality. Neither family nor relevance is extracted from
`physical`. Their physical interpretation and exhaustive relevance calibration
are OPEN application premises. Empty families can satisfy the body vacuously;
that does not certify calibration. No epistemic or metaphysical frame restriction
shrinks the domain on which coverage must hold.
-/

@[expose] public section
namespace TruthCore.Logic.ActualPhysicalCompleteness

/-- Every independently specified relevant physical fact has a predicate of the
represented physical value with exactly the same truth at every candidate.
This is coverage, not knowledge, a free adequacy flag, or global full-state
identity. It can fail when a relevant fact separates equal projection values.
Actual physical facthood and exhaustive question relevance remain OPEN; supplying
an arbitrary fact family does not establish those application premises. -/
def Complete {W P Fact : Type} (physical : W → P)
    (holds : Fact → W → Prop) (relevant : Fact → Prop) : Prop :=
  ∀ f, relevant f → ∃ represented : P → Prop,
    ∀ w, holds f w ↔ represented (physical w)

end TruthCore.Logic.ActualPhysicalCompleteness
