module

public import TruthCore.Causality.TermSenseForks
public import TruthCore.Logic.StrengthComparison

/-! ## Productive interpretation of an originating cause

`CausesOrigin` is an untimed, unconstrained field of `CauseFrame`. This OPEN
analyst bridge says only that each selected origin edge is realized by an
occurring exercise of the source which produces the target's existence. It
does not define `CausesOrigin`, assert that every cause is productive in this
sense, or establish that the relation has any real-world instances.

The bearer, exercise, and product are kept separate. An origin edge mediated
by a different bearer's exercise cannot be used as a self-origin edge. The
existential-priority laws remain four separate premises of the consuming
argument rather than properties silently inserted into this definition.

The no-self-origination argument uses only self-edges, so it consumes the weak
self-edge sibling `OriginHasProductiveSelfExercise` (#1610). The universal
bridge strengthens it; their certified difference is
`NonSelfOriginHasProductiveExercise`, the bridge's clause for edges that are
not self-edges (origination of one thing by another).
-/

@[expose] public section

namespace TruthCore.Causality.OriginExerciseBridge

open TruthCore.Causality.TermSenseForks

/-- Each `CAUSE_4` originating-cause edge is realized by some occurring
exercise borne by that very originator and producing that target's existence.
This is an OPEN interpretation bridge from `CausesOrigin` to the independent
existential-production vocabulary, not a source reading or a logical truth. -/
def OriginHasProductiveExercise {Being Respect Exercise : Type}
    (F : CauseFrame Being Respect) (Occurs : Exercise → Prop)
    (bearer : Exercise → Being) (produces : Exercise → Being → Prop) : Prop :=
  ∀ c x, F.CausesOrigin c x →
    ∃ a, Occurs a ∧ bearer a = c ∧ produces a x

/-- Weak self-edge sibling of `OriginHasProductiveExercise`: each `CAUSE_4`
self-origin edge `CausesOrigin x x` is realized by some occurring exercise
borne by `x` and producing `x`'s existence. OPEN analyst bridge; it says
nothing about origin edges between distinct beings. -/
def OriginHasProductiveSelfExercise {Being Respect Exercise : Type}
    (F : CauseFrame Being Respect) (Occurs : Exercise → Prop)
    (bearer : Exercise → Being) (produces : Exercise → Being → Prop) : Prop :=
  ∀ x, F.CausesOrigin x x →
    ∃ a, Occurs a ∧ bearer a = x ∧ produces a x

/-- Difference of the universal bridge over its self-edge sibling: every
origin edge is either a self-edge or realized by an occurring exercise borne
by its source and producing its target's existence. Classically this is the
universal bridge restricted to edges `CausesOrigin c x` with `c ≠ x`; the
disjunctive form keeps the comparison free of decidable identity. -/
def NonSelfOriginHasProductiveExercise {Being Respect Exercise : Type}
    (F : CauseFrame Being Respect) (Occurs : Exercise → Prop)
    (bearer : Exercise → Being) (produces : Exercise → Being → Prop) : Prop :=
  ∀ c x, F.CausesOrigin c x →
    c = x ∨ ∃ a, Occurs a ∧ bearer a = c ∧ produces a x

open TruthCore.Logic.StrengthComparison in
/-- Universal bridge over its self-edge sibling; difference: the clause for
origin edges that are not self-edges. -/
def universalOverSelf {Being Respect Exercise : Type}
    (F : CauseFrame Being Respect) (Occurs : Exercise → Prop)
    (bearer : Exercise → Being) (produces : Exercise → Being → Prop) :
    ComparisonSpec where
  stronger := OriginHasProductiveExercise F Occurs bearer produces
  weaker := OriginHasProductiveSelfExercise F Occurs bearer produces
  delta := NonSelfOriginHasProductiveExercise F Occurs bearer produces

/-- Exact factorization: the universal bridge holds iff its self-edge sibling
holds and every origin edge that is not a self-edge is productively exercised
by its source. -/
def UniversalOverSelfExact : Prop :=
  ∀ {Being Respect Exercise : Type} (F : CauseFrame Being Respect)
    (Occurs : Exercise → Prop) (bearer : Exercise → Being)
    (produces : Exercise → Being → Prop),
    OriginHasProductiveExercise F Occurs bearer produces ↔
      OriginHasProductiveSelfExercise F Occurs bearer produces ∧
        NonSelfOriginHasProductiveExercise F Occurs bearer produces

/-- Separating frame: of two beings, `true` originates `false` and nothing
originates itself. A formal interpretation only. -/
def otherOnlyFrame : CauseFrame Bool Unit where
  MovedIn _ _ := False
  MovesIn _ _ _ := False
  EfficientlyCausesIn _ _ _ := False
  CausesIn _ _ _ := False
  CausesOrigin c x := c = true ∧ x = false

open TruthCore.Logic.StrengthComparison in
/-- The separating application of `universalOverSelf`: the other-only frame
with no exercises at all. The self-edge sibling holds vacuously and the
universal bridge fails at the edge `true → false`. This is not a claim that
real origination lacks productive exercises. -/
def otherOnlySetting : ComparisonSpec :=
  universalOverSelf otherOnlyFrame (fun _ : Empty => True) (fun e => nomatch e)
    (fun e _ => nomatch e)

open TruthCore.Logic.StrengthComparison in
/-- The other-only setting satisfies the self-edge sibling but not the
universal bridge. -/
def OtherOnlySeparates : Prop := Separation otherOnlySetting

end TruthCore.Causality.OriginExerciseBridge
