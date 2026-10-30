import TruthCore.Logic.ExcludedMiddle
import TruthCore.Modern.Papineau.RiseOfPhysicalism
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question75.Subsistence

/-!
A certified comparison arena for one question of #419: what is the status of
occurrences of a target mental kind relative to physical occurrences?

The causal premises are readings of Papineau, "The Rise of Physicalism", p.9
(`PAPINEAU-RISE-PHYSICALISM-3-12`). The position labels (eliminative, reductive,
nonreductive, physically unbased) are comparison labels defined by the types
below, not readings of any eliminativist or nonreductivist author. The bridges
to q.75 a.2 are unattributed open premises. See
`docs/notes/mind-physicalism-fork-419.md`.

No declaration here says that a mental occurrence is or is not physical. Every
model of this vocabulary is a finite formal interpretation, not a claim about
metaphysical possibility or about how thinking is implemented.
-/

namespace TruthCore.Alternatives.MindPhysicalism

open TruthCore.Modern.Papineau.RiseOfPhysicalism
open TruthCore.Latin.Aquinas.SummaTheologiae.HumanIntellect

/-- Occurrences as instantiations of kinds, following Papineau's choice of facts
or property instantiations as causal relata (pp.9-10).

* `Has e k`: occurrence `e` instantiates kind `k`. An occurrence may have several
  kinds, so a mental occurrence may also have a physical kind.
* `PhysicalKind k`: `k` is specifiable without the mental vocabulary at issue
  (DEF-PAPINEAU-PHYSICAL).
* `mental`: the target kind. Whether it is itself a physical kind is left open.
* `Causes c x`: a primitive relation, read strictly or generously as the frame's
  interpretation decides (p.11); no transitivity, asymmetry or well-foundedness
  is assumed.
* `RealizedBy e r`: `e` is a second-order occurrence and `r` a first-order
  occurrence filling its role (pp.10-11); no structural law is assumed.

`IsEffect`, `Prior` and `FullyDeterminedByLaw` are the parameters of
`CompletenessOfPhysicsReading`. -/
structure Frame (Occurrence Kind : Type) where
  Has : Occurrence → Kind → Prop
  PhysicalKind : Kind → Prop
  mental : Kind
  IsEffect : Occurrence → Prop
  Prior : Occurrence → Occurrence → Prop
  FullyDeterminedByLaw : (Occurrence → Prop) → Occurrence → Prop
  Causes : Occurrence → Occurrence → Prop
  RealizedBy : Occurrence → Occurrence → Prop

variable {Occurrence Kind : Type}

/-- An occurrence of the target mental kind. -/
def Frame.Mental (f : Frame Occurrence Kind) (e : Occurrence) : Prop :=
  f.Has e f.mental

/-- An occurrence is physical when it has some physical kind. -/
def Frame.Physical (f : Frame Occurrence Kind) (e : Occurrence) : Prop :=
  ∃ k, f.PhysicalKind k ∧ f.Has e k

/-- Papineau's completeness premise, instantiated at the frame by reusing the
existing reading rather than restating it. -/
def Completeness (f : Frame Occurrence Kind) : Prop :=
  CompletenessOfPhysicsReading f.Physical f.IsEffect f.Prior f.FullyDeterminedByLaw

/-- A physical effect of `c`. -/
def Frame.PhysicalEffectOf (f : Frame Occurrence Kind) (c x : Occurrence) : Prop :=
  f.Physical x ∧ f.IsEffect x ∧ f.Causes c x

/-- `x`'s prior physical occurrences, the determiners in completeness. -/
def Frame.PriorPhysical (f : Frame Occurrence Kind) (x c : Occurrence) : Prop :=
  f.Physical c ∧ f.Prior c x

/-- `c` is one of the occurrences in `S` or is realized by one of them. -/
def Frame.AmongOrRealizedBy (f : Frame Occurrence Kind)
    (S : Occurrence → Prop) (c : Occurrence) : Prop :=
  S c ∨ ∃ r, S r ∧ f.RealizedBy c r

/-- `c` overdetermines `x`: it causes `x`, the prior physical occurrences fully
determine `x`, and `c` is neither among them nor realized by one of them. So `c`
is a cause distinct from the physical determiners, which is Papineau's contrast
at p.10 ("distinct mental and physical causes"). -/
def Frame.Overdetermines (f : Frame Occurrence Kind) (c x : Occurrence) : Prop :=
  f.Causes c x ∧ f.FullyDeterminedByLaw (f.PriorPhysical x) x ∧
    ¬ f.AmongOrRealizedBy (f.PriorPhysical x) c

/-- Papineau's premise 2, causal influence (p.9): "All mental occurrences have
physical effects." -/
def CausalInfluence (f : Frame Occurrence Kind) : Prop :=
  ∀ c, f.Mental c → ∃ x, f.PhysicalEffectOf c x

/-- Papineau's premise 3 read distributively over causes (p.9): each mental
occurrence with a physical effect has a physical effect it does not overdetermine.
The antecedent keeps this independent of premise 2: a mental occurrence with no
physical effect does not violate it. A distinct reading from
`NotAllOverdeterminedTogether`. -/
def EachCauseNotAllOverdetermined (f : Frame Occurrence Kind) : Prop :=
  ∀ c, f.Mental c → (∃ x, f.PhysicalEffectOf c x) →
    ¬ ∀ x, f.PhysicalEffectOf c x → f.Overdetermines c x

/-- Papineau's premise 3 read collectively (p.9): not every physical effect of
every mental cause is overdetermined. This is the weaker of the two readings
given a mental occurrence with a physical effect; it says nothing of any
particular mental occurrence. -/
def NotAllOverdeterminedTogether (f : Frame Occurrence Kind) : Prop :=
  ¬ ∀ c x, f.Mental c → f.PhysicalEffectOf c x → f.Overdetermines c x

/-- The causal background with the distributive premise 3. -/
def CausalBackground (f : Frame Occurrence Kind) : Prop :=
  Completeness f ∧ CausalInfluence f ∧ EachCauseNotAllOverdetermined f

/-- `e` is physical or realized by something physical. Papineau's strict
conclusion is the first disjunct and his generous one the second (p.11). -/
def PhysicallyBased (f : Frame Occurrence Kind) (e : Occurrence) : Prop :=
  f.Physical e ∨ ∃ r, f.Physical r ∧ f.RealizedBy e r

/-- Eliminative position on the target kind: it has no occurrence. This concerns
the frame's target kind; it does not say that nothing mental in any other
taxonomy occurs. -/
def Eliminative (f : Frame Occurrence Kind) : Prop :=
  ∀ e, ¬ f.Mental e

/-- Reductive position on the target kind: it has an occurrence and the kind
itself is physical (Papineau's stronger property reading, p.10). -/
def Reductive (f : Frame Occurrence Kind) : Prop :=
  (∃ e, f.Mental e) ∧ f.PhysicalKind f.mental

/-- Nonreductive physical position: the target kind has an occurrence, is not
itself a physical kind, and each of its occurrences is physically based, by
having another physical kind (occurrence identity, p.9) or by being realized
(pp.10-11). -/
def Nonreductive (f : Frame Occurrence Kind) : Prop :=
  (∃ e, f.Mental e) ∧ ¬ f.PhysicalKind f.mental ∧ ∀ e, f.Mental e → PhysicallyBased f e

/-- Some occurrence of the target kind is not physically based. This is the
frame's negative predicate only: it does not assert a subsisting bearer, a
nonphysical substance or a q.75 conclusion. -/
def SomeUnbased (f : Frame Occurrence Kind) : Prop :=
  ∃ e, f.Mental e ∧ ¬ PhysicallyBased f e

/-- Some occurrence of the target kind is physically based. -/
def SomeBased (f : Frame Occurrence Kind) : Prop :=
  ∃ e, f.Mental e ∧ PhysicallyBased f e

/-- The three positions remaining once `SomeUnbased` is excluded. -/
def PhysicalistFork (f : Frame Occurrence Kind) : Prop :=
  Eliminative f ∨ Reductive f ∨ Nonreductive f

variable {Principle Operation : Type}

/-- Open and unattributed: each intellectual exercise of `intellect` has an
occurrence of the target mental kind as a token. `tokenOf op e` relates a q.75
operation, which indexes a kind of exercise, to an occurrence in the frame. -/
def ExerciseTokened (f : Frame Occurrence Kind)
    (a : OperationAttribution Principle Operation) (intellect : Principle)
    (tokenOf : Operation → Occurrence → Prop) : Prop :=
  ∀ op, a.IntellectualExercise intellect op → ∃ e, tokenOf op e ∧ f.Mental e

/-- Open and unattributed: the semantic bridge between the modern and the q.75
vocabulary. If a mental token of an intellectual exercise is physically based,
the body shares in that exercise. No source states it, and it fails on a reading
where `BodyShares` means only instrumental exercise through an organ and a
token's physical realization is not such an exercise
(DISAMB-PHYSICAL-BASIS-AND-BODY-SHARING). -/
def PhysicalBasisIsBodySharing (f : Frame Occurrence Kind)
    (a : OperationAttribution Principle Operation) (intellect : Principle)
    (tokenOf : Operation → Occurrence → Prop) : Prop :=
  ∀ op e, a.IntellectualExercise intellect op → tokenOf op e → f.Mental e →
    PhysicallyBased f e → a.BodyShares op

/-- The negation of q.75's `PerSeIntellectualOperation`: no intellectual exercise
of `intellect` is free of bodily sharing. -/
def NoPerSeIntellectualOperation (a : OperationAttribution Principle Operation)
    (intellect : Principle) : Prop :=
  ¬ PerSeIntellectualOperation a intellect

end TruthCore.Alternatives.MindPhysicalism
