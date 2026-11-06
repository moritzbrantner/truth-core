module

public import TruthCore.Case.Catholicism.Root
public import TruthCore.Logic.ExcludedMiddle

/-!
# Church criteria and the visible-stage premise

A selected Church predicate and a spiritual-community predicate apply to the
same Society objects as the root. They are not two societies or individual
membership sets. The existing VisibleWithAuthority keeps its visible, enduring,
authoritative reading; no new criterion supplies its historical applicability.
An ordinary community can have both visible offices and inward fellowship;
neither description alone specifies whether the other aspect is present.

The three analyst definition propositions compare extensions: Church iff the
visible criterion, Church iff the spiritual criterion, and Church iff both.
A criterion is not an exclusion: spiritual does not mean invisible, and a
visible criterion does not deny spiritual communion. Joint aspects therefore
need not compete exclusively. These are not new attributions of the conciliar
source or an exhaustive census of ecclesiologies. Named coverage remains open,
with an explicit further extension. No particular modern body's identity or
local-to-universal identification is assumed.
-/

@[expose] public section

namespace TruthCore.Case.Catholicism.StageThree.ChurchDefinitions

open TruthCore.Case.Catholicism

/-- A selected Church has the root's visible criterion exactly; this does not
exclude a spiritual aspect of that same society. -/
def VisibleCriterion (σ : Signature) (church : σ.Society → Prop) : Prop :=
  ∀ c, church c ↔ σ.VisibleWithAuthority c

/-- A selected Church has the spiritual criterion exactly; spirituality does
not itself exclude the visible predicate. -/
def SpiritualCriterion (σ : Signature) (church spiritual : σ.Society → Prop) : Prop :=
  ∀ c, church c ↔ spiritual c

/-- The same body satisfies both aspects, without separating it into bodies. -/
def JointAspectCriterion (σ : Signature) (church spiritual : σ.Society → Prop) : Prop :=
  ∀ c, church c ↔ σ.VisibleWithAuthority c ∧ spiritual c

/-- Open named-extension coverage within this fixed society/profile scope. -/
def NamedChurchCoverage (σ : Signature) (church spiritual : σ.Society → Prop) : Prop :=
  VisibleCriterion σ church ∨ SpiritualCriterion σ church spiritual ∨
    JointAspectCriterion σ church spiritual

/-- A genuinely different selected extension, not merely another name. -/
def AdditionalChurchCriterion (σ : Signature) (church spiritual : σ.Society → Prop) : Prop :=
  ¬ VisibleCriterion σ church ∧ ¬ SpiritualCriterion σ church spiritual ∧
    ¬ JointAspectCriterion σ church spiritual

/-- Structural coverage retains the relevant further-extension option. -/
def ChurchCriterionCases (σ : Signature) (church spiritual : σ.Society → Prop) : Prop :=
  VisibleCriterion σ church ∨ SpiritualCriterion σ church spiritual ∨
    JointAspectCriterion σ church spiritual ∨ AdditionalChurchCriterion σ church spiritual

/-- The spiritual calibration is actually false, rather than merely
insufficient by itself for the stage-5 target. -/
def SpiritualCriterionFails (σ : Signature) (church spiritual : σ.Society → Prop) : Prop :=
  ¬ SpiritualCriterion σ church spiritual

/-- A historical founding witness for the selected Church predicate. It does
not already assert visibility, spiritual communion or Catholic identity. -/
def ChristFoundedSelectedChurch (σ : Signature) (church : σ.Society → Prop) : Prop :=
  ∃ c, σ.Founded σ.jesus c ∧ church c

/-- Six schema controls: overlap; spiritual and visible criteria alone;
nonempty joint-only criterion; and further criteria with opposite stage-5
verdicts. These establish neither actual Church history nor stage-6 identity. -/
def ChurchCriterionModels : Prop :=
  (∃ σ : Signature, ∃ church spiritual : σ.Society → Prop,
    ChristFoundedSelectedChurch σ church ∧ VisibleCriterion σ church ∧
    SpiritualCriterion σ church spiritual ∧ JointAspectCriterion σ church spiritual ∧
    ChristFoundedVisibleChurch σ) ∧
  (∃ σ : Signature, ∃ church spiritual : σ.Society → Prop,
    ChristFoundedSelectedChurch σ church ∧ SpiritualCriterion σ church spiritual ∧
    ¬ VisibleCriterion σ church ∧ ¬ JointAspectCriterion σ church spiritual ∧
    ¬ ChristFoundedVisibleChurch σ) ∧
  (∃ σ : Signature, ∃ church spiritual : σ.Society → Prop,
    ChristFoundedSelectedChurch σ church ∧ VisibleCriterion σ church ∧
    ¬ SpiritualCriterion σ church spiritual ∧ ¬ JointAspectCriterion σ church spiritual ∧
    ChristFoundedVisibleChurch σ) ∧
  (∃ σ : Signature, ∃ church spiritual : σ.Society → Prop,
    ChristFoundedSelectedChurch σ church ∧ JointAspectCriterion σ church spiritual ∧
    ¬ VisibleCriterion σ church ∧ ¬ SpiritualCriterion σ church spiritual ∧
    ChristFoundedVisibleChurch σ) ∧
  (∃ σ : Signature, ∃ church spiritual : σ.Society → Prop,
    ChristFoundedSelectedChurch σ church ∧ AdditionalChurchCriterion σ church spiritual ∧
    ChristFoundedVisibleChurch σ) ∧
  (∃ σ : Signature, ∃ church spiritual : σ.Society → Prop,
    ChristFoundedSelectedChurch σ church ∧ AdditionalChurchCriterion σ church spiritual ∧
    ¬ ChristFoundedVisibleChurch σ)

end TruthCore.Case.Catholicism.StageThree.ChurchDefinitions
