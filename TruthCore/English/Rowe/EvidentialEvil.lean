/-!
Rowe, “The Problem of Evil and Some Varieties of Atheism” (1979),
pp. 335–339, read in the materialized ROWE-EVIL-ATHEISM-1979-FULL witness.
The published simplified premises (1) and (2) are separated from their
inductive warrant. No probability or inference from unrecognized to absent
costs is built into this vocabulary. These are event/being/outcome relations,
not the voluntary-operation vocabulary of Aquinas' culpa account.
-/
namespace TruthCore.English.Rowe

/-- A scoped interpretation, not an identification with the existing Catholic
signature: that signature has neither counterfactual costs nor recognition.
`Cost b e o` says avoiding e would require losing outcome o (when a good),
or permitting o (when an evil). `GreaterGood` includes justice and goods
not later in time; a merely replaceable conjunction of good and suffering
is excluded (p.336 nn.2–3). The comparative and counterfactual predicates
remain open philosophical commitments, not facts established by the model. -/
structure Sig where
  Being : Type
  Event : Type
  Outcome : Type
  Omniscient : Being → Prop
  Omnipotent : Being → Prop
  WhollyGood : Being → Prop
  Occurs : Event → Prop
  IntenseSuffering : Event → Prop
  CanPrevent : Being → Event → Prop
  Cost : Being → Event → Outcome → Prop
  GreaterGood : Outcome → Event → Prop
  EqualOrWorseEvil : Outcome → Event → Prop
  /-- Recognition by the fixed finite investigator in the given interpretation;
  absence of recognition does not assert absence of an actual cost. -/
  RecognizesCost : Being → Event → Outcome → Prop

/-- An unavoidable unreplaceable greater-good loss or equal/worse evil cost.
A necessary condition for permission is not a sufficient moral justification.
This keeps the published simplified version: p.336 n.3 explicitly considers
also a balance-neutral good; that qualification is not proved equivalent. -/
def BlockingCost (s : Sig) (b : s.Being) (e : s.Event) : Prop :=
  ∃ o, s.Cost b e o ∧ (s.GreaterGood o e ∨ s.EqualOrWorseEvil o e)

/-- Rowe p.336 premise (1), with the omniscient/omnipotent hypothetical
preventer universally explicit. An actual suffering event is required;
existence of a theistic being is not presupposed. -/
def GratuitousSufferingReading (s : Sig) : Prop :=
  ∃ e, s.Occurs e ∧ s.IntenseSuffering e ∧
    ∀ b, s.Omniscient b → s.Omnipotent b → s.CanPrevent b e ∧ ¬ BlockingCost s b e

/-- Rowe pp.336–337 premise (2), stated in its necessary-condition form:
a wholly good omniscient being permitting preventable intense suffering
must face a blocking cost. It does not say every greater good licenses evil. -/
def PermissionConstraintReading (s : Sig) : Prop :=
  ∀ b e, s.Omniscient b → s.WhollyGood b → s.Occurs e →
    s.IntenseSuffering e → s.CanPrevent b e → BlockingCost s b e

/-- Rowe's narrow theism: existence of a being with all three attributes.
This is not every broad notion of deity or the whole Catholic theory. -/
def TheisticBeingExists (s : Sig) : Prop :=
  ∃ b, s.Omniscient b ∧ s.Omnipotent b ∧ s.WhollyGood b

def NoTheisticBeing (s : Sig) : Prop := ¬ TheisticBeingExists s

def NoGratuitousSuffering (s : Sig) : Prop := ¬ GratuitousSufferingReading s

/-- Finite-investigator projection of “so far as we can see” (p.337):
a preventable occurring intense suffering has no recognized blocking cost.
This is deliberately weaker than Rowe's total evidence in p.338 n.5,
which additionally invokes variety, profusion and apparently unnecessary
connections. It does not encode rational warrant, likelihood or probability. -/
def ApparentlyPointlessSuffering (s : Sig) : Prop :=
  ∃ e, s.Occurs e ∧ s.IntenseSuffering e ∧
    ∀ b, s.Omniscient b → s.Omnipotent b → s.CanPrevent b e ∧
      ¬ ∃ o, s.Cost b e o ∧ s.RecognizesCost b e o ∧
        (s.GreaterGood o e ∨ s.EqualOrWorseEvil o e)

end TruthCore.English.Rowe
