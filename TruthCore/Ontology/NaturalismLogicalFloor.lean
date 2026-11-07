module

public import TruthCore.Results.Ontology.Naturalism.Survivor.Solution
public import TruthCore.Logic.CaseNonContradiction
public import TruthCore.Logic.ExcludedMiddle

/-! Analyst compatibility control for #1109. The exact public ontology and
spatiotemporal frame of the old survivor are reused. Its unnamed thin reason
relation is made explicit so that the same reasoner is witnessed as existing,
located and part of spacetime. This is not a normative-authority calibration,
reification of reason facts, or a complete physical/worldview interpretation.
The inherited constructor `Cand.two` is only the designated singleton anchor's
label; no conclusion about every number or mathematical entity follows. -/

@[expose] public section
namespace TruthCore.Ontology.NaturalismLogicalFloor
open TruthCore.Results.Ontology.Naturalism.Survivor
open TruthCore.Ontology.Naturalism
open TruthCore.Ontology.Spatiotemporal
open TruthCore.Ontology.ConcreteAbstract

/-- The literal relation used anonymously in the earlier survivor proof.
There is no stronger ordinary-role or preference-independent warrant here. -/
def reason (a p : Cand) : Prop := a = .part 0 ∧ p = .part 0

/-- Listed same-model properties only: the old existential survivor certificate
is not substituted for unexported properties of its arbitrary witnesses.
Case-F1 is internal to Lean's negation; EM is explicitly granted by the theorem.
All four spatiotemporal naturalism variants coexist with an actual located
thin-F6 agent. The content role is a candidate, not a reified logical truth. -/
def MatchedFloorControl : Prop :=
  ExistenceNaturalism ontic (Located frame) () ∧
  ExistenceNaturalism ontic (Related frame) () ∧
  ExistenceNaturalism ontic (PartOfSpacetime frame) () ∧
  ConcreteNaturalism ontic (HasEsseInRe inAct ()) (PartOfSpacetime frame) () ∧
  CausalPowerNaturalism power (PartOfSpacetime frame) () ∧
  InteractionNaturalism ontic (PartOfSpacetime frame) () ∧
  TruthCore.Logic.CaseNonContradiction.CasePredicateNonContradiction.{1, 1} ∧
  TruthCore.Logic.ExcludedMiddle ∧
  TruthCore.Logic.EpistemicReasons.ThereAreEpistemicReasons reason ∧
  (∃ a p, reason a p ∧ ontic.ExistsAt () a ∧ Located frame a ∧
    PartOfSpacetime frame a) ∧
  (∀ a p, reason a p → ontic.ExistsAt () a ∧ Located frame a ∧
    PartOfSpacetime frame a)
end TruthCore.Ontology.NaturalismLogicalFloor
