import Mathlib.Data.Set.Defs
import TruthCore.Explanation.PSRStrength

/-!
Owner-proposed compression of multiple actual conditions into one conjunction.
A joint condition is a predicate on worlds, not a new causal substance or an
assumption that the fact domain contains a matching aggregate token. For a
Groups record use S = h.members g, including contributors AND enablers.
The existing Arena's beings, facts, truth and causal relations remain unchanged.
No explanation, individual sufficiency or causal direction follows from this
logical packaging. See docs/notes/underived-essence-identity.md.
-/
namespace TruthCore.Explanation.JointCondition
open TruthCore.Explanation.PSRStrength
open TruthCore.German.Kant.CosmologicalInference

/-- All selected members hold together at a world, with no finiteness demand. -/
def JointTrue {W B F : Type} (A : Arena W B F) (S : Set F) (w : W) : Prop :=
  ∀ f ∈ S, A.holds w f

/-- Some selected member actually holds and fails at an accessible world,
using the existing fact-level Contingent predicate. -/
def ContingentMember {W B F : Type} (A : Arena W B F) (S : Set F) (w : W) : Prop :=
  ∃ f ∈ S, Contingent A w f

/-- Actual joint truth plus accessible failure of that same fixed conjunction.
This specializes the existing actual-and-accessible-absence contingency shape
without inventing an aggregate fact/being in A's original domains. It is not
Hume's distinct two-possibilities-only predicate. -/
def JointContingent {W B F : Type} (A : Arena W B F) (S : Set F) (w : W) : Prop :=
  JointTrue A S w ∧ ∃ v, Access A w v ∧ ¬ JointTrue A S v

def JointNecessary {W B F : Type} (A : Arena W B F) (S : Set F) (w : W) : Prop :=
  ∀ v, Access A w v → JointTrue A S v

def MembersNecessary {W B F : Type} (A : Arena W B F) (S : Set F) (w : W) : Prop :=
  ∀ f ∈ S, ∀ v, Access A w v → A.holds v f

/-- Necessity of a fixed conjunction is necessity of every selected member. -/
def NecessityEquivalence : Prop :=
  ∀ (W B F : Type) (A : Arena W B F) (S : Set F) (w : W),
    JointNecessary A S w ↔ MembersNecessary A S w

/-- The SAME existing #755 ground model: the ground individual is actual and
necessary, choice is contingent, and their joint existence condition is
contingent. This changes no old existence/causal/explanatory interpretation. -/
def MixedCertificate : Prop :=
  (∀ v, (ground false).holds v GroundFact.ground) ∧
  Contingent (ground false) false GroundFact.choice ∧
  JointContingent (ground false) {GroundFact.ground, GroundFact.choice} false ∧
  NecessaryBeing (ground false).ontic false

end TruthCore.Explanation.JointCondition
