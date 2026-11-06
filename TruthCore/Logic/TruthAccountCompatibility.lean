module

public import TruthCore.Comparison.ExcludedMiddle
public import TruthCore.Greek.Aristotle.MetaphysicsIV7

/-! Analyst compatibility test of the existing exact account predicates, not
historical identification or a complete theory of truth. Proposition truth,
thought truth, composition and stage proof are kept at their actual types.
The source/comparison premises and their full strengths are unchanged. -/
@[expose] public section
namespace TruthCore.Logic.TruthAccountCompatibility
open TruthCore.Comparison.ExcludedMiddle
open TruthCore.English.Iemhoff
open TruthCore.Greek.Aristotle.Metaphysics

structure Thought where
  affirmative : Bool
  content : Prop

def object (t : Thought) : Prop := t.content
def Affirms (t : Thought) : Prop := t.affirmative = true
def Denies (t : Thought) : Prop := t.affirmative = false

def TrueThought (t : Thought) : Prop :=
  match t.affirmative with
  | false => ¬ t.content
  | true => t.content

def FalseThought (t : Thought) : Prop :=
  match t.affirmative with
  | false => t.content
  | true => ¬ t.content

/-- An entire previous encoded intuitionist witness can coexist with the
unchanged Aristotelian composition predicate. Four signed controls keep both
truth and falsity and affirmation and denial populated. -/
def JointEncodedAccounts : Prop :=
  (∃ s : Sig, Intuitionist s ∧ AssertionRequiresProofReading s.Proved s.Asserts ∧
    TruthIsProvabilityReading s.Proved) ∧
  ThoughtTrueOrFalseByCompositionReading object Affirms Denies TrueThought FalseThought ∧
  TrueThought ⟨true, True⟩ ∧ FalseThought ⟨true, False⟩ ∧
  TrueThought ⟨false, False⟩ ∧ FalseThought ⟨false, True⟩

end TruthCore.Logic.TruthAccountCompatibility
