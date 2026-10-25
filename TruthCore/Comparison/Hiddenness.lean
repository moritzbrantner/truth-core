import TruthCore.Hiddenness.Vocabulary

/-!
Finite consistency checks for the hiddenness slice of the rival bundles in
`docs/hiddenness.md`. The complete question map also records claims without a
Lean formalization and unexplained questions. These definitions assert neither
the truth nor the consistency of every commitment of a complete worldview.
-/
namespace TruthCore.Comparison.Hiddenness
open TruthCore.Hiddenness

/-- The Catholic reply keeps perfect love and the empirical challenge, while
replacing immediate access by a reason-qualified norm. The existence of a
sufficient reason for every actual gap remains an explicit open obligation. -/
def CatholicReply (s : Sig) : Prop :=
  GodExists s ∧ GodLoves s ∧ QualifiedOpen s ∧ ReasonForEachGap s ∧
    AccessNeedsBelief s ∧ NonresistantNonbelief s

/-- The non-theistic rival keeps the challenging phenomenon and the conceptual
norms. Its replacement account of inquiry and religious development is recorded
in the same question map; the consistency check is only this logical slice. -/
def Nontheistic (s : Sig) : Prop :=
  NoGod s ∧ GodLoves s ∧ AlwaysOpen s ∧ AccessNeedsBelief s ∧ NonresistantNonbelief s

def CatholicReplyConsistent : Prop := ∃ s : Sig, CatholicReply s

/-- Extension of the frozen logical core with a positive developmental
account. Its universal empirical coverage is open and unattributed. -/
def NontheisticDevelopment (s : Sig) : Prop :=
  NoGod s ∧ GodLoves s ∧ AlwaysOpen s ∧ AccessNeedsBelief s ∧
    NonresistantNonbelief s ∧ ConceptNeeded s ∧ DevelopmentalAccount s

def NontheisticDevelopmentConsistent : Prop := ∃ s : Sig, NontheisticDevelopment s

def NontheisticConsistent : Prop := ∃ s : Sig, Nontheistic s

end TruthCore.Comparison.Hiddenness
