module

public import TruthCore.Metaethics.GoodnessFormEnd

/-! Analyst sufficient support, distinct from classifying every admissible
proposal. All meanings and property-identity boundaries of the old profile
remain unchanged; no actual correct account or coverage is established. -/
@[expose] public section
namespace TruthCore.Metaethics.GoodnessCorrectSupport
open TruthCore.Metaethics.GoodnessFormEnd

/-- If the admissible class has a correct account, some admissible correct
account has a named extension. This may transfer to a different witness and
does not require coverage of every admissible account. It DOES entail semantic
named coverage of every admissible CORRECT account, since all correct accounts
coextend with GoodIn. It does not assert existence or property identity. No
globally weakest formulation is claimed. -/
def CorrectAccountSupport {f : Frame} (s : DefinitionSpace f) : Prop :=
  CorrectAccountExists s →
    ∃ d, s.admissible d ∧ CorrectAccount s d ∧ SemanticallyNamed s d

/-- Coverage only of admissible correct accounts under the SAME denotation and
GoodIn dictionary. Wrong admissible accounts may remain extension-unnamed. -/
def CorrectAccountsSemanticallyNamed {f : Frame} (s : DefinitionSpace f) : Prop :=
  ∀ d, s.admissible d → CorrectAccount s d → SemanticallyNamed s d

/-- The conditional existential formulation is equivalent to universal
coverage of CORRECT admissible accounts, not of all admissible candidates. -/
def SupportCoverageEquivalence : Prop :=
  ∀ (f : Frame) (s : DefinitionSpace f),
    CorrectAccountSupport s ↔ CorrectAccountsSemanticallyNamed s

/-- All original proposal meanings are retained; only admissibility is narrowed
for reuse of the existing semantic-elimination theorem at one supported witness. -/
def selectedSpace {f : Frame} (s : DefinitionSpace f) (d : s.Candidate) : DefinitionSpace f :=
  { s with admissible := fun e => e = d }

/-- Same due-actuality frame and same four proposal extensions as the original
finite control; the formerly excluded wrong .other account is now admissible. -/
def widerSpace : DefinitionSpace (artifactWithGood false) :=
  { artifactSpace false with admissible := fun _ => True }

/-- Export both concrete witnesses, all weaker elimination inputs, and actual
failure of global semantic coverage. The wrong account is extension-different,
not a renamed/coextensive property. No property identity is concluded. -/
def StrictControl : Prop :=
  CorrectAccountExists widerSpace ∧ CorrectAccountSupport widerSpace ∧
  FeatureAccountFails widerSpace ∧ ApprovalAccountFails widerSpace ∧
  DueActualityThesis (artifactWithGood false) ∧
  widerSpace.admissible .due ∧ CorrectAccount widerSpace .due ∧
  SemanticallyNamed widerSpace .due ∧
  widerSpace.admissible .other ∧ ¬ CorrectAccount widerSpace .other ∧
  ¬ SemanticallyNamed widerSpace .other ∧ ¬ SemanticNamedCoverage widerSpace
end TruthCore.Metaethics.GoodnessCorrectSupport
