/-!
Typed specifications for selected comparisons of open propositions. These are
descriptions, not proof-status records: certificates remain corpus results.
Background propositions are ordered and shared by every obligation. Vocabulary
and typeclass parameters belong to the enclosing specification declaration.
-/
namespace TruthCore.Logic.StrengthComparison

/-- A selected comparison, without any assertion that its obligations hold.
`delta` is proposed extra required content; `remainder` describes cases admitted
only by the weaker proposition and must not be confused with that requirement. -/
structure ComparisonSpec where
  background : List Prop := []
  stronger : Prop
  weaker : Prop
  delta : Prop
  remainder : Prop := weaker ∧ ¬ stronger

/-- Introduce exactly the selected background as ordered implication premises. -/
def Under (s : ComparisonSpec) (conclusion : Prop) : Prop :=
  s.background.foldr (fun premise result => premise → result) conclusion

def Implication (s : ComparisonSpec) : Prop := Under s (s.stronger → s.weaker)
def DeltaForward (s : ComparisonSpec) : Prop := Under s (s.stronger → s.delta)
def Reconstruction (s : ComparisonSpec) : Prop := Under s (s.weaker → s.delta → s.stronger)
def Equivalence (s : ComparisonSpec) : Prop := Under s (s.stronger ↔ s.weaker ∧ s.delta)
def Converse (s : ComparisonSpec) : Prop := Under s (s.weaker → s.stronger)
def AllowedCases (s : ComparisonSpec) : Prop := Under s (s.weaker ↔ s.stronger ∨ s.remainder)
def RemainderIdentity (s : ComparisonSpec) : Prop := Under s (s.remainder ↔ s.weaker ∧ ¬ s.stronger)

/-- A checked separating setting satisfies that same background and the weaker
proposition while falsifying the stronger one. It does not establish that its
interpretation is metaphysically possible. -/
def Separation (s : ComparisonSpec) : Prop :=
  s.background.foldr And True ∧ s.weaker ∧ ¬ s.stronger

end TruthCore.Logic.StrengthComparison
