import TruthCore.Alternatives.FideismReference
import TruthCore.Case.Catholicism.StageOneQuartaVia
namespace TruthCore.Results.Alternatives.FideismReference
open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.FideismReference
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- The *Dei Filius* ch. 1 / can. I.1 parallel (#1010). If the council defines a
move confessing, with the name `god`, that there is a being it names, and what
the council defines is endorsed by the practice's own standards, then the
fideist bundle of internal grammar, grammar-fixed reference and the WF-P1
reconstruction fails: the defined confession is correct by internality, so by
grammar-fixed reference the name refers to some being, which the
reconstruction denies. -/
theorem fideistReferenceBundleFails {Being : Type} (N : NamingPractice Being) (god : N.Name)
    (hCouncil : CouncilConfessesGodReading N god)
    (hDefinition : DefinitionIsOwnStandardReading N.toPractice) :
    FideistReferenceBundleFails N god := by
  sorry

/-- The council premise is needed. -/
theorem needsCouncil :
    ¬ ∀ (Being : Type) (N : NamingPractice Being) (god : N.Name),
      DefinitionIsOwnStandardReading N.toPractice → FideistReferenceBundleFails N god := by
  sorry

/-- The definition bridge is needed (the escape that conciliar teaching is
theology, not grammar). -/
theorem needsDefinitionIsOwnStandard :
    ¬ ∀ (Being : Type) (N : NamingPractice Being) (god : N.Name),
      CouncilConfessesGodReading N god → FideistReferenceBundleFails N god := by
  sorry

/-- WF-P1's own escape: without grammar-fixed reference, internal grammar and
the no-being reconstruction hold together with the council and the definition
bridge. The defined confession is correct, yet the name refers to nothing. So
the parallel bites only a fideist who also holds WF-P2's reference thesis. -/
theorem noBeingSurvivesWithoutGrammarFixedReference :
    ∃ (N : NamingPractice Unit) (god : N.Name),
      CouncilConfessesGodReading N god ∧ DefinitionIsOwnStandardReading N.toPractice ∧
        InternalGrammarReading N.toPractice ∧ GodNamesNoBeingReading N god ∧
          ¬ GrammarFixesReferenceReading N god := by
  sorry

/-- Link to the leaf `GodNamesTheFullyDescribedPrinciple`, as a schema with the
leaf's predicate instantiated by the practice-use reference of `god`: the leaf
and the no-being reconstruction together imply that no being fits the full
description. So the reconstruction is a rival of the leaf exactly where some
being fits it. -/
theorem noBeingExcludesFullDescription {Being : Type} {Respect : Type}
    (N : NamingPractice Being) (god : N.Name)
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (ComponentOf : Being → Being → Prop)
    (hLeaf : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf
      (N.RefersTo god))
    (hNoBeing : GodNamesNoBeingReading N god) :
    ∀ m, IsMaximumIn InAct MoreIn esse m → CausesAllInGenus InAct CausesIn esse m →
      CausesEveryPerfectionOfOthers InAct CausesIn m → RemoteFromAll ComponentOf m →
        ¬ (∀ m', IsMaximumIn InAct MoreIn esse m' → m' = m) := by
  sorry

/-- Link to the leaf `UniquePureActFirstMoverIsGod`, as the same schema: with
the no-being reconstruction, no pure-act first unmoved mover is the only one. -/
theorem noBeingExcludesUniquePureActFirstMover {Being : Type} {Respect : Type}
    (N : NamingPractice Being) (god : N.Name)
    (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
    (PureAct : Being → Prop)
    (hLeaf : UniquePureActFirstMoverIsGod MovedIn MovesIn PureAct (N.RefersTo god))
    (hNoBeing : GodNamesNoBeingReading N god) :
    ∀ f, IsFirstUnmovedMover MovedIn MovesIn f → PureAct f →
      ¬ (∀ g, IsFirstUnmovedMover MovedIn MovesIn g → g = f) := by
  sorry

end TruthCore.Results.Alternatives.FideismReference
