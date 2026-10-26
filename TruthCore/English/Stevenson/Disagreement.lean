/-!
Stevenson, The Emotive Meaning of Ethical Terms (1937), pp. 27–29.
This structured refinement is needed because the shared signature's primitive
ClashInAttitude does not distinguish opposed interests from opposed beliefs.
The signature reuses the comparison's sentence carrier for the practical object
under discussion; no identification of interests with beliefs is made.
-/
namespace TruthCore.English.Stevenson

/-- Interest opposition requires favourable versus unfavourable interest and
neither participant being content to leave the other's interest unchanged
(p. 27). `SeeksChange x y p` records this practical orientation, not success,
coercion, or a logical contradiction. -/
def InterestDisagreement {Agent Sentence : Type}
    (Favors Disfavors : Agent → Sentence → Prop)
    (SeeksChange : Agent → Agent → Sentence → Prop)
    (x y : Agent) (p : Sentence) : Prop :=
  Favors x p ∧ Disfavors y p ∧ SeeksChange x y p ∧ SeeksChange y x p

/-- Agreement on every designated factual sentence, not omniscience or truth
of those beliefs. -/
def FactualAgreement {Agent Sentence : Type}
    (Factual : Sentence → Prop) (Believes : Agent → Sentence → Prop)
    (x y : Agent) : Prop :=
  ∀ p, Factual p → (Believes x p ↔ Believes y p)

/-- The primary reading distinguishes interest from belief disagreement:
clash has the structured practical sense, and there can be a moral clash
between people who agree on all designated factual matters (pp. 27–29).
Existence here is representability in an interpretation, not an empirical
claim that such people actually exist. It does not assert that factual reasons
never change interests: p. 28 explicitly allows that they often do. -/
def DisagreementReading {Agent Sentence : Type}
    (Moral Factual : Sentence → Prop)
    (Favors Disfavors Believes : Agent → Sentence → Prop)
    (SeeksChange Clash : Agent → Agent → Sentence → Prop) : Prop :=
  (∀ x y p, Clash x y p ↔ InterestDisagreement Favors Disfavors SeeksChange x y p) ∧
    ∃ x y p, Moral p ∧ Clash x y p ∧ FactualAgreement Factual Believes x y ∧
      ∃ f, Factual f

end TruthCore.English.Stevenson
