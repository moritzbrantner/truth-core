import TruthCore.Case.Catholicism.StageOneQuartaVia
import TruthCore.Greek.Aristotle.Metaphysics
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Aquinas.SummaTheologiae.AtMostOneMaximeEns
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism (AtMostOneMaximeEns)

/-- There is at most one maximum in being. From the *quarta via*'s genus principle
(what is maximally such in a genus causes all others of that genus), Aristotle's
*Metaphysics* II.1 (a cause of a quality in another is more such than it), and
excluded middle. If `m'` were other than `m`, then `m`, being maximal in being,
would cause the being of `m'` (genus principle at *esse*; `m'` has being); a cause
of another's being is more a being than it (*Metaphysics* II.1); but nothing is
more a being than `m'`, which is also maximal. So `m'` is not other than `m`, and
by excluded middle `m = m'`. No ordering property of `MoreIn` (antisymmetry,
totality) is used: the causal premises exclude a tie. -/
theorem atMostOneMaximeEns {Being : Type} {Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    AtMostOneMaximeEns InAct MoreIn esse := by
  intro m m' hMax hMax'
  -- INF-AQUINAS-AT-MOST-ONE-MAXIME-ENS: m' is not other than m
  have hNotOther : ¬ m' ≠ m := by
    intro hNe
    have hCauses : CausesIn m m' esse := hGenus esse m hMax m' hNe hMax'.1
    have hMore : MoreIn esse m m' := hCauseMore m m' esse (fun h => hNe h.symm) hCauses
    exact hMax'.2 m hMore
  -- excluded middle on m = m'
  cases hEM (m = m') with
  | inl hSame => exact hSame
  | inr hOther => exact absurd (fun h => hOther h.symm) hNotOther

/-! ## Countermodels

`TiedMaxima`: two beings, both having being, neither more a being than the
other. They are two tied maxima, as in a preorder where both sit at the top.
`causesEachOther` lets each cause the other's being; `causesNothing` has no
causation. -/

namespace TiedMaxima

def inAct : Bool → Unit → Prop := fun _ _ => True
def more : Unit → Bool → Bool → Prop := fun _ _ _ => False
def causesEachOther : Bool → Bool → Unit → Prop := fun a b _ => a ≠ b
def causesNothing : Bool → Bool → Unit → Prop := fun _ _ _ => False

theorem bothMaximal (b : Bool) : IsMaximumIn inAct more () b :=
  ⟨True.intro, fun _ h => h⟩

theorem identity : ∀ a b : Bool, a = b ∨ a ≠ b := by
  intro a b
  cases a <;> cases b
  all_goals first | exact Or.inl rfl | exact Or.inr (fun h => Bool.noConfusion h)

end TiedMaxima

/-- *Metaphysics* II.1 is needed. With two tied maxima that cause each other's
being, the genus principle holds and excluded middle holds for identity, but
there are two maxima in being. A cause that is not more such than its effect
would allow a tie at the top. -/
theorem withoutCauseMoreNotUnique :
    ¬ ∀ (Being Respect : Type)
      (InAct : Being → Respect → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop) (esse : Respect),
      MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn →
      (∀ a b : Being, a = b ∨ a ≠ b) →
      AtMostOneMaximeEns InAct MoreIn esse := by
  open TiedMaxima in
  intro h
  have hU := h Bool Unit inAct more causesEachOther ()
    (fun _ _ _ x hx _ => fun hEq => hx hEq.symm) identity
  exact Bool.noConfusion (hU true false (bothMaximal true) (bothMaximal false))

/-- The genus principle is needed. With two tied maxima and no causation,
*Metaphysics* II.1 holds vacuously and excluded middle holds for identity, but
there are two maxima in being. -/
theorem withoutGenusNotUnique :
    ¬ ∀ (Being Respect : Type)
      (InAct : Being → Respect → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop) (esse : Respect),
      CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn →
      (∀ a b : Being, a = b ∨ a ≠ b) →
      AtMostOneMaximeEns InAct MoreIn esse := by
  open TiedMaxima in
  intro h
  have hU := h Bool Unit inAct more causesNothing ()
    (fun _ _ _ _ hc => False.elim hc) identity
  exact Bool.noConfusion (hU true false (bothMaximal true) (bothMaximal false))

end TruthCore.Results.Aquinas.SummaTheologiae.AtMostOneMaximeEns
