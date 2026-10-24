import TruthCore.Results.Aquinas.SummaTheologiae.AtMostOneMaximeEns.Solution
namespace TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGod
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism (AtMostOneMaximeEns MaximeEnsIsGod GodNamesTheUniqueMaximeEns)

/-- Whatever is maximal in being is God. Let `m` be maximal in being. By the genus
principle at *esse*, `m` causes the being of every other being. By the uniqueness
result (`AQUINAS-ST-I-Q2-A3-AT-MOST-ONE-MAXIME-ENS`), every being maximal in being
is `m`. So `m` is the only being that is above all and the principle of all, and
by the open premise `GodNamesTheUniqueMaximeEns` (the reduced nominal
description suffices; supported by q.13 a.8 ad 2 and *et hoc dicimus Deum*), `m`
is God. -/
theorem maximeEnsIsGod {Being : Type} {Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (God : Being → Prop)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hName : GodNamesTheUniqueMaximeEns InAct MoreIn CausesIn esse God) :
    MaximeEnsIsGod InAct MoreIn esse God := by
  intro m hMax
  -- INF-AQUINAS-AT-MOST-ONE-MAXIME-ENS (result AQUINAS-ST-I-Q2-A3-AT-MOST-ONE-MAXIME-ENS)
  have hUnique : AtMostOneMaximeEns InAct MoreIn esse :=
    AtMostOneMaximeEns.atMostOneMaximeEns InAct MoreIn CausesIn esse hGenus hCauseMore hEM
  -- INF-AQUINAS-MAXIME-ENS-IS-GOD: m causes the being of all others and is the only maximum
  have hCauses : CausesAllInGenus InAct CausesIn esse m := hGenus esse m hMax
  have hOnly : ∀ m', IsMaximumIn InAct MoreIn esse m' → m' = m :=
    fun m' hMax' => hUnique m' m hMax' hMax
  exact hName m hMax hCauses hOnly

/-! ## Countermodels -/

/-- The nominal definition is needed. One being, maximal in being and causing
nothing (there is nothing else); no being is called God. The genus principle,
*Metaphysics* II.1 and excluded middle for identity hold, but the maximum in being
is not God. Nothing but the definition ties the name to the *quarta via*'s
conclusion. -/
theorem withoutNominalDefinitionNotGod :
    ¬ ∀ (Being Respect : Type)
      (InAct : Being → Respect → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
      (God : Being → Prop),
      MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn →
      CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn →
      (∀ a b : Being, a = b ∨ a ≠ b) →
      MaximeEnsIsGod InAct MoreIn esse God := by
  intro h
  have hG := h Unit Unit (fun _ _ => True) (fun _ _ _ => False) (fun _ _ _ => False) ()
    (fun _ => False)
    (fun _ _ _ _ hx _ => absurd rfl hx)
    (fun _ _ _ _ hc => False.elim hc)
    (fun _ _ => Or.inl rfl)
  exact hG () ⟨True.intro, fun _ h => h⟩

/-- Uniqueness is needed, and so *Metaphysics* II.1, from which it is derived. Two
tied maxima cause each other's being (`AtMostOneMaximeEns.TiedMaxima`); no being
is called God. The genus principle and excluded middle for identity hold, and the
nominal definition holds too, because the description "the only being maximal in
being" fits neither. So neither maximum is God: a definite description refers
only when exactly one thing fits. -/
theorem withoutUniquenessNotGod :
    ¬ ∀ (Being Respect : Type)
      (InAct : Being → Respect → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
      (God : Being → Prop),
      MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn →
      (∀ a b : Being, a = b ∨ a ≠ b) →
      GodNamesTheUniqueMaximeEns InAct MoreIn CausesIn esse God →
      MaximeEnsIsGod InAct MoreIn esse God := by
  open AtMostOneMaximeEns.TiedMaxima in
  intro h
  have hG := h Bool Unit inAct more causesEachOther () (fun _ => False)
    (fun _ _ _ x hx _ => fun hEq => hx hEq.symm) identity
    (by
      intro m _ _ hOnly
      cases m
      · exact Bool.noConfusion (hOnly true (bothMaximal true))
      · exact Bool.noConfusion (hOnly false (bothMaximal false)))
  exact hG true (bothMaximal true)

/-- The premises are jointly satisfiable: one being, maximal in being, called God.
The genus principle and *Metaphysics* II.1 hold (there is nothing else to cause),
excluded middle holds for identity, and so does the nominal definition. -/
theorem premisesJointlySatisfiable :
    ∃ (InAct : Unit → Unit → Prop) (MoreIn : Unit → Unit → Unit → Prop)
      (CausesIn : Unit → Unit → Unit → Prop) (God : Unit → Prop),
      MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn ∧
      CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn ∧
      (∀ a b : Unit, a = b ∨ a ≠ b) ∧
      GodNamesTheUniqueMaximeEns InAct MoreIn CausesIn () God ∧
      (∃ m, IsMaximumIn InAct MoreIn () m ∧ God m) :=
  ⟨fun _ _ => True, fun _ _ _ => False, fun _ _ _ => False, fun _ => True,
    fun _ _ _ _ hx _ => absurd rfl hx,
    fun _ _ _ _ hc => False.elim hc,
    fun _ _ => Or.inl rfl,
    fun _ _ _ _ => True.intro,
    ⟨(), ⟨True.intro, fun _ h => h⟩, True.intro⟩⟩

end TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGod
