import TruthCore.Results.Aquinas.SummaTheologiae.AtMostOneMaximeEns.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article8
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1
namespace TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGodViaFullDescription
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism (MaximeEnsIsGod AtMostOneMaximeEns GodNamesTheFullyDescribedPrinciple
  CauseOfBeingCausesEveryPerfection CausesEveryPerfectionOfOthers RemoteFromAll)

/-- Version (a) of the discharge (owner decision on #143, 2026-10-24): the
unique maximum in being meets the fuller nominal definition, so it is God. Let
`m` be maximal in being. By the genus principle at *esse* it causes the being of
every other being; by the uniqueness result it is the only maximum. It causes
every perfection of every other being: whatever another being is in act in, that
being has being (q.4 a.1 ad 3), so `m` causes its being and therefore that
perfection. And it is part of nothing, since no component is maximal in being
(q.3 a.8). So the fuller description applies. -/
theorem maximeEnsIsGodViaFullDescription {Being : Type} {Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (ComponentOf : Being → Being → Prop) (God : Being → Prop)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hPerfections : CauseOfBeingCausesEveryPerfection InAct CausesIn esse)
    (hNoComponent : NoComponentIsMaximalInBeingReading InAct MoreIn esse ComponentOf)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf God) :
    MaximeEnsIsGod InAct MoreIn esse God := by
  intro m hMax
  -- INF-AQUINAS-FULL-DESCRIPTION-CAUSE-OF-BEING: the genus principle at esse
  have hCauses : CausesAllInGenus InAct CausesIn esse m := hGenus esse m hMax
  -- INF-AQUINAS-AT-MOST-ONE-MAXIME-ENS (result AQUINAS-ST-I-Q2-A3-AT-MOST-ONE-MAXIME-ENS)
  have hUnique : AtMostOneMaximeEns InAct MoreIn esse :=
    AtMostOneMaximeEns.atMostOneMaximeEns InAct MoreIn CausesIn esse hGenus hCauseMore hEM
  -- INF-AQUINAS-MAXIME-ENS-CAUSES-EVERY-PERFECTION
  have hEvery : CausesEveryPerfectionOfOthers InAct CausesIn m :=
    fun x r hOther hAct => hPerfections m x r (hCauses x hOther (hBeing x r hAct)) hAct
  -- INF-AQUINAS-MAXIME-ENS-REMOTE-FROM-ALL
  have hRemote : RemoteFromAll ComponentOf m :=
    fun x hComponent => hNoComponent m x hComponent hMax
  -- INF-AQUINAS-MAXIME-ENS-IS-GOD-VIA-FULL-DESCRIPTION
  exact hFull m hMax hCauses hEvery hRemote (fun m' hMax' => hUnique m' m hMax' hMax)

/-! ## Countermodels

Both models satisfy the genus principle, *Metaphysics* II.1 and excluded middle
for identity (the uniqueness result's premises), and the fuller definition. In
each, exactly one of the two new premises fails, and the maximum in being is not
God. -/

namespace Models

/-- Beings `true` (`a`) and `false` (`b`); respects `true` (*esse*) and `false`
(a second perfection). `a` is more a being than `b`; `b` is more in the second
perfection than `a`. -/
def more : Bool → Bool → Bool → Prop :=
  fun r y x => (r = true ∧ y = true ∧ x = false) ∨ (r = false ∧ y = false ∧ x = true)

/-- `a` causes `b`'s being; `b` causes `a`'s second perfection. -/
def causes : Bool → Bool → Bool → Prop :=
  fun c x r => (c = true ∧ x = false ∧ r = true) ∨ (c = false ∧ x = true ∧ r = false)

theorem genus : MaximumInGenusCausesAllInGenusReading (fun (_ : Bool) (_ : Bool) => True)
    more causes := by
  intro r m hMax x hOther _
  obtain ⟨_, hTop⟩ := hMax
  cases r <;> cases m <;> cases x
  all_goals first
    | exact absurd rfl hOther
    | exact Or.inl ⟨rfl, rfl, rfl⟩
    | exact Or.inr ⟨rfl, rfl, rfl⟩
    | exact absurd (Or.inl ⟨rfl, rfl, rfl⟩) (hTop true)
    | exact absurd (Or.inr ⟨rfl, rfl, rfl⟩) (hTop false)

theorem causeMore : CauseOfQualityInAnotherIsMoreSuchReading causes more :=
  fun _ _ _ _ h => by
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h3, h1, h2⟩
    · exact Or.inr ⟨h3, h1, h2⟩

end Models

/-- The bridge from causing being to causing perfections is needed. In the model
`a` is the only maximum in being and causes `b`'s being, but not `b`'s second
perfection. Nothing is a component of anything. `God` is true of what causes
every perfection of the others, so the fuller definition holds, yet `a` is not
God. -/
theorem withoutPerfectionsBridgeNotGod :
    ∃ (InAct : Bool → Bool → Prop) (MoreIn : Bool → Bool → Bool → Prop)
      (CausesIn : Bool → Bool → Bool → Prop) (ComponentOf : Bool → Bool → Prop)
      (God : Bool → Prop),
      MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn ∧
      CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn ∧
      (∀ a b : Bool, a = b ∨ a ≠ b) ∧
      ActualityOnlyInsofarAsBeingReading InAct true ∧
      NoComponentIsMaximalInBeingReading InAct MoreIn true ComponentOf ∧
      GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn true ComponentOf God ∧
      ¬ CauseOfBeingCausesEveryPerfection InAct CausesIn true ∧
      ¬ MaximeEnsIsGod InAct MoreIn true God := by
  refine ⟨fun _ _ => True, Models.more, Models.causes, fun _ _ => False,
    CausesEveryPerfectionOfOthers (fun _ _ => True) Models.causes,
    Models.genus, Models.causeMore, fun a b => by cases a <;> cases b <;> simp,
    fun _ _ _ => trivial, fun _ _ h => h.elim, fun _ _ _ hEvery _ _ => hEvery, ?_, ?_⟩
  · intro h
    rcases h true false false (Or.inl ⟨rfl, rfl, rfl⟩) trivial with ⟨_, _, h⟩ | ⟨h, _, _⟩
    · exact Bool.noConfusion h
    · exact Bool.noConfusion h
  · intro h
    have hMax : IsMaximumIn (fun (_ : Bool) (_ : Bool) => True) Models.more true true :=
      ⟨trivial, fun y hy => by
        rcases hy with ⟨_, _, h⟩ | ⟨h, _, _⟩
        · exact Bool.noConfusion h
        · exact Bool.noConfusion h⟩
    rcases h true hMax false false (fun h => Bool.noConfusion h) trivial with
      ⟨_, _, h⟩ | ⟨h, _, _⟩
    · exact Bool.noConfusion h
    · exact Bool.noConfusion h

/-- The *remotum ab omnibus* premise (q.3 a.8) is needed. One being, maximal in
being and a component of itself; `God` is true of what is remote from all, so
the fuller definition holds, yet the maximum is not God. -/
theorem withoutNoComponentNotGod :
    ∃ (InAct : Unit → Unit → Prop) (MoreIn : Unit → Unit → Unit → Prop)
      (CausesIn : Unit → Unit → Unit → Prop) (ComponentOf : Unit → Unit → Prop)
      (God : Unit → Prop),
      MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn ∧
      CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn ∧
      (∀ a b : Unit, a = b ∨ a ≠ b) ∧
      ActualityOnlyInsofarAsBeingReading InAct () ∧
      CauseOfBeingCausesEveryPerfection InAct CausesIn () ∧
      GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn () ComponentOf God ∧
      ¬ NoComponentIsMaximalInBeingReading InAct MoreIn () ComponentOf ∧
      ¬ MaximeEnsIsGod InAct MoreIn () God :=
  ⟨fun _ _ => True, fun _ _ _ => False, fun _ _ _ => False, fun _ _ => True,
    RemoteFromAll (fun _ _ => True),
    fun _ _ _ _ hx _ => absurd rfl hx, fun _ _ _ _ h => h.elim, fun _ _ => Or.inl rfl,
    fun _ _ _ => trivial, fun _ _ _ h _ => h.elim, fun _ _ _ _ hRemote _ => hRemote,
    fun h => h () () trivial ⟨trivial, fun _ h => h⟩,
    fun h => h () ⟨trivial, fun _ h => h⟩ () trivial⟩

end TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGodViaFullDescription
