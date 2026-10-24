import TruthCore.Case.Catholicism.StageOneConvergence
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaNecessaryPerSeIsMaximeEns
open TruthCore.Logic
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (NecessaryBeingHasBeing CauseOfNecessaryBeingCausesItsNecessity
  NecessaryPerSeIsMaximeEns)

/-- The *tertia via* converges on the *quarta via*. Let `n` be necessary per se
and `m` maximal in being. If `n` were other than `m`: `n` has being, so `m`
causes its being (genus principle at *esse*), and so causes its necessity; then
`n` has a cause of its necessity from elsewhere, against its being necessary per
se. So `n` is not other than `m`, and by excluded middle `n = m`. The argument
has the shape of the *prima via*'s identification with the maximal being. -/
theorem necessaryPerSeIsMaximeEns {Being Time Respect : Type}
    (Possible : (Time → Prop) → Prop) (IsAt : Being → Time → Prop)
    (CausesNecessityOf : Being → Being → Prop)
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hHasBeing : NecessaryBeingHasBeing Possible IsAt InAct esse)
    (hCauseNecessity :
      CauseOfNecessaryBeingCausesItsNecessity Possible IsAt CausesIn esse CausesNecessityOf)
    (hEM : ExcludedMiddle) :
    NecessaryPerSeIsMaximeEns Possible IsAt CausesNecessityOf InAct MoreIn esse := by
  intro n hPerSe m hMax
  obtain ⟨hNecessary, hNoCause⟩ := hPerSe
  cases hEM (n = m) with
  | inl hSame => exact hSame
  | inr hOther =>
    exfalso
    -- INF-TERTIA-VIA-MAXIME-ENS-CAUSES-BEING-OF-NECESSARY
    have hCauses : CausesIn m n esse := hGenus esse m hMax n hOther (hHasBeing n hNecessary)
    -- INF-TERTIA-VIA-NECESSARY-PER-SE-IS-MAXIME-ENS
    exact hNoCause ⟨m, fun h => hOther h.symm, hCauseNecessity m n hNecessary hCauses⟩

/-- The bridge from causing being to causing necessity is needed. Two beings, both
necessary (nothing is possible); `a` is maximal in being and causes `b`'s being,
but nothing causes anything's necessity, so `b` is necessary per se and is not
the maximum. -/
theorem withoutNecessityBridgeTwoFirsts :
    ∃ (Possible : (Unit → Prop) → Prop) (IsAt : Bool → Unit → Prop)
      (CausesNecessityOf : Bool → Bool → Prop) (InAct : Bool → Unit → Prop)
      (MoreIn : Unit → Bool → Bool → Prop) (CausesIn : Bool → Bool → Unit → Prop),
      MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn ∧
      NecessaryBeingHasBeing Possible IsAt InAct () ∧
      ¬ CauseOfNecessaryBeingCausesItsNecessity Possible IsAt CausesIn () CausesNecessityOf ∧
      ¬ NecessaryPerSeIsMaximeEns Possible IsAt CausesNecessityOf InAct MoreIn () := by
  refine ⟨fun _ => False, fun _ _ => True, fun _ _ => False, fun _ _ => True,
    fun _ y x => y = true ∧ x = false, fun c x _ => c = true ∧ x = false, ?_,
    fun _ _ => trivial, ?_, ?_⟩
  · intro r m hMax x hOther _
    obtain ⟨_, hTop⟩ := hMax
    cases m <;> cases x
    · exact absurd rfl hOther
    · exact absurd ⟨rfl, rfl⟩ (hTop true)
    · exact ⟨rfl, rfl⟩
    · exact absurd rfl hOther
  · intro h
    exact h true false (fun h => h) ⟨rfl, rfl⟩
  · intro h
    have hMax : IsMaximumIn (fun (_ : Bool) (_ : Unit) => True)
        (fun _ y x => y = true ∧ x = false) () true :=
      ⟨trivial, fun _ hy => Bool.noConfusion hy.2⟩
    have := h false ⟨fun h => h, fun ⟨_, _, h⟩ => h⟩ true hMax
    exact Bool.noConfusion this

end TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaNecessaryPerSeIsMaximeEns
