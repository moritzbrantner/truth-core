module

public import TruthCore.Latin.Aquinas.DeEnte.ExtrinsicSource
public import TruthCore.Causality.TermSenseForks2
public import TruthCore.Case.Catholicism.CauseOfBeingHasBeing

/-!
# De ente: from distinct esse to an extrinsic source (#1629)

Conditional derivations for the *De ente* c.3 [69874] inference (Baur/Koch
numbering; Leonine c.4). The extra premise that turns
"not self-caused" into "caused by another" is `DistinctEsseHasSomeCause`
(every actual distinct esse has some cause of being). In De ente's vocabulary
it comes from `DistinctEsseNatureOrOtherCause` (esse only, distinct-esse
beings only, nature disjunct in the efficient sense `NATURE_SOURCE_2`) and the
self-causation reading. The weak exhaustiveness is derived from the
literal De ente disjunction (`NATURE_SOURCE_1`, every respect) only through
the open sense bridge `NatureSourcedDistinctEsseIsEfficient`; the
`FormalNatureControl` interpretation shows that without that bridge the literal
disjunction and the rejection of efficient self-causation give no extrinsic
source. The conclusion certifies a cause of being other than x (`c ≠ x`, not
non-constituency) and in act as to being; "efficient" in the q.3 a.4 name is
not a further condition of the type. None of the premises is proved here.
-/

@[expose] public section

namespace TruthCore.Results.Aquinas.DeEnte.ExtrinsicSource

open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Causality.TermSenseForks (NothingCausesItsOwnBeing)
open TruthCore.Case.Catholicism.CauseOfBeingHasBeing (CauseOfBeingInActAsToBeing)

variable {B P R : Type}

/-- The De ente decomposition of the extra premise: the weak exhaustiveness
and the self-causation reading give every actual distinct-esse being some
cause of its esse (its own self, on the quiddity horn). -/
theorem distinctEsseCausedFromDeEnte (p : Profile B P R) (n : NatureSource B R)
    (hExhaustive : DistinctEsseNatureOrOtherCause p n)
    (hSelf : QuiddityCausingEsseIsSelfCausationReading p n) :
    DistinctEsseHasSomeCause p := by
  intro x hDistinct
  rcases hExhaustive x hDistinct with hQuiddity | ⟨c, _, hCause⟩
  · exact ⟨x, hSelf x hQuiddity⟩
  · exact ⟨c, hCause⟩

/-- From "caused" to "caused by another". For an actual x with esse other than
its essence, some c causes x's esse; c is not x, by no-self-causation; c is in
act as to being; so c witnesses the q.3 a.4 external cause of esse (distinct,
actual cause of being; the type does not fix that it is efficient). -/
theorem distinctEsseExternalFromCaused (p : Profile B P R)
    (hCaused : DistinctEsseHasSomeCause p)
    (hNoSelf : NothingCausesItsOwnBeing p.CausesIn p.esse)
    (hInAct : CauseOfBeingInActAsToBeing p.InAct p.CausesIn p.esse)
    (hBridge : OtherActualCauseOfBeingIsExternalEsseCause p) :
    DistinctEsseRequiresExternalCauseReading p := by
  intro x hDistinct
  obtain ⟨c, hCause⟩ := hCaused x hDistinct
  have hne : c ≠ x := fun h => hNoSelf x (h ▸ hCause)
  exact hBridge x c hne (hInAct c x hCause) hCause

/-- The literal De ente disjunction, instantiated at esse for a distinct-esse
being and passed through the efficiency bridge, gives the weak exhaustiveness. -/
theorem distinctEsseExhaustionFromDeEnte (p : Profile B P R) (n : NatureSource B R)
    (hGeneral : NatureOrExtrinsicSourceReading p n)
    (hEfficient : NatureSourcedDistinctEsseIsEfficient p n) :
    DistinctEsseNatureOrOtherCause p n := by
  intro x hDistinct
  rcases hGeneral x p.esse hDistinct.1 with hNature | hOther
  · exact Or.inl (hEfficient x hDistinct hNature)
  · exact Or.inr hOther

/-- The cause-sense bridge holds by the definition of `HasExternalEsseCause`. -/
theorem otherActualCauseOfBeingIsExternalEsseCause (p : Profile B P R) :
    OtherActualCauseOfBeingIsExternalEsseCause p :=
  fun _ c hne hAct hCause => ⟨c, hne, hAct, hCause⟩

/-- The six finite interpretations on `Bool`. Explicit proof terms; no
`propext` from `simp`. -/
theorem extrinsicSourceControls : ExtrinsicSourceControls := by
  refine ⟨?brute, ?formal, ?self, ?unrealized, ?nonactual, ?nonvacuity⟩
  · -- Brute esse: no causes, nothing from nature.
    let p : Profile Bool Bool Unit := {
      InAct := fun x _ => x = false
      CausesIn := fun _ _ _ => False
      essenceOf := fun _ => false
      esseOf := fun _ => true
      essentialPrinciplesAloneSufficeForEsse := fun _ => False
      esse := () }
    let n : NatureSource Bool Unit := {
      fromNature := fun _ _ => False
      quiddityEfficientlyCauses := fun _ _ => False }
    have hd : DistinctEsseAt p false := ⟨rfl, Bool.noConfusion⟩
    have hNoExt : ¬ HasExternalEsseCause p false := fun ⟨_, _, _, h⟩ => h
    exact ⟨p, n, hd, (fun _ h => h), (fun _ h => h), (fun _ _ h => h.elim),
      (fun _ _ h => h.elim),
      (fun h => (h false () rfl).elim (fun h => h) (fun ⟨_, _, h⟩ => h)),
      (fun h => (h false hd).elim (fun h => h) (fun ⟨_, _, h⟩ => h)),
      (fun h => let ⟨_, h⟩ := h false hd; h),
      (fun h => hNoExt (h false hd))⟩
  · -- Formal nature: esse from nature, not efficiently; no causes.
    let p : Profile Bool Bool Unit := {
      InAct := fun x _ => x = false
      CausesIn := fun _ _ _ => False
      essenceOf := fun _ => false
      esseOf := fun _ => true
      essentialPrinciplesAloneSufficeForEsse := fun _ => False
      esse := () }
    let n : NatureSource Bool Unit := {
      fromNature := fun _ _ => True
      quiddityEfficientlyCauses := fun _ _ => False }
    have hd : DistinctEsseAt p false := ⟨rfl, Bool.noConfusion⟩
    have hNoExt : ¬ HasExternalEsseCause p false := fun ⟨_, _, _, h⟩ => h
    exact ⟨p, n, hd, True.intro, (fun h => h),
      (fun _ _ _ => Or.inl True.intro), (fun _ h => h.elim), (fun _ h => h),
      (fun _ _ h => h.elim),
      (fun h => h false hd True.intro),
      (fun h => (h false hd).elim (fun h => h) (fun ⟨_, _, h⟩ => h)),
      (fun h => let ⟨_, h⟩ := h false hd; h),
      (fun h => hNoExt (h false hd))⟩
  · -- Self-cause: false causes its own esse through its quiddity.
    let p : Profile Bool Bool Unit := {
      InAct := fun x _ => x = false
      CausesIn := fun c x _ => c = false ∧ x = false
      essenceOf := fun _ => false
      esseOf := fun _ => true
      essentialPrinciplesAloneSufficeForEsse := fun _ => False
      esse := () }
    let n : NatureSource Bool Unit := {
      fromNature := fun x _ => x = false
      quiddityEfficientlyCauses := fun x _ => x = false }
    have hd : DistinctEsseAt p false := ⟨rfl, Bool.noConfusion⟩
    have hNoExt : ¬ HasExternalEsseCause p false :=
      fun ⟨_, hne, _, hc, _⟩ => hne hc
    exact ⟨p, n, hd,
      (fun x _ h => Or.inl h),
      (fun _ _ h => h),
      (fun x h => Or.inl h.1),
      (fun x h => ⟨false, rfl, h.1⟩),
      (fun x h => ⟨h, h⟩),
      (fun _ _ h => h.1),
      (fun h => h false ⟨rfl, rfl⟩),
      (fun h => hNoExt (h false hd))⟩
  · -- Unrealized quiddity: quiddity efficiently causes, thing does not.
    let p : Profile Bool Bool Unit := {
      InAct := fun x _ => x = false
      CausesIn := fun _ _ _ => False
      essenceOf := fun _ => false
      esseOf := fun _ => true
      essentialPrinciplesAloneSufficeForEsse := fun _ => False
      esse := () }
    let n : NatureSource Bool Unit := {
      fromNature := fun x _ => x = false
      quiddityEfficientlyCauses := fun x _ => x = false }
    have hd : DistinctEsseAt p false := ⟨rfl, Bool.noConfusion⟩
    have hNoExt : ¬ HasExternalEsseCause p false := fun ⟨_, _, _, h⟩ => h
    exact ⟨p, n, hd,
      (fun x _ h => Or.inl h),
      (fun _ _ h => h),
      (fun x h => Or.inl h.1),
      (fun h => let ⟨_, h⟩ := h false hd; h),
      (fun h => h false rfl),
      (fun _ h => h),
      (fun _ _ h => h.elim),
      (fun h => hNoExt (h false hd))⟩
  · -- Nonactual cause: true, not in act, causes false's esse.
    let p : Profile Bool Bool Unit := {
      InAct := fun x _ => x = false
      CausesIn := fun c x _ => c = true ∧ x = false
      essenceOf := fun _ => false
      esseOf := fun _ => true
      essentialPrinciplesAloneSufficeForEsse := fun _ => False
      esse := () }
    let n : NatureSource Bool Unit := {
      fromNature := fun _ _ => False
      quiddityEfficientlyCauses := fun _ _ => False }
    have hd : DistinctEsseAt p false := ⟨rfl, Bool.noConfusion⟩
    have hNoExt : ¬ HasExternalEsseCause p false := by
      intro ⟨y, _, hAct, hc, _⟩
      have hy : y = true := hc
      have hf : y = false := hAct
      exact Bool.noConfusion (hy.symm.trans hf)
    have hOther : ∀ x, p.InAct x () → ∃ c, c ≠ x ∧ p.CausesIn c x () := by
      intro x hx
      exact ⟨true, fun h => Bool.noConfusion (h.trans hx), rfl, hx⟩
    exact ⟨p, n, hd,
      (fun x _ hx => Or.inr (hOther x hx)),
      (fun _ _ h => h.elim),
      (fun x h => Or.inr (hOther x h.1)),
      (fun x h => ⟨true, rfl, h.1⟩),
      (fun _ h => h.elim),
      (fun x h => Bool.noConfusion (h.1.symm.trans h.2)),
      (fun h => Bool.noConfusion (h true false ⟨rfl, rfl⟩)),
      (fun h => hNoExt (h false hd))⟩
  · -- Nonvacuity: true, in act, causes false's esse.
    let p : Profile Bool Bool Unit := {
      InAct := fun _ _ => True
      CausesIn := fun c x _ => c = true ∧ x = false
      essenceOf := fun _ => false
      esseOf := Bool.not
      essentialPrinciplesAloneSufficeForEsse := fun _ => False
      esse := () }
    let n : NatureSource Bool Unit := {
      fromNature := fun x _ => x = true
      quiddityEfficientlyCauses := fun _ _ => False }
    have hd : DistinctEsseAt p false := ⟨True.intro, Bool.noConfusion⟩
    have hExt : HasExternalEsseCause p false :=
      ⟨true, Bool.noConfusion, True.intro, rfl, rfl⟩
    have hEff : NatureSourcedDistinctEsseIsEfficient p n := by
      intro x h hx
      have hx' : x = true := hx
      subst hx'
      exact (h.2 rfl).elim
    have hConcl : DistinctEsseRequiresExternalCauseReading p := by
      intro x h
      cases x with
      | false => exact hExt
      | true => exact (h.2 rfl).elim
    have hGen : NatureOrExtrinsicSourceReading p n := by
      intro x r _
      cases x with
      | true => exact Or.inl rfl
      | false => exact Or.inr ⟨true, Bool.noConfusion, rfl, rfl⟩
    exact ⟨p, n, hd, hGen, hEff,
      distinctEsseExhaustionFromDeEnte p n hGen hEff,
      distinctEsseCausedFromDeEnte p n (distinctEsseExhaustionFromDeEnte p n hGen hEff)
        (fun _ h => h.elim),
      (fun _ h => h.elim),
      (fun x h => Bool.noConfusion (h.1.symm.trans h.2)),
      (fun _ _ _ => True.intro),
      otherActualCauseOfBeingIsExternalEsseCause p,
      hExt, hConcl⟩

end TruthCore.Results.Aquinas.DeEnte.ExtrinsicSource
