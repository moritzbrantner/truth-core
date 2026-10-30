import TruthCore.Alternatives.MindPhysicalism
import TruthCore.Results.Aquinas.SummaTheologiae.HumanIntellectSubsistence.Solution

/-!
Solutions for the fork and core of `TruthCore.Alternatives.MindPhysicalism`.
All controls are finite formal interpretations. See
`docs/notes/mind-physicalism-fork-419.md`.
-/

namespace TruthCore.Results.Comparison.MindPhysicalism

open TruthCore.Logic
open TruthCore.Modern.Papineau.RiseOfPhysicalism
open TruthCore.Latin.Aquinas.SummaTheologiae.HumanIntellect
open TruthCore.Results.Aquinas.SummaTheologiae
open TruthCore.Alternatives.MindPhysicalism

/-- A cause that does not overdetermine a fully determined effect is among, or
realized by, the effect's prior physical occurrences. -/
theorem based_of_not_overdetermines {Occurrence Kind : Type}
    (hEM : ExcludedMiddle) (f : Frame Occurrence Kind) (c x : Occurrence)
    (hComplete : Completeness f) (hEffect : f.PhysicalEffectOf c x)
    (hNot : ¬ f.Overdetermines c x) : PhysicallyBased f c := by
  have hDetermined : f.FullyDeterminedByLaw (f.PriorPhysical x) x :=
    hComplete x hEffect.1 hEffect.2.1
  cases hEM (f.AmongOrRealizedBy (f.PriorPhysical x) c) with
  | inl hBased =>
    cases hBased with
    | inl hAmong => exact Or.inl hAmong.1
    | inr hRealized =>
      obtain ⟨r, hr, hReal⟩ := hRealized
      exact Or.inr ⟨r, hr.1, hReal⟩
  | inr hNotBased => exact (hNot ⟨hEffect.2.2, hDetermined, hNotBased⟩).elim

/-- The three causal premises make every occurrence of the target kind physically
based. -/
theorem allBased {Occurrence Kind : Type}
    (hEM : ExcludedMiddle) (f : Frame Occurrence Kind)
    (hComplete : Completeness f) (hInfluence : CausalInfluence f)
    (hEach : EachCauseNotAllOverdetermined f) (c : Occurrence) (hMental : f.Mental c) :
    PhysicallyBased f c := by
  have hSome := hInfluence c hMental
  cases hEM (∃ x, f.PhysicalEffectOf c x ∧ ¬ f.Overdetermines c x) with
  | inl hExists =>
    obtain ⟨x, hEffect, hNot⟩ := hExists
    exact based_of_not_overdetermines hEM f c x hComplete hEffect hNot
  | inr hNone =>
    refine (hEach c hMental hSome (fun x hEffect => ?_)).elim
    cases hEM (f.Overdetermines c x) with
    | inl hOver => exact hOver
    | inr hNot => exact (hNone ⟨x, hEffect, hNot⟩).elim

/-- Under excluded middle and Papineau's three premises (premise 3 distributive),
the eliminative, reductive and nonreductive positions cover the target kind.
This does not choose among them, and it does not establish the premises. -/
theorem physicalistFork {Occurrence Kind : Type} (f : Frame Occurrence Kind)
    (hEM : ExcludedMiddle) (hComplete : CompletenessOfPhysicsReading f.Physical f.IsEffect f.Prior f.FullyDeterminedByLaw)
    (hInfluence : CausalInfluence f) (hEach : EachCauseNotAllOverdetermined f) :
    PhysicalistFork f := by
  cases hEM (∃ e, f.Mental e) with
  | inr hNone => exact Or.inl (fun e he => hNone ⟨e, he⟩)
  | inl hSome =>
    cases hEM (f.PhysicalKind f.mental) with
    | inl hKind => exact Or.inr (Or.inl ⟨hSome, hKind⟩)
    | inr hNotKind =>
      exact Or.inr (Or.inr ⟨hSome, hNotKind, allBased hEM f hComplete hInfluence hEach⟩)

/-- From excluded middle alone the three positions and `SomeUnbased` cover the
target kind. This partition has no causal content: the causal premises are what
remove its fourth member. -/
theorem fourWayCoverage {Occurrence Kind : Type} (f : Frame Occurrence Kind)
    (hEM : ExcludedMiddle) : PhysicalistFork f ∨ SomeUnbased f := by
  cases hEM (SomeUnbased f) with
  | inl hUnbased => exact Or.inr hUnbased
  | inr hNotUnbased =>
    refine Or.inl ?_
    cases hEM (∃ e, f.Mental e) with
    | inr hNone => exact Or.inl (fun e he => hNone ⟨e, he⟩)
    | inl hSome =>
      cases hEM (f.PhysicalKind f.mental) with
      | inl hKind => exact Or.inr (Or.inl ⟨hSome, hKind⟩)
      | inr hNotKind =>
        refine Or.inr (Or.inr ⟨hSome, hNotKind, fun e he => ?_⟩)
        cases hEM (PhysicallyBased f e) with
        | inl hBased => exact hBased
        | inr hNot => exact (hNotUnbased ⟨e, he, hNot⟩).elim

/-- The four positions are pairwise exclusive in every frame. -/
theorem positionsExclusive {Occurrence Kind : Type} (f : Frame Occurrence Kind) :
    ¬ (Eliminative f ∧ Reductive f) ∧ ¬ (Eliminative f ∧ Nonreductive f) ∧
    ¬ (Reductive f ∧ Nonreductive f) ∧ ¬ (Eliminative f ∧ SomeUnbased f) ∧
    ¬ (Reductive f ∧ SomeUnbased f) ∧ ¬ (Nonreductive f ∧ SomeUnbased f) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨hE, ⟨e, he⟩, _⟩; exact hE e he
  · rintro ⟨hE, ⟨e, he⟩, _⟩; exact hE e he
  · rintro ⟨⟨_, hK⟩, _, hNot, _⟩; exact hNot hK
  · rintro ⟨hE, e, he, _⟩; exact hE e he
  · rintro ⟨⟨_, hK⟩, e, he, hNot⟩; exact hNot (Or.inl ⟨_, hK, he⟩)
  · rintro ⟨⟨_, _, hAll⟩, e, he, hNot⟩; exact hNot (hAll e he)

/-- With the two open q.75 bridges, Papineau's three premises exclude a per-se
intellectual operation. So whoever keeps such an operation must reject excluded
middle, completeness, causal influence, distributive premise 3, tokening or the
basis/sharing bridge; the theorem does not say which. -/
theorem noPerSeOperation {Occurrence Kind Principle Operation : Type}
    (f : Frame Occurrence Kind) (a : OperationAttribution Principle Operation)
    (intellect : Principle) (tokenOf : Operation → Occurrence → Prop)
    (hEM : ExcludedMiddle) (hComplete : CompletenessOfPhysicsReading f.Physical f.IsEffect f.Prior f.FullyDeterminedByLaw)
    (hInfluence : CausalInfluence f) (hEach : EachCauseNotAllOverdetermined f)
    (hTokened : ExerciseTokened f a intellect tokenOf)
    (hBridge : PhysicalBasisIsBodySharing f a intellect tokenOf) :
    NoPerSeIntellectualOperation a intellect := by
  rintro ⟨op, hExercise, hNoShare⟩
  obtain ⟨e, hToken, hMental⟩ := hTokened op hExercise
  exact hNoShare (hBridge op e hExercise hToken hMental
    (allBased hEM f hComplete hInfluence hEach e hMental))

/-- Composition with the existing q.75 reductios: the five q.75 premises that
yield a per-se operation, the three causal premises and the two bridges cannot
all hold. This is a dilemma among eleven commitments with excluded middle, not a
refutation of any one of them. -/
theorem q75BundleIncompatible {Occurrence Kind Principle Nature Operation : Type}
    (m : Model Principle Nature) (through : Principle → Principle → Prop)
    (f : Frame Occurrence Kind) (a : OperationAttribution Principle Operation)
    (intellect : Principle) (tokenOf : Operation → Occurrence → Prop)
    (hScope : UniversalBodilyCognition m intellect)
    (hBodies : BodilyDeterminacy m)
    (hIntrinsic : NaturalBodilyInterference m intellect)
    (hOrgan : OrganBodilyInterference m through intellect)
    (hAttribution : NonorganicOperationAttribution m through a intellect)
    (hEM : ExcludedMiddle) (hComplete : Completeness f)
    (hInfluence : CausalInfluence f) (hEach : EachCauseNotAllOverdetermined f)
    (hTokened : ExerciseTokened f a intellect tokenOf)
    (hBridge : PhysicalBasisIsBodySharing f a intellect tokenOf) : False :=
  noPerSeOperation f a intellect tokenOf hEM hComplete hInfluence hEach hTokened hBridge
    (hAttribution
      (HumanIntellectIncorporeal.intellectIsNotBody m intellect hScope hBodies hIntrinsic)
      (HumanIntellectNonorganic.intellectUsesNoBodilyOrgan m through intellect
        hScope hBodies hOrgan))

/-- The collective reading of premise 3 yields only that some occurrence of the
target kind is physically based. `collectiveHybrid` shows that it does not yield
this of all of them. -/
theorem someBased {Occurrence Kind : Type} (f : Frame Occurrence Kind)
    (hEM : ExcludedMiddle) (hComplete : Completeness f)
    (hTogether : NotAllOverdeterminedTogether f) : SomeBased f := by
  cases hEM (SomeBased f) with
  | inl h => exact h
  | inr hNone =>
    refine (hTogether (fun c x hMental hEffect => ?_)).elim
    cases hEM (f.Overdetermines c x) with
    | inl hOver => exact hOver
    | inr hNot =>
      exact (hNone ⟨c, hMental,
        based_of_not_overdetermines hEM f c x hComplete hEffect hNot⟩).elim

/-! ### Finite interpretations -/

/-- Three points: a candidate occurrence, a base occurrence and an effect. -/
inductive Point where
  | candidate | base | effect

open Point

/-- Candidate and base may have the mental kind (`true`); base and effect have
the kind `false`, which is physical. The propositional parameters decide the
rest: whether candidate and base are mental, whether the mental kind is physical,
whether candidate and base cause the effect, and whether base realizes candidate.
`FullyDeterminedByLaw S x` is read in these models as: something in `S` causes
`x`. -/
def pointFrame (candMental baseMental kindPhysical candCauses baseCauses realized : Prop) :
    Frame Point Bool where
  Has
    | candidate, true => candMental
    | base, true => baseMental
    | candidate, false => False
    | base, false => True
    | effect, true => False
    | effect, false => True
  PhysicalKind
    | true => kindPhysical
    | false => True
  mental := true
  IsEffect
    | effect => True
    | _ => False
  Prior
    | candidate, effect => True
    | base, effect => True
    | _, _ => False
  FullyDeterminedByLaw := fun S x =>
    match x with
    | effect => (S candidate ∧ candCauses) ∨ (S base ∧ baseCauses)
    | _ => False
  Causes
    | candidate, effect => candCauses
    | base, effect => baseCauses
    | _, _ => False
  RealizedBy
    | candidate, base => realized
    | _, _ => False

/-- The base occurrence is physical. -/
theorem basePhysical (a b c d e g : Prop) : (pointFrame a b c d e g).Physical base :=
  ⟨false, trivial, trivial⟩

/-- The effect occurrence is physical. -/
theorem effectPhysical (a b c d e g : Prop) : (pointFrame a b c d e g).Physical effect :=
  ⟨false, trivial, trivial⟩

/-- With the mental kind not physical, the candidate has no physical kind. -/
theorem candidateNotPhysical (a b d e g : Prop) :
    ¬ (pointFrame a b False d e g).Physical candidate := by
  rintro ⟨k, hk, h⟩
  cases k with
  | true => exact hk
  | false => exact h

/-- A candidate with no realizer and no physical kind is not physically based. -/
theorem candidateUnbased (a b d e : Prop) :
    ¬ PhysicallyBased (pointFrame a b False d e False) candidate := by
  rintro (h | ⟨r, _, hr⟩)
  · exact candidateNotPhysical _ _ _ _ _ h
  · cases r <;> exact hr

/-- If the base causes the effect, completeness holds. -/
theorem completeOfBase (a b c d g : Prop) : Completeness (pointFrame a b c d True g) := by
  intro x _ hEffect
  cases x with
  | effect => exact Or.inr ⟨⟨basePhysical _ _ _ _ _ _, trivial⟩, trivial⟩
  | candidate => exact hEffect.elim
  | base => exact hEffect.elim

/-- Only the effect is an effect. -/
theorem effectOf {a b c d e g : Prop} {o x : Point}
    (h : (pointFrame a b c d e g).PhysicalEffectOf o x) : x = effect := by
  cases x with
  | effect => rfl
  | candidate => exact h.2.1.elim
  | base => exact h.2.1.elim

/-- In a frame where the base is the mental occurrence's determiner, the base does
not overdetermine the effect. -/
theorem baseNotOver (a b c d e g : Prop) :
    ¬ (pointFrame a b c d e g).Overdetermines base effect :=
  fun h => h.2.2 (Or.inl ⟨basePhysical _ _ _ _ _ _, trivial⟩)

/-- The base has the effect as a physical effect when it causes it. -/
theorem baseEffect (a b c d g : Prop) :
    (pointFrame a b c d True g).PhysicalEffectOf base effect :=
  ⟨effectPhysical _ _ _ _ _ _, trivial, trivial⟩

/-- The candidate has the effect as a physical effect when it causes it. -/
theorem candidateEffect (a b c e g : Prop) :
    (pointFrame a b c True e g).PhysicalEffectOf candidate effect :=
  ⟨effectPhysical _ _ _ _ _ _, trivial, trivial⟩

/-- Eliminative branch: no occurrence of the target kind, with the background
holding vacuously on the mental side. -/
theorem eliminativeWitness :
    ∃ (Occurrence Kind : Type) (f : Frame Occurrence Kind),
      CausalBackground f ∧ Eliminative f := by
  refine ⟨Point, Bool, pointFrame False False False False True False, ?_⟩
  have hNo : Eliminative (pointFrame False False False False True False) := by
    intro e he
    cases e with
    | candidate => exact he
    | base => exact he
    | effect => exact he
  exact ⟨⟨completeOfBase _ _ _ _ _, fun c hc => (hNo c hc).elim,
    fun c hc => (hNo c hc).elim⟩, hNo⟩

/-- The reductive frame satisfies the causal background. -/
theorem reductiveBackground :
    CausalBackground (pointFrame True False True True True False) := by
  refine ⟨completeOfBase _ _ _ _ _, ?_, ?_⟩
  · intro c hc
    cases c with
    | candidate => exact ⟨effect, candidateEffect _ _ _ _ _⟩
    | base => exact hc.elim
    | effect => exact hc.elim
  · intro c hc _ hAll
    cases c with
    | candidate =>
      exact (hAll effect (candidateEffect _ _ _ _ _)).2.2
        (Or.inl ⟨⟨true, trivial, trivial⟩, trivial⟩)
    | base => exact hc
    | effect => exact hc

/-- Reductive branch: the mental kind is itself physical and its occurrence causes
the effect. -/
theorem reductiveWitness :
    ∃ (Occurrence Kind : Type) (f : Frame Occurrence Kind),
      CausalBackground f ∧ Reductive f := by
  exact ⟨Point, Bool, pointFrame True False True True True False, reductiveBackground,
    ⟨candidate, trivial⟩, trivial⟩

/-- Nonreductive branch by realization: the mental occurrence has no physical kind
and is realized by a physical occurrence, while the mental kind is not physical. -/
theorem realizationWitness :
    ∃ (Occurrence Kind : Type) (f : Frame Occurrence Kind),
      CausalBackground f ∧ Nonreductive f ∧ ∃ e, f.Mental e ∧ ¬ f.Physical e := by
  let f := pointFrame True False False True True True
  refine ⟨Point, Bool, f, ⟨completeOfBase _ _ _ _ _, ?_, ?_⟩,
    ⟨⟨candidate, trivial⟩, id, ?_⟩, candidate, trivial, candidateNotPhysical _ _ _ _ _⟩
  · intro c hc
    cases c with
    | candidate => exact ⟨effect, candidateEffect _ _ _ _ _⟩
    | base => exact hc.elim
    | effect => exact hc.elim
  · intro c hc _ hAll
    cases c with
    | candidate =>
      exact (hAll effect (candidateEffect _ _ _ _ _)).2.2
        (Or.inr ⟨base, ⟨basePhysical _ _ _ _ _ _, trivial⟩, trivial⟩)
    | base => exact hc
    | effect => exact hc
  · intro e he
    cases e with
    | candidate => exact Or.inr ⟨base, basePhysical _ _ _ _ _ _, trivial⟩
    | base => exact he.elim
    | effect => exact he.elim

/-- Nonreductive branch by occurrence identity: the mental occurrence also has a
physical kind, while the mental kind is not physical. -/
theorem occurrenceIdentityWitness :
    ∃ (Occurrence Kind : Type) (f : Frame Occurrence Kind),
      CausalBackground f ∧ Nonreductive f ∧ ∀ e, f.Mental e → f.Physical e := by
  let f := pointFrame False True False False True False
  have hAll : ∀ e, f.Mental e → f.Physical e := by
    intro e he
    cases e with
    | candidate => exact he.elim
    | base => exact basePhysical _ _ _ _ _ _
    | effect => exact he.elim
  refine ⟨Point, Bool, f, ⟨completeOfBase _ _ _ _ _, ?_, ?_⟩,
    ⟨⟨base, trivial⟩, id, fun e he => Or.inl (hAll e he)⟩, hAll⟩
  · intro c hc
    cases c with
    | candidate => exact hc.elim
    | base => exact ⟨effect, baseEffect _ _ _ _ _⟩
    | effect => exact hc.elim
  · intro c hc _ hAll'
    cases c with
    | candidate => exact hc.elim
    | base => exact baseNotOver _ _ _ _ _ _ (hAll' effect (baseEffect _ _ _ _ _))
    | effect => exact hc.elim

/-- One operation, always exercised, with the candidate as its only token. -/
def pointAttribution (shares : Prop) : OperationAttribution Unit Unit :=
  ⟨fun _ _ => True, fun _ => shares, fun _ => False, fun _ => False⟩

/-- The candidate as the token of the operation. -/
def candidateToken : Unit → Point → Prop
  | _, candidate => True
  | _, _ => False

/-- The operation with no sharing is a per-se operation. -/
theorem pointPerSe : PerSeIntellectualOperation (pointAttribution False) () :=
  ⟨(), trivial, id⟩

/-- A mental candidate tokens the operation. -/
theorem pointTokened (b c d e g : Prop) :
    ExerciseTokened (pointFrame True b c d e g) (pointAttribution False) () candidateToken :=
  fun _ _ => ⟨candidate, trivial, trivial⟩

/-- With an unbased candidate as sole token, the bridge holds vacuously. -/
theorem pointBridge (b d e : Prop) :
    PhysicalBasisIsBodySharing (pointFrame True b False d e False)
      (pointAttribution False) () candidateToken := by
  intro _ e' _ hToken _ hBased
  cases e' with
  | candidate => exact candidateUnbased _ _ _ _ hBased
  | base => exact hToken.elim
  | effect => exact hToken.elim

/-- With the candidate unbased, the three-member fork fails. -/
theorem forkFailsOfUnbased {Occurrence Kind : Type} (f : Frame Occurrence Kind)
    (h : SomeUnbased f) : ¬ PhysicalistFork f := by
  obtain ⟨e, he, hNot⟩ := h
  rintro (hE | ⟨_, hK⟩ | ⟨_, _, hAll⟩)
  · exact hE e he
  · exact hNot (Or.inl ⟨_, hK, he⟩)
  · exact hNot (hAll e he)

/-- Deletion control, interactionist shape: the candidate causes the effect and
nothing physical does, so only completeness fails. -/
theorem completenessExit :
    ∃ (Occurrence Kind Principle Operation : Type) (f : Frame Occurrence Kind)
      (a : OperationAttribution Principle Operation) (i : Principle)
      (tokenOf : Operation → Occurrence → Prop),
      ¬ Completeness f ∧ CausalInfluence f ∧ EachCauseNotAllOverdetermined f ∧
      ExerciseTokened f a i tokenOf ∧ PhysicalBasisIsBodySharing f a i tokenOf ∧
      PerSeIntellectualOperation a i ∧ SomeUnbased f ∧ ¬ PhysicalistFork f := by
  let f := pointFrame True False False True False False
  have hUnbased : SomeUnbased f := ⟨candidate, trivial, candidateUnbased _ _ _ _⟩
  refine ⟨Point, Bool, Unit, Unit, f, pointAttribution False, (), candidateToken,
    ?_, ?_, ?_, pointTokened _ _ _ _ _, pointBridge _ _ _, pointPerSe, hUnbased,
    forkFailsOfUnbased f hUnbased⟩
  · intro h
    rcases h effect (effectPhysical _ _ _ _ _ _) trivial with h | h
    · exact candidateNotPhysical _ _ _ _ _ h.1.1
    · exact h.2
  · intro c hc
    cases c with
    | candidate => exact ⟨effect, candidateEffect _ _ _ _ _⟩
    | base => exact hc.elim
    | effect => exact hc.elim
  · intro c hc _ hAll
    cases c with
    | candidate =>
      rcases (hAll effect (candidateEffect _ _ _ _ _)).2.1 with h | h
      · exact candidateNotPhysical _ _ _ _ _ h.1.1
      · exact h.2
    | base => exact hc
    | effect => exact hc

/-- Deletion control, epiphenomenal shape: the candidate has no physical effect,
so only causal influence fails. -/
theorem influenceExit :
    ∃ (Occurrence Kind Principle Operation : Type) (f : Frame Occurrence Kind)
      (a : OperationAttribution Principle Operation) (i : Principle)
      (tokenOf : Operation → Occurrence → Prop),
      Completeness f ∧ ¬ CausalInfluence f ∧ EachCauseNotAllOverdetermined f ∧
      ExerciseTokened f a i tokenOf ∧ PhysicalBasisIsBodySharing f a i tokenOf ∧
      PerSeIntellectualOperation a i ∧ SomeUnbased f ∧ ¬ PhysicalistFork f := by
  let f := pointFrame True False False False True False
  have hUnbased : SomeUnbased f := ⟨candidate, trivial, candidateUnbased _ _ _ _⟩
  have hNoEffect : ¬ ∃ x, f.PhysicalEffectOf candidate x := by
    rintro ⟨x, hx⟩
    cases effectOf hx
    exact hx.2.2
  refine ⟨Point, Bool, Unit, Unit, f, pointAttribution False, (), candidateToken,
    completeOfBase _ _ _ _ _, fun h => hNoEffect (h candidate trivial), ?_,
    pointTokened _ _ _ _ _, pointBridge _ _ _, pointPerSe, hUnbased,
    forkFailsOfUnbased f hUnbased⟩
  intro c hc hSome
  cases c with
  | candidate => exact (hNoEffect hSome).elim
  | base => exact hc.elim
  | effect => exact hc.elim

/-- The candidate overdetermines the effect when both it and the base cause it. -/
theorem candidateOverdetermines :
    (pointFrame True False False True True False).Overdetermines candidate effect := by
  refine ⟨trivial, Or.inr ⟨⟨basePhysical _ _ _ _ _ _, trivial⟩, trivial⟩, ?_⟩
  rintro (h | ⟨r, _, hr⟩)
  · exact candidateNotPhysical _ _ _ _ _ h.1
  · cases r <;> exact hr

/-- Deletion control, overdetermination shape: candidate and base both cause the
effect, so only distributive premise 3 fails. -/
theorem overdeterminationExit :
    ∃ (Occurrence Kind Principle Operation : Type) (f : Frame Occurrence Kind)
      (a : OperationAttribution Principle Operation) (i : Principle)
      (tokenOf : Operation → Occurrence → Prop),
      Completeness f ∧ CausalInfluence f ∧ ¬ EachCauseNotAllOverdetermined f ∧
      ExerciseTokened f a i tokenOf ∧ PhysicalBasisIsBodySharing f a i tokenOf ∧
      PerSeIntellectualOperation a i ∧ SomeUnbased f ∧ ¬ PhysicalistFork f := by
  let f := pointFrame True False False True True False
  have hUnbased : SomeUnbased f := ⟨candidate, trivial, candidateUnbased _ _ _ _⟩
  refine ⟨Point, Bool, Unit, Unit, f, pointAttribution False, (), candidateToken,
    completeOfBase _ _ _ _ _, ?_, ?_, pointTokened _ _ _ _ _, pointBridge _ _ _, pointPerSe,
    hUnbased, forkFailsOfUnbased f hUnbased⟩
  · intro c hc
    cases c with
    | candidate => exact ⟨effect, candidateEffect _ _ _ _ _⟩
    | base => exact hc.elim
    | effect => exact hc.elim
  · intro h
    refine h candidate trivial ⟨effect, candidateEffect _ _ _ _ _⟩ (fun x hx => ?_)
    cases effectOf hx
    exact candidateOverdetermines

/-- Deletion control: an exercise with no token in the frame. The target kind is
physical and the causal background holds, while the exercise has no bodily sharing. -/
theorem tokeningExit :
    ∃ (Occurrence Kind Principle Operation : Type) (f : Frame Occurrence Kind)
      (a : OperationAttribution Principle Operation) (i : Principle)
      (tokenOf : Operation → Occurrence → Prop),
      CausalBackground f ∧ Reductive f ∧ ¬ ExerciseTokened f a i tokenOf ∧
      PhysicalBasisIsBodySharing f a i tokenOf ∧ PerSeIntellectualOperation a i := by
  refine ⟨Point, Bool, Unit, Unit, pointFrame True False True True True False,
    pointAttribution False, (), (fun _ _ => False), reductiveBackground,
    ⟨⟨candidate, trivial⟩, trivial⟩, ?_, ?_, pointPerSe⟩
  · intro h
    obtain ⟨_, hToken, _⟩ := h () trivial
    exact hToken
  · intro _ _ _ hToken
    exact hToken.elim

/-- The central deletion control. Reductive position, causal background and
tokening hold together with a per-se operation, and only the bridge fails: unless
physical basis is bodily sharing, these do not exclude a per-se operation. This
is a formal non-entailment, not a defense of any reading of `BodyShares`. -/
theorem bridgeExit :
    ∃ (Occurrence Kind Principle Operation : Type) (f : Frame Occurrence Kind)
      (a : OperationAttribution Principle Operation) (i : Principle)
      (tokenOf : Operation → Occurrence → Prop),
      CausalBackground f ∧ Reductive f ∧ ExerciseTokened f a i tokenOf ∧
      ¬ PhysicalBasisIsBodySharing f a i tokenOf ∧ PerSeIntellectualOperation a i := by
  refine ⟨Point, Bool, Unit, Unit, pointFrame True False True True True False,
    pointAttribution False, (), candidateToken, reductiveBackground,
    ⟨⟨candidate, trivial⟩, trivial⟩, pointTokened _ _ _ _ _, ?_, pointPerSe⟩
  intro h
  exact h () candidate trivial trivial trivial (Or.inl ⟨true, trivial, trivial⟩)

/-- The bundle of `noPerSeOperation` is jointly satisfiable, so the theorem is not
vacuous: every premise holds and the operation shares with the body. -/
theorem bundleWitness :
    ∃ (Occurrence Kind Principle Operation : Type) (f : Frame Occurrence Kind)
      (a : OperationAttribution Principle Operation) (i : Principle)
      (tokenOf : Operation → Occurrence → Prop),
      CausalBackground f ∧ Reductive f ∧ ExerciseTokened f a i tokenOf ∧
      PhysicalBasisIsBodySharing f a i tokenOf ∧ NoPerSeIntellectualOperation a i := by
  refine ⟨Point, Bool, Unit, Unit, pointFrame True False True True True False,
    pointAttribution True, (), candidateToken, reductiveBackground,
    ⟨⟨candidate, trivial⟩, trivial⟩, ?_, ?_, ?_⟩
  · exact fun _ _ => ⟨candidate, trivial, trivial⟩
  · exact fun _ _ _ _ _ _ => trivial
  · rintro ⟨_, _, hNot⟩
    exact hNot trivial

/-- Hybrid control for the collective reading of premise 3. The base is a mental
occurrence with a physical kind and does not overdetermine; the candidate is a
mental occurrence with no physical basis and does. Completeness, causal influence,
the collective reading, tokening, the bridge and a per-se operation all hold, the
distributive reading fails, and some occurrence is unbased. So the collective
reading does not deliver a conclusion about every mental occurrence, nor about
one designated by a token. -/
theorem collectiveHybrid :
    ∃ (Occurrence Kind Principle Operation : Type) (f : Frame Occurrence Kind)
      (a : OperationAttribution Principle Operation) (i : Principle)
      (tokenOf : Operation → Occurrence → Prop),
      Completeness f ∧ CausalInfluence f ∧ NotAllOverdeterminedTogether f ∧
      ¬ EachCauseNotAllOverdetermined f ∧ ExerciseTokened f a i tokenOf ∧
      PhysicalBasisIsBodySharing f a i tokenOf ∧ PerSeIntellectualOperation a i ∧
      SomeBased f ∧ SomeUnbased f := by
  let f := pointFrame True True False True True False
  have hOver : f.Overdetermines candidate effect := by
    refine ⟨trivial, Or.inr ⟨⟨basePhysical _ _ _ _ _ _, trivial⟩, trivial⟩, ?_⟩
    rintro (h | ⟨r, _, hr⟩)
    · exact candidateNotPhysical _ _ _ _ _ h.1
    · cases r <;> exact hr
  refine ⟨Point, Bool, Unit, Unit, f, pointAttribution False, (), candidateToken,
    completeOfBase _ _ _ _ _, ?_, ?_, ?_, pointTokened _ _ _ _ _, pointBridge _ _ _,
    pointPerSe, ⟨base, trivial, Or.inl (basePhysical _ _ _ _ _ _)⟩,
    ⟨candidate, trivial, candidateUnbased _ _ _ _⟩⟩
  · intro c hc
    cases c with
    | candidate => exact ⟨effect, candidateEffect _ _ _ _ _⟩
    | base => exact ⟨effect, baseEffect _ _ _ _ _⟩
    | effect => exact hc.elim
  · intro h
    exact baseNotOver _ _ _ _ _ _ (h base effect trivial (baseEffect _ _ _ _ _))
  · intro h
    refine h candidate trivial ⟨effect, candidateEffect _ _ _ _ _⟩ (fun x hx => ?_)
    cases effectOf hx
    exact hOver

end TruthCore.Results.Comparison.MindPhysicalism
