import TruthCore.Alternatives.MindPhysicalism

namespace TruthCore.Results.Comparison.MindPhysicalism

open TruthCore.Logic
open TruthCore.Modern.Papineau.RiseOfPhysicalism
open TruthCore.Latin.Aquinas.SummaTheologiae.HumanIntellect
open TruthCore.Alternatives.MindPhysicalism

/-- Under excluded middle and Papineau's three premises (premise 3 distributive),
the eliminative, reductive and nonreductive positions cover the target kind.
This does not choose among them, and it does not establish the premises. -/
theorem physicalistFork {Occurrence Kind : Type} (f : Frame Occurrence Kind)
    (hEM : ExcludedMiddle) (hComplete : CompletenessOfPhysicsReading f.Physical f.IsEffect f.Prior f.FullyDeterminedByLaw)
    (hInfluence : CausalInfluence f) (hEach : EachCauseNotAllOverdetermined f) :
    PhysicalistFork f := by
  sorry

/-- From excluded middle alone the three positions and `SomeUnbased` cover the
target kind. This partition has no causal content: the causal premises are what
remove its fourth member. -/
theorem fourWayCoverage {Occurrence Kind : Type} (f : Frame Occurrence Kind)
    (hEM : ExcludedMiddle) : PhysicalistFork f ∨ SomeUnbased f := by
  sorry

/-- The four positions are pairwise exclusive in every frame. -/
theorem positionsExclusive {Occurrence Kind : Type} (f : Frame Occurrence Kind) :
    ¬ (Eliminative f ∧ Reductive f) ∧ ¬ (Eliminative f ∧ Nonreductive f) ∧
    ¬ (Reductive f ∧ Nonreductive f) ∧ ¬ (Eliminative f ∧ SomeUnbased f) ∧
    ¬ (Reductive f ∧ SomeUnbased f) ∧ ¬ (Nonreductive f ∧ SomeUnbased f) := by
  sorry

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
  sorry

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
    (hBridge : PhysicalBasisIsBodySharing f a intellect tokenOf) : False := by
  sorry

/-- The collective reading of premise 3 yields only that some occurrence of the
target kind is physically based. `collectiveHybrid` shows that it does not yield
this of all of them. -/
theorem someBased {Occurrence Kind : Type} (f : Frame Occurrence Kind)
    (hEM : ExcludedMiddle) (hComplete : Completeness f)
    (hTogether : NotAllOverdeterminedTogether f) : SomeBased f := by
  sorry

/-- Eliminative branch: no occurrence of the target kind, with the background
holding vacuously on the mental side. -/
theorem eliminativeWitness :
    ∃ (Occurrence Kind : Type) (f : Frame Occurrence Kind),
      CausalBackground f ∧ Eliminative f := by
  sorry

/-- Reductive branch: the mental kind is itself physical and its occurrence causes
the effect. -/
theorem reductiveWitness :
    ∃ (Occurrence Kind : Type) (f : Frame Occurrence Kind),
      CausalBackground f ∧ Reductive f := by
  sorry

/-- Nonreductive branch by realization: the mental occurrence has no physical kind
and is realized by a physical occurrence, while the mental kind is not physical. -/
theorem realizationWitness :
    ∃ (Occurrence Kind : Type) (f : Frame Occurrence Kind),
      CausalBackground f ∧ Nonreductive f ∧ ∃ e, f.Mental e ∧ ¬ f.Physical e := by
  sorry

/-- Nonreductive branch by occurrence identity: the mental occurrence also has a
physical kind, while the mental kind is not physical. -/
theorem occurrenceIdentityWitness :
    ∃ (Occurrence Kind : Type) (f : Frame Occurrence Kind),
      CausalBackground f ∧ Nonreductive f ∧ ∀ e, f.Mental e → f.Physical e := by
  sorry

/-- Deletion control, interactionist shape: the candidate causes the effect and
nothing physical does, so only completeness fails. -/
theorem completenessExit :
    ∃ (Occurrence Kind Principle Operation : Type) (f : Frame Occurrence Kind)
      (a : OperationAttribution Principle Operation) (i : Principle)
      (tokenOf : Operation → Occurrence → Prop),
      ¬ Completeness f ∧ CausalInfluence f ∧ EachCauseNotAllOverdetermined f ∧
      ExerciseTokened f a i tokenOf ∧ PhysicalBasisIsBodySharing f a i tokenOf ∧
      PerSeIntellectualOperation a i ∧ SomeUnbased f ∧ ¬ PhysicalistFork f := by
  sorry

/-- Deletion control, epiphenomenal shape: the candidate has no physical effect,
so only causal influence fails. -/
theorem influenceExit :
    ∃ (Occurrence Kind Principle Operation : Type) (f : Frame Occurrence Kind)
      (a : OperationAttribution Principle Operation) (i : Principle)
      (tokenOf : Operation → Occurrence → Prop),
      Completeness f ∧ ¬ CausalInfluence f ∧ EachCauseNotAllOverdetermined f ∧
      ExerciseTokened f a i tokenOf ∧ PhysicalBasisIsBodySharing f a i tokenOf ∧
      PerSeIntellectualOperation a i ∧ SomeUnbased f ∧ ¬ PhysicalistFork f := by
  sorry

/-- Deletion control, overdetermination shape: candidate and base both cause the
effect, so only distributive premise 3 fails. -/
theorem overdeterminationExit :
    ∃ (Occurrence Kind Principle Operation : Type) (f : Frame Occurrence Kind)
      (a : OperationAttribution Principle Operation) (i : Principle)
      (tokenOf : Operation → Occurrence → Prop),
      Completeness f ∧ CausalInfluence f ∧ ¬ EachCauseNotAllOverdetermined f ∧
      ExerciseTokened f a i tokenOf ∧ PhysicalBasisIsBodySharing f a i tokenOf ∧
      PerSeIntellectualOperation a i ∧ SomeUnbased f ∧ ¬ PhysicalistFork f := by
  sorry

/-- Deletion control: an exercise with no token in the frame. The target kind is
physical and the causal background holds, while the exercise has no bodily sharing. -/
theorem tokeningExit :
    ∃ (Occurrence Kind Principle Operation : Type) (f : Frame Occurrence Kind)
      (a : OperationAttribution Principle Operation) (i : Principle)
      (tokenOf : Operation → Occurrence → Prop),
      CausalBackground f ∧ Reductive f ∧ ¬ ExerciseTokened f a i tokenOf ∧
      PhysicalBasisIsBodySharing f a i tokenOf ∧ PerSeIntellectualOperation a i := by
  sorry

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
  sorry

/-- The bundle of `noPerSeOperation` is jointly satisfiable, so the theorem is not
vacuous: every premise holds and the operation shares with the body. -/
theorem bundleWitness :
    ∃ (Occurrence Kind Principle Operation : Type) (f : Frame Occurrence Kind)
      (a : OperationAttribution Principle Operation) (i : Principle)
      (tokenOf : Operation → Occurrence → Prop),
      CausalBackground f ∧ Reductive f ∧ ExerciseTokened f a i tokenOf ∧
      PhysicalBasisIsBodySharing f a i tokenOf ∧ NoPerSeIntellectualOperation a i := by
  sorry

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
  sorry

end TruthCore.Results.Comparison.MindPhysicalism
