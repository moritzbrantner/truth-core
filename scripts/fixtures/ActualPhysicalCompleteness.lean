import TruthCore.Logic.ActualPhysicalCompleteness
import TruthCore.Logic.KnowledgeAdmissibility

open TruthCore.Logic.ActualPhysicalCompleteness
open TruthCore.Logic.KnowledgeAdmissibility (AllPhysicalKnown)
open TruthCore.Logic.JustificationIntrospection (Knows)
open TruthCore.Modal (Frame)

-- Full arbitrary domains: coverage and represented knowledge transfer truth of
-- each relevant fact. Neither assumption certifies actual physics calibration.
example {W P Fact : Type} (physical : W → P) (holds : Fact → W → Prop)
    (relevant : Fact → Prop) (E : Frame W) (a : W)
    (coverage : Complete physical holds relevant)
    (known : AllPhysicalKnown E physical a) :
    ∀ f, relevant f → holds f a → Knows E (holds f) a := by
  intro f hr hf
  obtain ⟨represented, exactness⟩ := coverage f hr
  intro v hv
  exact (exactness v).mpr (known represented ((exactness a).mp hf) v hv)

-- Nonempty infinite candidate/fact domains, genuine relevant questions, coverage.
example : Complete (fun n : Nat => n)
    (fun f n : Nat => n = f) (fun _ => True) := by
  intro f _
  exact ⟨fun n => n = f, fun _ => Iff.rfl⟩

-- On the SAME full infinite domain, an impoverished projection knows all its
-- predicates while failing coverage of the independently specified facts.
example :
    AllPhysicalKnown (⟨fun _ _ : Nat => True⟩ : Frame Nat)
      (fun _ => ()) 0 ∧
    ¬ Complete (fun _ : Nat => ()) (fun f n : Nat => n = f) (fun _ => True) := by
  constructor
  · intro predicate hp _ _
    exact hp
  · intro coverage
    obtain ⟨represented, exactness⟩ := coverage 0 trivial
    have zero := (exactness 0).mp rfl
    have impossible : (1 : Nat) = 0 := (exactness 1).mpr zero
    cases impossible

-- Unrelated facts need not factor: relevance is explicit, not global-state scope.
example : Complete (fun _ : Nat => ())
    (fun f n : Nat => n = f) (fun _ => False) := by
  intro _ impossible
  exact False.elim impossible
