import TruthCore.Causality.UnderivedEssenceEsse

/-! Selected-world restrictions of the existing support vocabulary. These are
open structural hypotheses, with no new historical attribution. -/
namespace TruthCore.Causality.ActualUnderivedEssenceEsse
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4

/-- Only existing supporters at this selected world are constrained. -/
def ActualNoContingent (m : Ontic W B) (R : W → B → B → Prop) (w : W) : Prop :=
  ∀ c n, m.ExistsAt w c → NecessaryAt m w n → R w c n → NecessaryAt m w c

/-- Actual support restricted to necessary bearers, not all actual beings. -/
def ActualNecessarySupport (m : Ontic W B) (R : W → B → B → Prop)
    (w : W) (c n : B) : Prop :=
  NecessaryAt m w c ∧ NecessaryAt m w n ∧ PresentEsseSupport m R w c n

def ActualNecessaryWellFounded (m : Ontic W B) (R : W → B → B → Prop)
    (w : W) : Prop := WellFounded (ActualNecessarySupport m R w)

/-- One same actually present necessary bearer has no incoming actual support
and represented essence–esse identity. Support elsewhere is unrestricted. -/
def ActualUnderivedEssenceIdentity (m : Ontic W B) (R : W → B → B → Prop)
    (w : W) (p : Profile B P A) : Prop :=
  ∃ n, m.ExistsAt w n ∧ NecessaryAt m w n ∧
    NoExistingSupportAt m R w n ∧ p.esseOf n = p.essenceOf n
end TruthCore.Causality.ActualUnderivedEssenceEsse
