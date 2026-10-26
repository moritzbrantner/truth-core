import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaOrder
namespace TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionCauseMoreSuch
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Three beings: the primary `p`, a secondary cause `a` and its effect `b`. -/
inductive B where
  | p
  | a
  | b
  deriving DecidableEq

/-- Degrees of approach to `p`: `a` least, `b` nearer, `p` itself highest. -/
def near : B → ℕ
  | .p => 2
  | .b => 1
  | .a => 0

/-- `p` causes being in both others; `a` also causes being in `b`. -/
def causes : B → B → Unit → Prop
  | .p, .a, _ => True
  | .p, .b, _ => True
  | .a, .b, _ => True
  | _, _, _ => False

/-- On the reading by attribution, *Metaphysics* II.1 holds for the primary and
not in general. With strict primacy the primary is more `r` than anything else,
so than whatever it causes `r` in. But in a three-being model (`p` nearest, then
`b`, then `a`) where `p` causes being in both others (both creatures) and `a`
also causes being in `b`, the order by approach, strict primacy, the causal
order of creatures to the primary, everything else being a creature and the
broad genus principle all hold, while `a` causes being in `b` without being
more a being. -/
theorem attributionOrderRestrictsCauseMoreSuch :
    AttributionOrderRestrictsCauseMoreSuch := by
  refine ⟨?_, ?_⟩
  · -- INF-QUARTA-VIA-ATTRIBUTION-RESTRICTS-CAUSE-MORE-SUCH (1): the primary exceeds all others
    intro Being Respect Degree _ InAct MoreIn CausesIn r near p hApproach hStrict x hx _
    exact (hApproach.2 p x).2 (hStrict x hx)
  · -- INF-QUARTA-VIA-ATTRIBUTION-RESTRICTS-CAUSE-MORE-SUCH (2): countermodel
    intro h
    have hApproach : ApproachToPrimaryReading (fun (_ : B) (_ : Unit) => True)
        (fun _ x y => near y < near x) () near B.p :=
      ⟨trivial, fun _ _ => Iff.rfl⟩
    have hStrict : StrictPrimacyReading near B.p := fun x hx => by
      cases x with
      | p => exact absurd rfl hx
      | a => decide
      | b => decide
    have hCreatures : OthersAreCreaturesReading (fun x => x ≠ B.p) B.p :=
      fun _ hx => hx
    have hOrdered : OrderedToPrimaryAsCauseReading (fun (_ : B) (_ : Unit) => True)
        causes (fun x => x ≠ B.p) () B.p := by
      intro x hx _
      cases x with
      | p => exact absurd rfl hx
      | a => trivial
      | b => trivial
    have hGenus : MaximumInGenusCausesAllInGenusReading (fun (_ : B) (_ : Unit) => True)
        (fun _ x y => near y < near x) causes := by
      intro r m hm
      have hEq : m = B.p := by
        cases m
        · rfl
        · exact absurd (show near B.a < near B.p by decide) (hm.2 B.p)
        · exact absurd (show near B.b < near B.p by decide) (hm.2 B.p)
      subst hEq
      exact hOrdered.causesAllInGenus hCreatures
    have hMore := h B Unit ℕ (fun _ _ => True) (fun _ x y => near y < near x) causes
      (fun x => x ≠ B.p) () near B.p hApproach hStrict hOrdered hCreatures hGenus
      B.a B.b () (by decide) trivial
    exact absurd hMore (by decide)
end TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionCauseMoreSuch
