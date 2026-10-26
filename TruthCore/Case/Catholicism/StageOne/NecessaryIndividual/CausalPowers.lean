import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.Quantifiers

/-!
Analyst-stipulated intervention semantics for #435. No source is attributed this
signature. The SEP archived discussion (witness SEP-ABSTRACT-OBJECTS-2020-CRITERIA,
§3.2) motivates testing capacities separately from exercises, but does not
provide a response-function theory. A Bool intervention switches the bearer on;
the output records an effect in a distinct recipient. This is a mathematical
capacity criterion, not an analysis of metaphysical causation or a proof of
metaphysical possibility. See docs/necessary-concrete-causal-powers.md.
-/
namespace TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.CausalPowers
open TruthCore.Modal
open TruthCore.Isabelle.AFP.GoedelGod (Box)
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1 (ExistsAt)

/-- Response of recipient y to activating bearer x at world w. The intervention
is a separate input, not an extra world or a change of x's identity. -/
abbrev Response (W I : Type) := I → I → W → Bool → Bool

/-- A capacity is a witnessed accessible manifestation with existing, distinct
endpoints and a different output under activation and deactivation. It need
not be exercised at w. Possession does not explain the bearer's existence. -/
def Capacity {W I : Type} (F : Frame W) (ex : ExistsAt W I)
    (response : Response W I) (x : I) (w : W) : Prop :=
  ∃ v, F.access w v ∧ ex x v ∧ ∃ y, ex y v ∧ x ≠ y ∧
    response x y v true ≠ response x y v false

/-- A stronger local response discipline than a bare opaque 'has power' atom:
no output without activation, no nonexisting endpoints, no self-effect. This
discipline alone asserts no capacities or necessary bearers. -/
def Disciplined {W I : Type} (ex : ExistsAt W I) (r : Response W I) : Prop :=
  (∀ x y w, r x y w false = false) ∧
  (∀ x y w, r x y w true = true → ex x w ∧ ex y w ∧ x ≠ y)

/-- One rigid necessary bearer false; recipient true exists only at world true.
World false is explicitly actual; the world type is inhabited and nontrivial. -/
def existsAt : ExistsAt Bool Bool := fun x w => x = false ∨ w = true

/-- The necessary bearer can produce an effect on the contingent recipient
when that recipient exists and activation is supplied. No effect in the dormant
world false; no response by recipient true or toward bearer false. -/
def response : Response Bool Bool := fun x y w on => (!x) && y && w && on

/-- One exact theory-relative compatibility contract. The witness false is
concrete by the independently computed response criterion in every successor;
the actual world has no exercise, while true has an activation-sensitive effect.
The recipient is contingent, so this is not necessity of all existence facts.
The original deRe-to-deDicto law is reused to obtain necessary exemplification.
The zero-response control has the same existence extension and no capacities. -/
def Compatibility : Prop :=
  Reflexive alternatingFrame ∧ alternatingFrame.access false true ∧ true ≠ false ∧
  Disciplined existsAt response ∧
  existsAt false false ∧
  Box alternatingFrame (existsAt false) false ∧
  Box alternatingFrame (Capacity alternatingFrame existsAt response false) false ∧
  DeDicto alternatingFrame
    (ConcreteAt existsAt (Capacity alternatingFrame existsAt response)) false ∧
  (∀ x y, response x y false true = false) ∧
  response false true true true = true ∧ response false true true false = false ∧
  ¬ existsAt true false ∧ existsAt true true ∧
  (∀ x w, ¬ Capacity alternatingFrame existsAt (fun _ _ _ _ => false) x w)

end TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.CausalPowers
