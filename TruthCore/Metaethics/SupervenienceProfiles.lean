module

public import TruthCore.English.VanRoojen.MoralCognitivism

/-!
Analyst comparison of moral-supervenience claims, connected to the Blackburn
competence reading in `MoralCognitivism` but not attributed to Blackburn.

`World` is an explicitly selected range of admissible situations, not a proof
that every metaphysically possible world is represented. `Case` is shared
across that range. `natural` is the selected nonmoral comparison
profile, `moral` is an alleged moral fact/extension, and `verdict` is the
stipulated verdict function per world. These are deliberately different fields. No causal
grounding, moral truthmaker, normative authority, objectivity or exhaustive
nonmoral description is supplied by the signature.

The controls use two worlds and two cases. Their structural counterexamples
are not counterexamples to actual moral realism, because applicability of the
profile to reality is left open. In particular a conceptual constraint on
competent verdicts does not bridge to metaphysical necessitation of facts.
-/

@[expose] public section

namespace TruthCore.Metaethics.SupervenienceProfiles

structure Profile (World Case : Type) where
  natural : World → Case → Bool
  moral : World → Case → Bool
  verdict : World → Case → Bool
  competent : World → Prop

/-- World-relative (weak) moral supervenience: in any admitted world,
nonmorally identical cases have the same moral status. -/
def Weak {World Case : Type} (p : Profile World Case) : Prop :=
  ∀ w x y, p.natural w x = p.natural w y → p.moral w x = p.moral w y

/-- Cross-world (strong) moral supervenience: any two admitted cases, even
across worlds, share moral status if their nonmoral profiles match. -/
def Strong {World Case : Type} (p : Profile World Case) : Prop :=
  ∀ w v x y, p.natural w x = p.natural v y → p.moral w x = p.moral v y

/-- A separate constraint on competent *verdicts*, not the moral facts.
It says nothing about whether those verdicts are correct. -/
def Competence {World Case : Type} (p : Profile World Case) : Prop :=
  ∀ w, p.competent w → ∀ x y,
    p.natural w x = p.natural w y → p.verdict w x = p.verdict w y

/-- Strong supervenience can be strictly stronger than weak; the conceptual
verdict constraint need not imply factual supervenience; and two separately
strongly supervenient profile assignments can disagree on a moral mapping while sharing
their entire selected natural profile. These are finite encoding controls. -/
def Controls : Prop :=
  (∃ p : Profile Bool Bool, Weak p ∧ ¬ Strong p) ∧
  (∃ p : Profile Bool Bool, Competence p ∧ ¬ Weak p) ∧
  (∃ p q : Profile Bool Bool,
    p.natural = q.natural ∧ Strong p ∧ Strong q ∧
    ∃ w x, p.moral w x ≠ q.moral w x)

def weakOnly : Profile Bool Bool where
  natural := fun _ _ => false
  moral := fun w _ => w
  verdict := fun _ _ => false
  competent := fun _ => True

def competentOnly : Profile Bool Bool where
  natural := fun _ _ => false
  moral := fun _ x => x
  verdict := fun _ _ => false
  competent := fun _ => True

def firstStrong : Profile Bool Bool where
  natural := fun _ x => x
  moral := fun _ x => x
  verdict := fun _ x => x
  competent := fun _ => True

def secondStrong : Profile Bool Bool where
  natural := fun _ x => x
  moral := fun _ x => !x
  verdict := fun _ x => !x
  competent := fun _ => True

end TruthCore.Metaethics.SupervenienceProfiles
