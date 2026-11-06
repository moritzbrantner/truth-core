module

public import TruthCore.German.Kant.CosmologicalInference

/-!
# Operari sequitur esse: two readings (#1103)

Two Aquinas readings used to derive the owner's causal-power concreteness
principle from the esse sense of concrete. Both are stated at a selected world
over the generic `Ontic` signature. `InAct x r` is the shared Aquinas vocabulary
("x is in act in the respect r"; `DEF-ESSE`). Neither reading says in which
respect the agent is in act, and neither mentions being: getting from "in act"
to "has esse" is the separate reading `ActualityOnlyInsofarAsBeingReading`
(ST I q.4 a.1 ad 3).

Pinned witnesses: `AQUINAS-ST-I-Q75-A1-A2` and `AQUINAS-ST-I-Q25-A1`
(Corpus Thomisticum, Leonine text).
-/

@[expose] public section

namespace TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.OperationFollowsBeing

open TruthCore.German.Kant.CosmologicalInference (Ontic)

/-- ST I q.75 a.2 co.: "Non enim est operari nisi entis in actu, unde eo modo
aliquid operatur, quo est. Propter quod non dicimus quod calor calefacit, sed
calidum." Operating belongs only to a being in act. It is applied here to
causing another (`Ontic.Causes`), which the passage's own example (the hot thing
heats) treats as operating. This is the weakest reading: the agent is in act in
some respect. Being, subsistence and the mode of operation are not included. -/
def OperationOnlyOfBeingInActReading {W B R : Type} (o : Ontic W B)
    (InAct : B → R → Prop) (w : W) : Prop :=
  ∀ x y, o.Causes w x y → ∃ r, InAct x r

/-- ST I q.25 a.1 co.: "unumquodque, secundum quod est actu et perfectum,
secundum hoc est principium activum alicuius ... potentia activa est principium
agendi in aliud". Whatever has active power, a principle of acting on another
(here the supplied causal-power predicate), is in act in some respect. Neither
the converse nor any degree of power is included. -/
def ActivePowerOnlyInsofarAsInActReading {W B R : Type}
    (hasCausalPower : W → B → Prop) (InAct : B → R → Prop) (w : W) : Prop :=
  ∀ x, hasCausalPower w x → ∃ r, InAct x r

end TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.OperationFollowsBeing
