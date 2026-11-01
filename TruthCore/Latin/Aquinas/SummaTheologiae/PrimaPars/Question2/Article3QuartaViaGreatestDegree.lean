import Mathlib.Order.Bounds.Basic
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia

/-! A greatest-degree interpretation of *maxime tale* in ST I q.2 a.3,
quarta via, passage AQUINAS-ST-I-Q2-A3. The supplied value map interprets
one selected perfection; it does not identify analogical being with a
homogeneous ontology or impose a total order. This reading is separate from
the stronger, order-free analyst principle whose antecedent is mere maximality.
No implication to that existing principle is asserted. -/
namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v w

/-- A bearer of the selected perfection whose represented degree is greatest
among its bearers' degrees. Own possession is explicit; Mathlib's image-set
membership alone would not imply possession by this particular being.
Preorder-equivalent degrees and different beings at the greatest degree are
allowed: neither strict supremacy nor uniqueness is asserted. -/
def GreatestDegreeBearer {Being : Type u} {Respect : Sort v}
    {Degree : Type w} [Preorder Degree]
    (InAct : Being → Respect → Prop) (r : Respect)
    (value : Being → Degree) (m : Being) : Prop :=
  InAct m r ∧ IsGreatest (value '' {x | InAct x r}) (value m)

/-- Read *quod autem dicitur maxime tale in aliquo genere, est causa omnium
quae sunt illius generis* at one arbitrary supplied perfection. A greatest-degree
bearer causes that perfection in every other bearer. This is a source assertion,
not a proof of the causal principle or the reality of the supplied degrees.
The source's fire example and Aristotle citation supply no independent warrant
for the universal converse; the separate source-interpretation record retains
that limitation. -/
def GreatestDegreeCausesAllInGenusReading {Being : Type u} {Respect : Sort v}
    {Degree : Type w} [Preorder Degree]
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (r : Respect)
    (value : Being → Degree) : Prop :=
  ∀ m, GreatestDegreeBearer InAct r value m →
    CausesAllInGenus InAct CausesIn r m

end TruthCore.Latin.Aquinas.SummaTheologiae
