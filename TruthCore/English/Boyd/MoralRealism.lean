/-! Richard Boyd, “How to be a Moral Realist”, Contemporary Materialism
reprint §4.3, pp.329–331. This is a determinate positive-case fragment:
fostering goods and sustaining their homeostasis is sufficient for positive
moral goodness. It does not replace degrees or borderline cases by a universal
bivalent definition. The empirical existence and referential adequacy of the
cluster remain open. -/
namespace TruthCore.English.Boyd

/-- §4.3(3): actions tending to foster human goods or their unifying mechanisms
are morally good to that extent. Only a sufficient positive-case condition is
encoded; no precise threshold or resolution of hard cases is attributed. -/
def ClusterGoodnessReading {Act : Type}
    (Good FostersGoods SustainsMechanisms : Act → Prop) : Prop :=
  ∀ a, FostersGoods a ∨ SustainsMechanisms a → Good a

end TruthCore.English.Boyd
