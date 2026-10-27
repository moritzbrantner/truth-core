import TruthCore.Case.Catholicism.Root

/-!
# Divine founding through an attested envoy (#357)

The skeleton's bridge `BridgeChristsChurchFoundedByGod` is decomposed here
into four typed premises over one agency vocabulary, so that the bridge is
*derived* rather than assumed (`TruthCore.Results.Case.Catholicism.StageThree.DivineFounding`).

The line of the derivation:

1. **Attestation** (`ResurrectionConfirmsMandate`): if Jesus claimed divine
   authority and rose, then God, by the resurrection, confirms the proposition
   that Jesus holds a mandate from God. Source: Acts 17.31 (God "gave
   assurance to all" by raising the man he appointed).
2. **Veracity** (`GodConfirmsOnlyTruth`): what God confirms by a sign is true.
   Supported by *Dei Filius* ch. 3, para. 1 (God "can neither be deceived nor
   deceive").
3. **Scope** (`MandatedFoundingWithTeaching`): if Jesus holds God's mandate,
   then each visible authoritative society Jesus founded he founded in the
   exercise of that mandate, commissioning it to teach. Supported by Matthew
   28.18-20, where the commission to disciple, baptize and teach is grounded
   ("therefore") in the authority Jesus says was given to him. The universal
   scope over societies is *not* in the source; it is an explicit open part.
4. **Envoy founding** (`EnvoyFoundingIsPrincipalsFounding`): if an envoy of a
   God founds a society in the exercise of his mandate from that God and
   commissions it to teach, that God founded it as a teaching authority.
   Supported by John 13.20 (who receives the one I send receives me, and who
   receives me receives the one who sent me); its extension from reception to
   founding is open.

The decisive fork is premise 3: whether an attested mandate covers the
founding of an institution with teaching authority, or only a message.
Each premise is necessary: `omissionModels` exhibits, for each one, a model
of the other three together with every stage antecedent of the bridge in
which the bridge fails. `jointModel` shows the four premises and the bridge's
antecedents are jointly satisfiable, so the derivation is not vacuous. These
are schema models, not possible worlds of Christian history.
-/

namespace TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism

/-- Typed agency vocabulary over the skeleton signature (DEF-DIVINE-FOUNDING-AGENCY).

* `Confirms g p` — `g` confirms the proposition `p` by a sign that is `g`'s own
  deed (a testimonial act, as *Dei Filius* ch. 3 calls miracles *argumenta* of
  revelation), not merely a display of power.
* `HoldsMandate x g` — `x` speaks and acts with authority received from `g`
  (`x` is `g`'s envoy). It does not identify `x` with `g`.
* `FoundedInMandate x g c` — `x` founded the society `c` in the exercise of the
  mandate `x` holds from `g`.
* `CommissionedToTeach x c` — in founding `c`, `x` commissioned it to teach.

All four are parameters; no axiom constrains them. Their content is fixed only
by the premises below. -/
structure Agency (σ : Signature) where
  Confirms : σ.Being → Prop → Prop
  HoldsMandate : σ.Being → σ.Being → Prop
  FoundedInMandate : σ.Being → σ.Being → σ.Society → Prop
  CommissionedToTeach : σ.Being → σ.Society → Prop

/-- Attestation premise `STMT-RESURRECTION-CONFIRMS-JESUS-MANDATE`: for any God
with the classical attributes who can reveal recognizably, if Jesus claimed
divine authority and rose, then that God, by the resurrection, confirms that
Jesus holds a mandate from him. Source: Acts 17.31 (claim
`NT-ACTS-17-31-RESURRECTION-AS-ASSURANCE`). The source speaks of the man God
appointed to judge the world; that the appointment is the mandate Jesus
claimed is the claim's reading. -/
def ResurrectionConfirmsMandate (σ : Signature) (A : Agency σ) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → σ.RevealsRecognizably g →
    σ.ClaimedDivineAuthority σ.jesus → σ.RoseFromTheDead σ.jesus →
      A.Confirms g (A.HoldsMandate σ.jesus g)

/-- Veracity premise `STMT-GOD-CONFIRMS-ONLY-TRUTH`: whatever a God with the
classical attributes confirms by a sign is true. Supported by *Dei Filius*
ch. 3, para. 1 (*qui nec falli nec fallere potest*), read as applying to
confirmation by signs (para. 2). Divine veracity is not among the encoded
classical attributes, so this is a separate premise. -/
def GodConfirmsOnlyTruth (σ : Signature) (A : Agency σ) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ p : Prop, A.Confirms g p → p

/-- Scope premise `STMT-MANDATE-COVERS-JESUS-FOUNDING-WITH-TEACHING`: if Jesus
holds a mandate from `g`, then every visible society with authority that Jesus
founded he founded in the exercise of that mandate and commissioned to teach.
Supported (not stated) by Matthew 28.18-20; the universal scope over every such
society, and the map from the commissioned eleven to a society, are open
content of this premise, not attributed to Matthew. -/
def MandatedFoundingWithTeaching (σ : Signature) (A : Agency σ) : Prop :=
  ∀ g, A.HoldsMandate σ.jesus g →
    ∀ c, σ.Founded σ.jesus c → σ.VisibleWithAuthority c →
      A.FoundedInMandate σ.jesus g c ∧ A.CommissionedToTeach σ.jesus c

/-- Envoy-founding premise `STMT-ENVOY-FOUNDING-IS-GODS-FOUNDING`: if a God's
envoy founds a society in the exercise of his mandate from that God and
commissions it to teach, that God founded it as a teaching authority (founding
*through* an envoy, as *Dei Filius* ch. 3 para. 5 says God instituted the
Church *per Filium*; DISAMB-FOUNDED-BY-GOD). Supported by John 13.20; the
extension from receiving an envoy to founding through one is open. -/
def EnvoyFoundingIsPrincipalsFounding (σ : Signature) (A : Agency σ) : Prop :=
  ∀ g x c, σ.IsGod g → A.FoundedInMandate x g c → A.CommissionedToTeach x c →
    σ.FoundedAsTeachingAuthority g c

/-! ## Schema models: necessity of each premise and joint satisfiability

Two beings (`true` is the God, `false` is Jesus) and one society. Every stage
antecedent of the bridge holds. These are formal-schema models only. -/

/-- A two-being signature in which every stage predicate holds and
`FoundedAsTeachingAuthority` is the given proposition `fta`. -/
def modelSig (fta : Prop) : Signature where
  Being := Bool
  IsGod b := b = true
  HasClassicalAttributes _ := True
  RevealsRecognizably _ := True
  jesus := false
  ClaimedDivineAuthority _ := True
  RoseFromTheDead _ := True
  Society := Unit
  catholicChurch := ()
  Founded _ _ := True
  VisibleWithAuthority _ := True
  FoundedAsTeachingAuthority _ _ := fta
  DefinitivelyProposesAsRevealed _ _ := True
  creedOneGodFatherAlmightyCreator := True
  creedOneLordJesusChristOnlyBegottenConsubstantial := True
  creedIncarnateOfSpiritAndVirginMary := True
  creedCrucifiedUnderPilateSufferedBuried := True
  creedRoseOnTheThirdDay := True
  creedAscendedSeatedAtRightHand := True
  creedWillComeToJudgeKingdomWithoutEnd := True
  creedHolySpiritLordGiverOfLife := True
  creedOneHolyCatholicApostolicChurch := True
  creedOneBaptismForForgiveness := True
  creedResurrectionOfTheDead := True
  creedLifeOfTheWorldToCome := True

/-- An agency interpretation with constant relations. -/
def modelAgency (fta : Prop) (conf : Prop → Prop) (mandate inMandate teach : Prop) :
    Agency (modelSig fta) where
  Confirms _ p := conf p
  HoldsMandate _ _ := mandate
  FoundedInMandate _ _ _ := inMandate
  CommissionedToTeach _ _ := teach

/-- Every stage antecedent of the bridge holds in `modelSig`, with a God, a
founded visible society and Jesus' claim and resurrection. -/
theorem modelSig_antecedents (fta : Prop) :
    GodExists (modelSig fta).IsGod ∧ GodHasClassicalAttributes (modelSig fta) ∧
    RevelationPossibleAndRecognizable (modelSig fta) ∧
    JesusClaimedDivineAuthorityAndRose (modelSig fta) ∧
    ChristFoundedVisibleChurch (modelSig fta) :=
  ⟨⟨true, rfl⟩, fun _ _ => trivial, fun _ _ => trivial, ⟨trivial, trivial⟩,
    ⟨(), trivial, trivial⟩⟩

/-- With `FoundedAsTeachingAuthority` false, the bridge fails in `modelSig`. -/
theorem modelSig_bridge_fails : ¬ BridgeChristsChurchFoundedByGod (modelSig False) :=
  fun h => h true rfl trivial trivial trivial trivial () trivial trivial

/-- Each of the four premises is needed: dropping any one, the other three and
every stage antecedent hold while the bridge fails. -/
theorem omissionModels :
    (∃ σ : Signature, ∃ A : Agency σ, ¬ ResurrectionConfirmsMandate σ A ∧
      GodConfirmsOnlyTruth σ A ∧ MandatedFoundingWithTeaching σ A ∧
      EnvoyFoundingIsPrincipalsFounding σ A ∧ ¬ BridgeChristsChurchFoundedByGod σ) ∧
    (∃ σ : Signature, ∃ A : Agency σ, ResurrectionConfirmsMandate σ A ∧
      ¬ GodConfirmsOnlyTruth σ A ∧ MandatedFoundingWithTeaching σ A ∧
      EnvoyFoundingIsPrincipalsFounding σ A ∧ ¬ BridgeChristsChurchFoundedByGod σ) ∧
    (∃ σ : Signature, ∃ A : Agency σ, ResurrectionConfirmsMandate σ A ∧
      GodConfirmsOnlyTruth σ A ∧ ¬ MandatedFoundingWithTeaching σ A ∧
      EnvoyFoundingIsPrincipalsFounding σ A ∧ ¬ BridgeChristsChurchFoundedByGod σ) ∧
    (∃ σ : Signature, ∃ A : Agency σ, ResurrectionConfirmsMandate σ A ∧
      GodConfirmsOnlyTruth σ A ∧ MandatedFoundingWithTeaching σ A ∧
      ¬ EnvoyFoundingIsPrincipalsFounding σ A ∧ ¬ BridgeChristsChurchFoundedByGod σ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Without attestation: God confirms only truths, and no mandate holds.
    refine ⟨modelSig False, modelAgency False (fun p => p) False False False,
      ?_, ?_, ?_, ?_, modelSig_bridge_fails⟩
    · intro h; exact h true rfl trivial trivial trivial trivial
    · intro _ _ _ _ hp; exact hp
    · intro _ hm; exact hm.elim
    · intro _ _ _ _ hm; exact hm.elim
  · -- Without veracity: God confirms everything, but no mandate holds.
    refine ⟨modelSig False, modelAgency False (fun _ => True) False False False,
      ?_, ?_, ?_, ?_, modelSig_bridge_fails⟩
    · intro _ _ _ _ _ _; trivial
    · intro h; exact h true rfl trivial False trivial
    · intro _ hm; exact hm.elim
    · intro _ _ _ _ hm; exact hm.elim
  · -- Without scope: the mandate holds, but the founding is not done in it.
    refine ⟨modelSig False, modelAgency False (fun p => p) True False True,
      ?_, ?_, ?_, ?_, modelSig_bridge_fails⟩
    · intro _ _ _ _ _ _; trivial
    · intro _ _ _ _ hp; exact hp
    · intro h; exact (h true trivial () trivial trivial).1
    · intro _ _ _ _ hm; exact hm.elim
  · -- Without envoy founding: everything holds except God's founding.
    refine ⟨modelSig False, modelAgency False (fun p => p) True True True,
      ?_, ?_, ?_, ?_, modelSig_bridge_fails⟩
    · intro _ _ _ _ _ _; trivial
    · intro _ _ _ _ hp; exact hp
    · intro _ _ _ _ _; exact ⟨trivial, trivial⟩
    · intro h; exact h true false () rfl trivial trivial

/-- The four premises and every stage antecedent of the bridge are jointly
satisfiable, so the derivation of the bridge is not vacuous. -/
theorem jointModel :
    ∃ σ : Signature, ∃ A : Agency σ,
      ResurrectionConfirmsMandate σ A ∧ GodConfirmsOnlyTruth σ A ∧
      MandatedFoundingWithTeaching σ A ∧ EnvoyFoundingIsPrincipalsFounding σ A ∧
      GodExists σ.IsGod ∧ GodHasClassicalAttributes σ ∧
      RevelationPossibleAndRecognizable σ ∧ JesusClaimedDivineAuthorityAndRose σ ∧
      ChristFoundedVisibleChurch σ := by
  refine ⟨modelSig True, modelAgency True (fun p => p) True True True,
    ?_, ?_, ?_, ?_, modelSig_antecedents True⟩
  · intro _ _ _ _ _ _; trivial
  · intro _ _ _ _ hp; exact hp
  · intro _ _ _ _ _; exact ⟨trivial, trivial⟩
  · intro _ _ _ _ _ _; trivial

end TruthCore.Case.Catholicism.StageThree.DivineFounding
