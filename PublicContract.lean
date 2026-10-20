import AnthropicRepresentation

/-!
# Public contract verification

Each `example` assigns a fully explicit public declaration to the precise type
required by the supplied specification. The `@` applications expose every
implicit parameter and typeclass argument. In particular, the existence check
has no representation premise, and the probability uniqueness checks have no
nonemptiness assumption beyond the explicitly supplied scenario.

The final commands expose protected definitions and public declaration types;
Dependency audits separately check the kernel boundary.
-/
set_option autoImplicit false
noncomputable section
open LotteryChoice

example : ∀ {X : Type} [Fintype X] {Site S : Type} {Z : S → Type}
    [∀ s, Fintype (Z s)] (site : S → Site) [Nonempty S]
    (pref : Ticket X Z → Ticket X Z → Prop),
    Representation site pref → Axioms site pref :=
  @LotteryChoice.axioms_of_representation

example : ∀ {X : Type} [Fintype X] {Site S : Type} {Z : S → Type}
    [∀ s, Fintype (Z s)] (site : S → Site)
    (pref : Ticket X Z → Ticket X Z → Prop),
    Axioms site pref → Nonempty (Representation site pref) :=
  @LotteryChoice.representation_of_axioms

example : ∀ {X : Type} [Fintype X] {Site S : Type} {Z : S → Type}
    [∀ s, Fintype (Z s)] (site : S → Site) [Nonempty S]
    (pref : Ticket X Z → Ticket X Z → Prop),
    Axioms site pref ↔ Nonempty (Representation site pref) :=
  @LotteryChoice.representation_iff

example : ∀ {X : Type} [Fintype X] {Site S : Type} {Z : S → Type}
    [∀ s, Fintype (Z s)] (site : S → Site)
    (f : ∀ s, Z s → Lottery X)
    {pref : Ticket X Z → Ticket X Z → Prop}
    (rep : Representation site pref) {s s' : S},
    site s = site s' →
      (delib f pref s s' ↔ V site f rep s' ≤ V site f rep s) :=
  @LotteryChoice.delib_iff

example : ∀ {X : Type} [Fintype X] {Site S : Type} {Z : S → Type}
    [∀ s, Fintype (Z s)] (site : S → Site)
    {pref : Ticket X Z → Ticket X Z → Prop}
    (r r' : Representation site pref) (s : S), r.R s = r'.R s :=
  @LotteryChoice.R_unique

example : ∀ {X : Type} [Fintype X] {Site S : Type} {Z : S → Type}
    [∀ s, Fintype (Z s)] (site : S → Site) [Nonempty S]
    {pref : Ticket X Z → Ticket X Z → Prop}
    (r r' : Representation site pref),
    ∃ a b : ℝ, 0 < a ∧ ∀ p : Lottery X, r'.u p = a * r.u p + b :=
  @LotteryChoice.u_unique

example : ∀ {X : Type} [Fintype X] {Site S : Type} {Z : S → Type}
    [∀ s, Fintype (Z s)] (site : S → Site)
    {pref : Ticket X Z → Ticket X Z → Prop}
    (_rep : Representation site pref) (a _b : ℝ),
    0 < a → Representation site pref :=
  @LotteryChoice.Representation.positiveAffine

example : ∀ {X : Type} [Fintype X] {Site S : Type} {Z : S → Type}
    [∀ s, Fintype (Z s)] (site : S → Site)
    {pref : Ticket X Z → Ticket X Z → Prop}
    (rep : Representation site pref) (a b : ℝ) (ha : 0 < a) (p : Lottery X),
    (Representation.positiveAffine site rep a b ha).u p = a * rep.u p + b :=
  @LotteryChoice.Representation.positiveAffine_u

example : ∀ {X : Type} [Fintype X] {Site S : Type} {Z : S → Type}
    [∀ s, Fintype (Z s)] (site : S → Site)
    {pref : Ticket X Z → Ticket X Z → Prop}
    (rep : Representation site pref) (a b : ℝ) (ha : 0 < a),
    (Representation.positiveAffine site rep a b ha).R = rep.R :=
  @LotteryChoice.Representation.positiveAffine_R

example : ∀ {X : Type} [Fintype X] {Problem Info : Type}
    (eligible : Problem → Info → Prop) (A : Info → Type) [∀ I, Fintype (A I)]
    (Z : Problem → Type) [∀ Γ, Fintype (Z Γ)] [Nonempty (Paper.Scenario eligible A)]
    (pref : Ticket X (Paper.scenarioNodes eligible A Z) →
      Ticket X (Paper.scenarioNodes eligible A Z) → Prop),
    Axioms (Paper.scenarioSite eligible A) pref ↔
      Nonempty (Representation (Paper.scenarioSite eligible A) pref) :=
  @LotteryChoice.Paper.representation_iff

example : ∀ {X : Type} [Fintype X] {Problem Info : Type}
    (eligible : Problem → Info → Prop) (A : Info → Type) [∀ I, Fintype (A I)]
    (Z : Problem → Type) [∀ Γ, Fintype (Z Γ)]
    (f : ∀ Γ : Problem, Z Γ → Lottery X)
    {pref : Ticket X (Paper.scenarioNodes eligible A Z) →
      Ticket X (Paper.scenarioNodes eligible A Z) → Prop}
    (rep : Representation (Paper.scenarioSite eligible A) pref)
    {s s' : Paper.Scenario eligible A},
    s.I = s'.I →
      (pref ⟨s, f s.Γ⟩ ⟨s', f s'.Γ⟩ ↔
        (∑ z : Z s'.Γ, (rep.R s').prob z * rep.u (f s'.Γ z)) ≤
        (∑ z : Z s.Γ, (rep.R s).prob z * rep.u (f s.Γ z))) :=
  @LotteryChoice.Paper.deliberation_iff

example : ∀ {X : Type} [Fintype X] {Problem Info : Type}
    (eligible : Problem → Info → Prop) (A : Info → Type) [∀ I, Fintype (A I)]
    (Z : Problem → Type) [∀ Γ, Fintype (Z Γ)]
    {pref : Ticket X (Paper.scenarioNodes eligible A Z) →
      Ticket X (Paper.scenarioNodes eligible A Z) → Prop}
    (rep rep' : Representation (Paper.scenarioSite eligible A) pref)
    (s : Paper.Scenario eligible A), rep.R s = rep'.R s :=
  @LotteryChoice.Paper.R_unique

example : ∀ {X : Type} [Fintype X] {Problem Info : Type}
    (eligible : Problem → Info → Prop) (A : Info → Type) [∀ I, Fintype (A I)]
    (Z : Problem → Type) [∀ Γ, Fintype (Z Γ)] [Nonempty (Paper.Scenario eligible A)]
    {pref : Ticket X (Paper.scenarioNodes eligible A Z) →
      Ticket X (Paper.scenarioNodes eligible A Z) → Prop}
    (rep rep' : Representation (Paper.scenarioSite eligible A) pref),
    ∃ a b : ℝ, 0 < a ∧ ∀ p : Lottery X, rep'.u p = a * rep.u p + b :=
  @LotteryChoice.Paper.u_unique

/- The adapter uses exactly the information label and the problem's terminals. -/
example {Problem Info : Type} (eligible : Problem → Info → Prop)
    (A : Info → Type) [∀ I, Fintype (A I)] (s : Paper.Scenario eligible A) :
    Paper.scenarioSite eligible A s = s.I := rfl

example {Problem Info : Type} (eligible : Problem → Info → Prop)
    (A : Info → Type) [∀ I, Fintype (A I)] (Z : Problem → Type)
    (s : Paper.Scenario eligible A) : Paper.scenarioNodes eligible A Z s = Z s.Γ := rfl

end

#check @LotteryChoice.axioms_of_representation
#check @LotteryChoice.representation_of_axioms
#check @LotteryChoice.representation_iff
#check @LotteryChoice.delib_iff
#check @LotteryChoice.R_unique
#check @LotteryChoice.u_unique
#check @LotteryChoice.Representation.positiveAffine
#check @LotteryChoice.Representation.positiveAffine_u
#check @LotteryChoice.Representation.positiveAffine_R
#check @LotteryChoice.Paper.representation_iff
#check @LotteryChoice.Paper.deliberation_iff
#check @LotteryChoice.Paper.R_unique
#check @LotteryChoice.Paper.u_unique

#print LotteryChoice.Lottery
#print LotteryChoice.Lottery.mix
#print LotteryChoice.Lottery.pure
#print LotteryChoice.Ticket
#print LotteryChoice.mixF
#print LotteryChoice.Axioms
#print LotteryChoice.EV
#print LotteryChoice.Representation
#print LotteryChoice.delib
#print LotteryChoice.V
#print LotteryChoice.Paper.Scenario
#print LotteryChoice.Paper.scenarioSite
#print LotteryChoice.Paper.scenarioNodes

#print axioms LotteryChoice.affine_order_unique
#print axioms LotteryChoice.affine_rep_unique
#print axioms LotteryChoice.normalized_constants_agree
#print axioms LotteryChoice.representation_of_axioms
#print axioms LotteryChoice.axioms_of_representation
#print axioms LotteryChoice.representation_iff
#print axioms LotteryChoice.delib_iff
#print axioms LotteryChoice.R_unique
#print axioms LotteryChoice.u_unique
#print axioms LotteryChoice.Representation.positiveAffine
#print axioms LotteryChoice.Representation.positiveAffine_u
#print axioms LotteryChoice.Representation.positiveAffine_R
#print axioms LotteryChoice.Paper.representation_iff
#print axioms LotteryChoice.Paper.deliberation_iff
#print axioms LotteryChoice.Paper.R_unique
#print axioms LotteryChoice.Paper.u_unique

/-! Additional audits of the finite-mixture and normalisation prerequisites. -/
#check @LotteryChoice.exists_best_worst
#check @LotteryChoice.affine_rep_of_bounded_normalized
#check @LotteryChoice.affine_rep_unique
#check @LotteryChoice.normalized_constants_agree
#check @LotteryChoice.finite_ticket_representation
#print axioms LotteryChoice.exists_best_worst
#print axioms LotteryChoice.affine_rep_of_bounded_normalized
#print axioms LotteryChoice.affine_baryF
#print axioms LotteryChoice.affine_barycenter
#print axioms LotteryChoice.finite_ticket_representation
