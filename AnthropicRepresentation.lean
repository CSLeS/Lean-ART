import AnthropicRepresentation.Existence

set_option autoImplicit false
noncomputable section
namespace LotteryChoice
variable {X : Type} [Fintype X]
section Abstract
variable {Site S : Type} {Z : S → Type} [∀ s, Fintype (Z s)] (site : S → Site)

/-- Theorem 1, first clause: A1–A5 hold iff a lottery choice representation exists. -/
theorem representation_iff [Nonempty S] (pref : Ticket X Z → Ticket X Z → Prop) :
    Axioms site pref ↔ Nonempty (Representation site pref) :=
  ⟨representation_of_axioms site pref, fun h => h.elim (axioms_of_representation site pref)⟩

/-- Deliberation: the diagonal restriction `s ≿_I s' :↔ (s; f_s) ≿_I (s'; f_{s'})`. -/
def delib (f : ∀ s, Z s → Lottery X) (pref : Ticket X Z → Ticket X Z → Prop)
    (s s' : S) : Prop :=
  pref ⟨s, f s⟩ ⟨s', f s'⟩

/-- `V_s = ∑_z R_s(z) u(f_s(z))`. -/
def V (f : ∀ s, Z s → Lottery X) {pref : Ticket X Z → Ticket X Z → Prop}
    (rep : Representation site pref) (s : S) : ℝ :=
  EV rep.u rep.R ⟨s, f s⟩

/-- Theorem 1, second clause: deliberation is represented by `V`. -/
theorem delib_iff (f : ∀ s, Z s → Lottery X) {pref : Ticket X Z → Ticket X Z → Prop}
    (rep : Representation site pref) {s s' : S} (h : site s = site s') :
    delib f pref s s' ↔ V site f rep s' ≤ V site f rep s := by
  unfold delib V
  exact rep.represents _ _ h


end Abstract

/-! ## Problem / information-set / action adapter

This namespace defines the full additional domain needed for the supplied
specialisation; it does not require access to any manuscript. Problem and Info
are arbitrary types, eligible Gamma I records admissible information labels,
A I is the finite action type, and Z Gamma is the finite terminal type. Equal
information labels specify the common comparison domain. Actual payoffs are
indexed only by the problem, so changes of contemplated behaviour do not change
them. No extra behavioural assumptions are introduced.
-/

namespace Paper

/-- A contemplated behaviour at an eligible information set of a problem. -/
structure Scenario {Problem Info : Type}
    (eligible : Problem → Info → Prop)
    (A : Info → Type) [∀ I, Fintype (A I)] where
  Γ : Problem
  I : Info
  hI : eligible Γ I
  α : Lottery (A I)

variable {Problem Info : Type}
variable (eligible : Problem → Info → Prop)
variable (A : Info → Type) [∀ I, Fintype (A I)]
variable (Z : Problem → Type) [∀ Γ, Fintype (Z Γ)]

/-- The comparison site is the information-set label. -/
abbrev scenarioSite (s : Scenario eligible A) : Info :=
  s.I

/-- All scenarios of a given problem share that problem's terminal type. -/
abbrev scenarioNodes (s : Scenario eligible A) : Type :=
  Z s.Γ

/-- The abstract iff specialised to problem/information/action scenarios. -/
theorem representation_iff [Nonempty (Scenario eligible A)]
    (pref : Ticket X (scenarioNodes eligible A Z) →
      Ticket X (scenarioNodes eligible A Z) → Prop) :
    Axioms (scenarioSite eligible A) pref ↔
      Nonempty (Representation (scenarioSite eligible A) pref) := by
  exact LotteryChoice.representation_iff (scenarioSite eligible A) pref

/-- The actual-payoff comparison at a common information set is represented
by the expected utility of each problem's own payoff assignment. -/
theorem deliberation_iff
    (f : ∀ Γ : Problem, Z Γ → Lottery X)
    {pref : Ticket X (scenarioNodes eligible A Z) →
      Ticket X (scenarioNodes eligible A Z) → Prop}
    (rep : Representation (scenarioSite eligible A) pref)
    {s s' : Scenario eligible A} (h : s.I = s'.I) :
    pref ⟨s, f s.Γ⟩ ⟨s', f s'.Γ⟩ ↔
      (∑ z : Z s'.Γ, (rep.R s').prob z * rep.u (f s'.Γ z)) ≤
      (∑ z : Z s.Γ, (rep.R s).prob z * rep.u (f s.Γ z)) := by
  exact rep.represents ⟨s, f s.Γ⟩ ⟨s', f s'.Γ⟩ h

/-- Terminal probabilities are identified by the full specialised ticket
preferences, including when distinct terminals have the same actual payoff. -/
theorem R_unique
    {pref : Ticket X (scenarioNodes eligible A Z) →
      Ticket X (scenarioNodes eligible A Z) → Prop}
    (rep rep' : Representation (scenarioSite eligible A) pref)
    (s : Scenario eligible A) : rep.R s = rep'.R s := by
  exact LotteryChoice.R_unique (scenarioSite eligible A) rep rep' s

/-- One common positive affine transformation relates the two utilities. -/
theorem u_unique [Nonempty (Scenario eligible A)]
    {pref : Ticket X (scenarioNodes eligible A Z) →
      Ticket X (scenarioNodes eligible A Z) → Prop}
    (rep rep' : Representation (scenarioSite eligible A) pref) :
    ∃ a b : ℝ, 0 < a ∧ ∀ p : Lottery X, rep'.u p = a * rep.u p + b := by
  exact LotteryChoice.u_unique (scenarioSite eligible A) rep rep'

end Paper

end LotteryChoice

end

/-! Kernel dependency audit of every required public result. -/
#print axioms LotteryChoice.representation_of_axioms
#print axioms LotteryChoice.axioms_of_representation
#print axioms LotteryChoice.representation_iff
#print axioms LotteryChoice.delib_iff
#print axioms LotteryChoice.R_unique
#print axioms LotteryChoice.u_unique
#print axioms LotteryChoice.Representation.positiveAffine
#print axioms LotteryChoice.Paper.representation_iff
#print axioms LotteryChoice.Paper.deliberation_iff
#print axioms LotteryChoice.Paper.R_unique
#print axioms LotteryChoice.Paper.u_unique

#print axioms LotteryChoice.Representation.positiveAffine_u
#print axioms LotteryChoice.Representation.positiveAffine_R
