import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic

/-!
# Anthropic lottery choice: definitions and mathematical contract

The protected definitions below are unchanged from the supplied specification.
The proof modules establish normalised affine values, finite probability weights,
the representation and converse, and both uniqueness claims. The entry module
retains the problem/information/action specialisation and the public axiom audit.

## Mathematical domain

* Lottery X is the full real probability simplex on the finite prize type X.
  Mixtures use t : unitInterval, including endpoints. Independence applies only
  when 0 < t < 1. No restriction to rational weights is permitted.
* S is an arbitrary type of scenarios; Site is an arbitrary type of comparison
  indices. Neither type is assumed finite. site : S -> Site assigns a scenario
  to the comparison domain in which it belongs. Surjectivity is unnecessary.
* Z s is the finite terminal type at scenario s. A ticket is a function from Z s
  to Lottery X. Ticket X Z includes its scenario tag, so terminal types can be
  shared by different scenarios without identifying their ticket preferences.
* pref a b means a is weakly preferred to b. Direct comparisons are represented
  only when site a.1 = site b.1. Values of pref on other pairs are irrelevant.
* calib gives indifference between copies of the same constant lottery at any
  two scenarios of the same site. It gives both directions because its scenario
  arguments range over ordered pairs.
* common compares within-scenario constant-lottery rankings across ALL scenarios,
  including different sites. Do not add an equal-site hypothesis to common.
  This defines one common nondegenerate objective-lottery ranking. mono writes
  that ranking using constant tickets at the current scenario.
* Only ticket mixtures at a fixed scenario are constrained. No continuity,
  affinity, or mixture operation on scenarios or contemplated actions is assumed.
* R s is a probability distribution; zero probabilities are allowed. Its
  uniqueness is identified by the full hypothetical-ticket relations. The
  actual-payoff restriction alone need not identify it.
* The common utility is nonconstant on Lottery X. No separate nonconstancy on
  any particular problem's actual terminal payoffs is required.

## Nonemptiness

The public iff and reverse implication assume Nonempty S. The forward direction
obtains a scenario from Axioms.nondeg. That field also supplies objective
lotteries, which rule out an empty prize type. The common field transfers its
strict constant-lottery comparison to each scenario; an empty terminal type
would make the two constant tickets equal, so every Z s is nonempty. Derive these
facts directly, before constructing probabilities. A Representation itself
supplies objective lotteries through nonconst and terminal lotteries through R.
Do not derive prerequisite facts using the representation theorem being proved.

-/

set_option autoImplicit false

noncomputable section

namespace LotteryChoice

/-! ## Lotteries -/

/-- `C = Δ(X)`: probability distributions on the finite prize set `X`. -/
@[ext]
structure Lottery (X : Type) [Fintype X] where
  prob : X → ℝ
  nonneg : ∀ x, 0 ≤ prob x
  sum_one : ∑ x, prob x = 1

/-- Labelled tickets `(s; g)`: a scenario together with a ticket on its node set. -/
abbrev Ticket (X : Type) [Fintype X] {S : Type} (Z : S → Type) : Type :=
  Σ s : S, (Z s → Lottery X)

variable {X : Type} [Fintype X]

/-- Objective mixture `p_t q = t p + (1 - t) q`. -/
def Lottery.mix (t : unitInterval) (p q : Lottery X) : Lottery X where
  prob x := (t : ℝ) * p.prob x + (1 - (t : ℝ)) * q.prob x
  nonneg x :=
    add_nonneg (mul_nonneg (unitInterval.nonneg t) (p.nonneg x))
      (mul_nonneg (unitInterval.one_minus_nonneg t) (q.nonneg x))
  sum_one := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, p.sum_one, q.sum_one]
    ring

/-- The degenerate lottery on prize `x` (a prize denotes this lottery). -/
def Lottery.pure [DecidableEq X] (x : X) : Lottery X where
  prob y := if y = x then 1 else 0
  nonneg y := by by_cases h : y = x <;> simp [h]
  sum_one := by simp

/-- Coordinatewise mixture of tickets: `(g_t h)(z) = g(z)_t h(z)`. -/
def mixF {N : Type} (t : unitInterval) (g h : N → Lottery X) : N → Lottery X :=
  fun z => Lottery.mix t (g z) (h z)

/-! ## Axioms -/

section Abstract

variable {Site S : Type} {Z : S → Type} [∀ s, Fintype (Z s)] (site : S → Site)

/-- A1–A5. `pref a b` reads `a ≿_I b` for `a, b` at the same site `I`. -/
structure Axioms (pref : Ticket X Z → Ticket X Z → Prop) : Prop where
  /-- A1: complete on each site. -/
  complete : ∀ a b : Ticket X Z, site a.1 = site b.1 → (pref a b ∨ pref b a)
  /-- A1: transitive on each site. -/
  trans : ∀ a b c : Ticket X Z, site a.1 = site b.1 → site b.1 = site c.1 →
    pref a b → pref b c → pref a c
  /-- A2(a): calibration. A constant ticket is indifferent to its copy at any other
  scenario of the same site (both directions, as `s s'` range over ordered pairs). -/
  calib : ∀ s s' : S, site s = site s' → ∀ p : Lottery X,
    pref ⟨s, fun _ => p⟩ ⟨s', fun _ => p⟩
  /-- A2(b): constant tickets rank the same way at every scenario. This is what
  defines `≿₀`; within a site it already follows from A2(a) and A1. -/
  common : ∀ s s' : S, ∀ p q : Lottery X,
    (pref ⟨s, fun _ => p⟩ ⟨s, fun _ => q⟩ ↔ pref ⟨s', fun _ => p⟩ ⟨s', fun _ => q⟩)
  /-- A2(c): nondegeneracy, some `p ≻₀ q`. -/
  nondeg : ∃ (s : S) (p q : Lottery X),
    pref ⟨s, fun _ => p⟩ ⟨s, fun _ => q⟩ ∧ ¬ pref ⟨s, fun _ => q⟩ ⟨s, fun _ => p⟩
  /-- A3: mixture independence at a fixed scenario. -/
  indep : ∀ (s : S) (g h k : Z s → Lottery X) (t : unitInterval),
    0 < (t : ℝ) → (t : ℝ) < 1 →
    (pref ⟨s, g⟩ ⟨s, h⟩ ↔ pref ⟨s, mixF t g k⟩ ⟨s, mixF t h k⟩)
  /-- A4: mixture continuity at a fixed scenario. -/
  cont : ∀ (s : S) (g h k : Z s → Lottery X),
    IsClosed {t : unitInterval | pref ⟨s, mixF t g h⟩ ⟨s, k⟩} ∧
    IsClosed {t : unitInterval | pref ⟨s, k⟩ ⟨s, mixF t g h⟩}
  /-- A5: terminal monotonicity, with `g(z) ≿₀ h(z)` written as the comparison of
  the constant tickets `g z` and `h z` at `s`. -/
  mono : ∀ (s : S) (g h : Z s → Lottery X),
    (∀ z, pref ⟨s, fun _ => g z⟩ ⟨s, fun _ => h z⟩) → pref ⟨s, g⟩ ⟨s, h⟩

/-! ## Representation -/

/-- `∑_{z ∈ Z_s} R_s(z) u(g(z))` for the labelled ticket `a = (s; g)`. -/
def EV (u : Lottery X → ℝ) (R : ∀ s : S, Lottery (Z s)) (a : Ticket X Z) : ℝ :=
  ∑ z, (R a.1).prob z * u (a.2 z)

/-- A lottery choice representation of `{≿_I}`. -/
structure Representation (pref : Ticket X Z → Ticket X Z → Prop) where
  /-- The common utility on `C`. -/
  u : Lottery X → ℝ
  affine : ∀ (t : unitInterval) (p q : Lottery X),
    u (Lottery.mix t p q) = (t : ℝ) * u p + (1 - (t : ℝ)) * u q
  nonconst : ∃ p q : Lottery X, u p ≠ u q
  /-- The subjective lottery `R_s ∈ Δ(Z_s)` at each scenario. -/
  R : ∀ s : S, Lottery (Z s)
  /-- Every same-site comparison of labelled tickets is represented. -/
  represents : ∀ a b : Ticket X Z, site a.1 = site b.1 →
    (pref a b ↔ EV u R b ≤ EV u R a)


end Abstract
end LotteryChoice
end
