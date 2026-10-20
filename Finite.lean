import AnthropicRepresentation.Basic

set_option autoImplicit false
noncomputable section
open scoped unitInterval
namespace LotteryChoice
variable {X : Type} [Fintype X]

/-- Finite mixtures retain arbitrary real probabilities, including zero weights. -/
def Lottery.barycenter {J : Type} [Fintype J]
    (w : Lottery J) (p : J → Lottery X) : Lottery X where
  prob x := ∑ i, w.prob i * (p i).prob x
  nonneg x := Finset.sum_nonneg (fun i _ => mul_nonneg (w.nonneg i) ((p i).nonneg x))
  sum_one := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, Lottery.sum_one, mul_one]

/-- A finite mixture at each terminal, with the same coefficients. -/
def baryF {J N : Type} [Fintype J] (w : Lottery J)
    (g : J → N → Lottery X) : N → Lottery X :=
  fun z => Lottery.barycenter w (fun i => g i z)

/-- Binary affinity determines every finite convex combination. -/
theorem affine_baryF {J N : Type} [Fintype J]
    (W : (N → Lottery X) → ℝ)
    (aW : ∀ (t : unitInterval) (g h : N → Lottery X),
      W (mixF t g h) = (t : ℝ) * W g + (1 - (t : ℝ)) * W h)
    (w : Lottery J) (g : J → N → Lottery X) :
    W (baryF w g) = ∑ i, w.prob i * W (g i) := by
  let graph : Set ((N → X → ℝ) × ℝ) :=
    {v | ∃ h : N → Lottery X, v.1 = (fun z => (h z).prob) ∧ v.2 = W h}
  have hconv : Convex ℝ graph := by
    intro x hx y hy a b ha hb hab
    obtain ⟨p, hp, hpW⟩ := hx
    obtain ⟨q, hq, hqW⟩ := hy
    let t : unitInterval := ⟨a, ha, by linarith⟩
    refine ⟨mixF t p q, ?_, ?_⟩
    · ext z k
      change a * x.1 z k + b * y.1 z k =
        a * (p z).prob k + (1 - a) * (q z).prob k
      rw [hp, hq]
      congr 1
      congr 1
      linarith
    · change a * x.2 + b * y.2 = W (mixF t p q)
      rw [hpW, hqW, aW]
      change a * W p + b * W q = a * W p + (1 - a) * W q
      congr 1
      congr 1
      linarith
  have hmem := hconv.sum_mem (t := Finset.univ) (w := w.prob)
    (z := fun i => ((fun z => (g i z).prob), W (g i)))
    (fun i _ => w.nonneg i) w.sum_one
    (fun i _ => show ((fun z => (g i z).prob), W (g i)) ∈ graph from ⟨g i, rfl, rfl⟩)
  obtain ⟨h, hh, hhW⟩ := hmem
  have hh' : h = baryF w g := by
    funext z
    apply Lottery.ext
    funext k
    have hhzk := congrFun (congrFun hh z) k
    simpa [baryF, Lottery.barycenter, Prod.fst_sum] using hhzk.symm
  rw [hh'] at hhW
  simpa [Prod.snd_sum] using hhW.symm

/-- An affine objective utility preserves finite lottery mixtures. -/
theorem affine_barycenter {J : Type} [Fintype J]
    (u : Lottery X → ℝ)
    (au : ∀ (t : unitInterval) (p q : Lottery X),
      u (Lottery.mix t p q) = (t : ℝ) * u p + (1 - (t : ℝ)) * u q)
    (w : Lottery J) (p : J → Lottery X) :
    u (Lottery.barycenter w p) = ∑ i, w.prob i * u (p i) := by
  exact affine_baryF (N := Unit) (fun g => u (g ()))
    (fun t g h => au t (g ()) (h ())) w (fun i _ => p i)
/-- Normalised affine ticket values determine a probability distribution on
terminals. Only utility profiles affect values; no positivity of individual
terminal probabilities is required. -/
theorem finite_ticket_representation {N : Type} [Fintype N] [Nonempty N]
    (u : Lottery X → ℝ) (W : (N → Lottery X) → ℝ)
    (top bot : Lottery X)
    (au : ∀ (t : unitInterval) (p q : Lottery X),
      u (Lottery.mix t p q) = (t : ℝ) * u p + (1 - (t : ℝ)) * u q)
    (aW : ∀ (t : unitInterval) (g h : N → Lottery X),
      W (mixF t g h) = (t : ℝ) * W g + (1 - (t : ℝ)) * W h)
    (u_bot : u bot = 0) (u_top : u top = 1)
    (hu_bounds : ∀ p, 0 ≤ u p ∧ u p ≤ 1)
    (hW_nonneg : ∀ g, 0 ≤ W g)
    (hconstants : ∀ p, W (fun _ => p) = u p)
    (hprofile : ∀ g h, (∀ z, u (g z) = u (h z)) → W g = W h) :
    ∃ R : Lottery N, ∀ g, W g = ∑ z, R.prob z * u (g z) := by
  classical
  have hn : 0 < (Fintype.card N : ℝ) := by exact_mod_cast Fintype.card_pos
  have hn1 : (1 : ℝ) ≤ Fintype.card N := by exact_mod_cast Fintype.card_pos
  let uniform : Lottery N := {
    prob := fun _ => 1 / Fintype.card N
    nonneg := fun _ => div_nonneg (by norm_num) (le_of_lt hn)
    sum_one := by simp [ne_of_gt hn] }
  let t : unitInterval := ⟨1 / Fintype.card N,
    div_nonneg (by norm_num) (le_of_lt hn), (div_le_one hn).mpr hn1⟩
  let indicator : N → N → Lottery X := fun i z => if z = i then top else bot
  have hformula : ∀ g : N → Lottery X,
      W g = ∑ i, W (indicator i) * u (g i) := by
    intro g
    let tickets : N → N → Lottery X :=
      fun i => mixF ⟨u (g i), hu_bounds (g i)⟩ (indicator i) (fun _ => bot)
    have hprofile_eq : W (mixF t g (fun _ => bot)) = W (baryF uniform tickets) := by
      apply hprofile
      intro z
      change u (Lottery.mix t (g z) bot) =
        u (Lottery.barycenter uniform (fun i => tickets i z))
      rw [au, affine_barycenter u au]
      simp only [u_bot, mul_zero, add_zero]
      have hterm : ∀ i : N, u (tickets i z) = if z = i then u (g i) else 0 := by
        intro i
        dsimp [tickets, mixF]
        rw [au]
        by_cases hzi : z = i <;> simp [indicator, hzi, u_top, u_bot]
      simp_rw [hterm]
      simp [uniform, t]
    rw [aW, hconstants, u_bot, mul_zero, add_zero,
      affine_baryF W aW] at hprofile_eq
    have htermW : ∀ i : N, W (tickets i) = u (g i) * W (indicator i) := by
      intro i
      dsimp [tickets]
      rw [aW, hconstants, u_bot]
      ring
    simp_rw [htermW] at hprofile_eq
    change (1 / (Fintype.card N : ℝ)) * W g =
      ∑ i, (1 / (Fintype.card N : ℝ)) * (u (g i) * W (indicator i)) at hprofile_eq
    rw [← Finset.mul_sum] at hprofile_eq
    have heq := (mul_left_cancel₀ (ne_of_gt (one_div_pos.mpr hn))) hprofile_eq
    simpa [mul_comm] using heq
  have hsum : ∑ i, W (indicator i) = 1 := by
    have h := hformula (fun _ => top)
    simpa [hconstants, u_top] using h.symm
  refine ⟨⟨fun i => W (indicator i), fun i => hW_nonneg _, hsum⟩, ?_⟩
  exact hformula
private theorem finite_mix_self (t : unitInterval) (p : Lottery X) :
    Lottery.mix t p p = p := by
  ext x
  simp only [Lottery.mix]
  ring

private theorem finite_mix_zero (p q : Lottery X) : Lottery.mix 0 p q = q := by
  ext x
  simp [Lottery.mix]

private theorem finite_mix_one (p q : Lottery X) : Lottery.mix 1 p q = p := by
  ext x
  simp [Lottery.mix]

private theorem finite_mix_swap (t : unitInterval) (p q : Lottery X) :
    Lottery.mix t p q = Lottery.mix (σ t) q p := by
  ext x
  simp only [Lottery.mix, unitInterval.coe_symm_eq]
  ring

private theorem finite_mix_bound
    (r : Lottery X → Lottery X → Prop)
    (_hcomp : ∀ p q, r p q ∨ r q p)
    (htrans : ∀ p q w, r p q → r q w → r p w)
    (hind : ∀ p q w (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      (r p q ↔ r (Lottery.mix t p w) (Lottery.mix t q w)))
    (top p q : Lottery X) (hp : r top p) (hq : r top q) (t : unitInterval) :
    r top (Lottery.mix t p q) := by
  by_cases ht0 : (t : ℝ) = 0
  · have ht : t = 0 := Subtype.ext ht0
    simpa [ht, finite_mix_zero] using hq
  by_cases ht1 : (t : ℝ) = 1
  · have ht : t = 1 := Subtype.ext ht1
    simpa [ht, finite_mix_one] using hp
  have hpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht0)
  have hlt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 ht1
  have h₁ : r top (Lottery.mix t top q) := by
    have hs := (hind top q top (σ t) (by simpa using sub_pos.mpr hlt)
      (by simp only [unitInterval.coe_symm_eq]; linarith)).mp hq
    rw [finite_mix_self, ← finite_mix_swap] at hs
    exact hs
  exact htrans _ _ _ h₁ ((hind top p q t hpos hlt).mp hp)

private theorem finite_bound_all
    (r : Lottery X → Lottery X → Prop)
    (hcomp : ∀ p q, r p q ∨ r q p)
    (htrans : ∀ p q w, r p q → r q w → r p w)
    (hind : ∀ p q w (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      (r p q ↔ r (Lottery.mix t p w) (Lottery.mix t q w)))
    [DecidableEq X] (top : Lottery X) (htop : ∀ x, r top (Lottery.pure x)) :
    ∀ p, r top p := by
  let bounded : Set (X → ℝ) := {v | ∃ p : Lottery X, v = p.prob ∧ r top p}
  have hconv : Convex ℝ bounded := by
    intro x hx y hy a b ha hb hab
    obtain ⟨p, hp, hpr⟩ := hx
    obtain ⟨q, hq, hqr⟩ := hy
    let t : unitInterval := ⟨a, ha, by linarith⟩
    refine ⟨Lottery.mix t p q, ?_, finite_mix_bound r hcomp htrans hind top p q hpr hqr t⟩
    ext k
    change a * x k + b * y k = a * p.prob k + (1 - a) * q.prob k
    rw [hp, hq]
    congr 1
    congr 1
    linarith
  intro p
  have hmem := hconv.sum_mem (t := Finset.univ) (w := p.prob)
    (z := fun i => (Lottery.pure i).prob)
    (fun i _ => p.nonneg i) p.sum_one (fun i _ => ⟨Lottery.pure i, rfl, htop i⟩)
  obtain ⟨q, hq, hqr⟩ := hmem
  have hpq : p = q := by
    ext x
    have hx := congrFun hq x
    simpa [Lottery.pure] using hx
  simpa [← hpq] using hqr

private theorem finite_top [Nonempty X] (r : X → X → Prop)
    (hcomp : ∀ x y, r x y ∨ r y x)
    (htrans : ∀ x y z, r x y → r y z → r x z) : ∃ x, ∀ y, r x y := by
  classical
  have h : ∀ s : Finset X, ∃ x, ∀ y ∈ s, r x y := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨Classical.choice ‹Nonempty X›, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨x, hx⟩ := ih
      rcases hcomp a x with hax | hxa
      · refine ⟨a, ?_⟩
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact (hcomp _ _).elim id id
        · exact htrans a x y hax (hx y hy)
      · refine ⟨x, ?_⟩
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hxa
        · exact hx y hy
  obtain ⟨x, hx⟩ := h Finset.univ
  exact ⟨x, fun y => hx y (Finset.mem_univ y)⟩

/-- Completeness, transitivity, and independence bound the full real simplex
by two pure prizes; continuity is unnecessary. -/
theorem exists_best_worst [Nonempty X] (r : Lottery X → Lottery X → Prop)
    (hcomp : ∀ p q, r p q ∨ r q p)
    (htrans : ∀ p q w, r p q → r q w → r p w)
    (hind : ∀ p q w (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      (r p q ↔ r (Lottery.mix t p w) (Lottery.mix t q w))) :
    ∃ top bot : Lottery X, (∀ p, r top p) ∧ (∀ p, r p bot) := by
  classical
  obtain ⟨top, htop⟩ := finite_top (fun x y : X => r (Lottery.pure x) (Lottery.pure y))
    (fun x y => hcomp _ _) (fun x y z => htrans _ _ _)
  obtain ⟨bot, hbot⟩ := finite_top (fun x y : X => r (Lottery.pure y) (Lottery.pure x))
    (fun x y => (hcomp _ _).symm) (fun x y z hxy hyz => htrans _ _ _ hyz hxy)
  refine ⟨Lottery.pure top, Lottery.pure bot, finite_bound_all r hcomp htrans hind _ htop, ?_⟩
  exact finite_bound_all (fun p q => r q p) (fun p q => (hcomp p q).symm)
    (fun p q w hpq hqw => htrans w q p hqw hpq)
    (fun p q w t ht0 ht1 => hind q p w t ht0 ht1) _ hbot

end LotteryChoice
end






