import AnthropicRepresentation.Basic

set_option autoImplicit false
noncomputable section
namespace LotteryChoice

/-- Affine real-valued functions inducing the same weak order differ by one
positive affine transformation, including on empty and constant domains. -/
theorem affine_order_unique {D : Type} (mix : unitInterval → D → D → D)
    (W W' : D → ℝ)
    (horder : ∀ g h, W g ≤ W h ↔ W' g ≤ W' h)
    (aW : ∀ t g h, W (mix t g h) = (t : ℝ) * W g + (1 - (t : ℝ)) * W h)
    (aW' : ∀ t g h, W' (mix t g h) = (t : ℝ) * W' g + (1 - (t : ℝ)) * W' h) :
    ∃ a b : ℝ, 0 < a ∧ ∀ g, W' g = a * W g + b := by
  classical
  have heq : ∀ g h, W g = W h → W' g = W' h := by
    intro g h hgh
    exact le_antisymm ((horder g h).mp hgh.le) ((horder h g).mp hgh.ge)
  have segment : ∀ x y z, W x < W z → W x ≤ W y → W y ≤ W z →
      (W' y - W' x) * (W z - W x) = (W y - W x) * (W' z - W' x) := by
    intro x y z hxz hxy hyz
    have hden : 0 < W z - W x := sub_pos.mpr hxz
    let t : unitInterval := ⟨(W y - W x) / (W z - W x),
      div_nonneg (sub_nonneg.mpr hxy) hden.le,
      (div_le_one hden).mpr (by linarith)⟩
    have hm : W (mix t z x) = W y := by
      rw [aW]
      dsimp [t]
      field_simp [ne_of_gt hden]
      nlinarith
    have hm' := heq (mix t z x) y hm
    rw [aW'] at hm'
    dsimp [t] at hm'
    field_simp [ne_of_gt hden] at hm'
    nlinarith
  by_cases hconstant : ∀ g h, W g = W h
  · by_cases hD : Nonempty D
    · let g₀ : D := Classical.choice hD
      refine ⟨1, W' g₀ - W g₀, by norm_num, ?_⟩
      intro g
      rw [heq g g₀ (hconstant g g₀), hconstant g g₀]
      ring
    · refine ⟨1, 0, by norm_num, ?_⟩
      intro g
      exact (hD ⟨g⟩).elim
  · push Not at hconstant
    obtain ⟨g, h, hgh⟩ := hconstant
    have hex : ∃ p q, W q < W p := by
      rcases lt_or_gt_of_ne hgh with hlt | hlt
      · exact ⟨h, g, hlt⟩
      · exact ⟨g, h, hlt⟩
    obtain ⟨p, q, hqp⟩ := hex
    have hqp' : W' q < W' p := by
      apply lt_of_le_of_ne ((horder q p).mp hqp.le)
      intro he
      have := (horder p q).mpr he.ge
      linarith
    have hden : 0 < W p - W q := sub_pos.mpr hqp
    have cross : ∀ g, (W' g - W' q) * (W p - W q) =
        (W g - W q) * (W' p - W' q) := by
      intro g
      by_cases hqg : W q ≤ W g
      · by_cases hgp : W g ≤ W p
        · exact segment q g p hqp hqg hgp
        · have hpg : W p < W g := lt_of_not_ge hgp
          have := segment q p g (hqp.trans hpg) hqp.le hpg.le
          nlinarith
      · have hgq : W g < W q := lt_of_not_ge hqg
        have := segment g q p (hgq.trans hqp) hgq.le hqp.le
        nlinarith
    refine ⟨(W' p - W' q) / (W p - W q),
      W' q - ((W' p - W' q) / (W p - W q)) * W q,
      div_pos (sub_pos.mpr hqp') hden, ?_⟩
    intro g
    have hc := cross g
    field_simp [ne_of_gt hden]
    nlinarith

variable {X : Type} [Fintype X]

theorem affine_rep_unique {N : Type}
    (r : (N → Lottery X) → (N → Lottery X) → Prop)
    (W W' : (N → Lottery X) → ℝ)
    (hW : ∀ g h, r g h ↔ W h ≤ W g) (hW' : ∀ g h, r g h ↔ W' h ≤ W' g)
    (aW : ∀ (t : unitInterval) (g h : N → Lottery X),
      W (mixF t g h) = (t : ℝ) * W g + (1 - (t : ℝ)) * W h)
    (aW' : ∀ (t : unitInterval) (g h : N → Lottery X),
      W' (mixF t g h) = (t : ℝ) * W' g + (1 - (t : ℝ)) * W' h) :
    ∃ a b : ℝ, 0 < a ∧ ∀ g, W' g = a * W g + b :=
  affine_order_unique mixF W W' (fun g h => (hW h g).symm.trans (hW' h g)) aW aW'

theorem normalized_constants_agree {N : Type}
    (r : Lottery X → Lottery X → Prop)
    (u : Lottery X → ℝ) (W : (N → Lottery X) → ℝ)
    (top bot : Lottery X)
    (hu : ∀ p q, r p q ↔ u q ≤ u p)
    (hW : ∀ p q, r p q ↔ W (fun _ => q) ≤ W (fun _ => p))
    (au : ∀ (t : unitInterval) (p q : Lottery X),
      u (Lottery.mix t p q) = (t : ℝ) * u p + (1 - (t : ℝ)) * u q)
    (aW : ∀ (t : unitInterval) (g h : N → Lottery X),
      W (mixF t g h) = (t : ℝ) * W g + (1 - (t : ℝ)) * W h)
    (u_bot : u bot = 0) (u_top : u top = 1)
    (W_bot : W (fun _ => bot) = 0) (W_top : W (fun _ => top) = 1) :
    ∀ p : Lottery X, W (fun _ => p) = u p := by
  obtain ⟨a, b, ha, hab⟩ := affine_order_unique Lottery.mix u
    (fun p => W (fun _ => p)) (fun p q => (hu q p).symm.trans (hW q p))
    au (fun t p q => aW t (fun _ => p) (fun _ => q))
  have hb := hab bot
  have ha := hab top
  rw [u_bot, W_bot] at hb
  rw [u_top, W_top] at ha
  have hb0 : b = 0 := by linarith
  have ha1 : a = 1 := by linarith
  intro p
  simpa [ha1, hb0] using hab p

end LotteryChoice
end

namespace LotteryChoice
noncomputable section
variable {X : Type} [Fintype X]
variable {Site S : Type} {Z : S → Type} [∀ s, Fintype (Z s)]

@[simp] theorem EV_const (u : Lottery X → ℝ) (R : ∀ s : S, Lottery (Z s))
    (s : S) (p : Lottery X) : EV u R ⟨s, fun _ => p⟩ = u p := by
  simp only [EV, ← Finset.sum_mul, (R s).sum_one, one_mul]

theorem Lottery.prob_le_one {N : Type} [Fintype N] (p : Lottery N) (n : N) :
    p.prob n ≤ 1 := by
  classical
  calc
    p.prob n ≤ ∑ i, p.prob i := Finset.single_le_sum (fun i _ => p.nonneg i) (Finset.mem_univ n)
    _ = 1 := p.sum_one

theorem EV_indicator (u : Lottery X → ℝ) (R : ∀ s : S, Lottery (Z s))
    (s : S) (z : Z s) (p q : Lottery X) [DecidableEq (Z s)] :
    EV u R ⟨s, fun i => if i = z then p else q⟩ =
      (R s).prob z * u p + (1 - (R s).prob z) * u q := by
  unfold EV
  have hpoint : ∀ i : Z s, (R s).prob i * u (if i = z then p else q) =
      (if i = z then (R s).prob z * (u p - u q) else 0) + (R s).prob i * u q := by
    intro i
    by_cases hi : i = z
    · subst i
      simp only [if_true]
      ring
    · simp [hi]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul,
    (R s).sum_one, one_mul]
  ring

variable (site : S → Site)

theorem u_unique [Nonempty S] {pref : Ticket X Z → Ticket X Z → Prop}
    (r r' : Representation site pref) :
    ∃ a b : ℝ, 0 < a ∧ ∀ p : Lottery X, r'.u p = a * r.u p + b := by
  let s : S := Classical.choice ‹Nonempty S›
  apply affine_order_unique Lottery.mix r.u r'.u ?_ r.affine r'.affine
  intro p q
  have h := (r.represents ⟨s, fun _ => q⟩ ⟨s, fun _ => p⟩ rfl).symm.trans
    (r'.represents ⟨s, fun _ => q⟩ ⟨s, fun _ => p⟩ rfl)
  simpa only [EV_const] using h

theorem R_unique {pref : Ticket X Z → Ticket X Z → Prop}
    (r r' : Representation site pref) (s : S) : r.R s = r'.R s := by
  classical
  obtain ⟨p, q, hpq⟩ := r.nonconst
  have hequal : ∀ a b : Ticket X Z, site a.1 = site b.1 →
      EV r.u r.R a = EV r.u r.R b → EV r'.u r'.R a = EV r'.u r'.R b := by
    intro a b hab he
    apply le_antisymm
    · exact (r'.represents b a hab.symm).mp ((r.represents b a hab.symm).mpr he.le)
    · exact (r'.represents a b hab).mp ((r.represents a b hab).mpr he.ge)
  have hpq' : r'.u p ≠ r'.u q := by
    intro hpq'
    have h₁ := (r.represents ⟨s, fun _ => p⟩ ⟨s, fun _ => q⟩ rfl).mp
      ((r'.represents ⟨s, fun _ => p⟩ ⟨s, fun _ => q⟩ rfl).mpr
        (by simpa only [EV_const] using hpq'.ge))
    have h₂ := (r.represents ⟨s, fun _ => q⟩ ⟨s, fun _ => p⟩ rfl).mp
      ((r'.represents ⟨s, fun _ => q⟩ ⟨s, fun _ => p⟩ rfl).mpr
        (by simpa only [EV_const] using hpq'.le))
    simp only [EV_const] at h₁ h₂
    exact hpq (le_antisymm h₂ h₁)
  apply Lottery.ext
  funext z
  let t : unitInterval := ⟨(r.R s).prob z, (r.R s).nonneg z, (r.R s).prob_le_one z⟩
  have h₀ : EV r.u r.R ⟨s, fun i => if i = z then p else q⟩ =
      EV r.u r.R ⟨s, fun _ => Lottery.mix t p q⟩ := by
    rw [EV_indicator, EV_const, r.affine]
  have h := hequal ⟨s, fun i => if i = z then p else q⟩
    ⟨s, fun _ => Lottery.mix t p q⟩ rfl h₀
  rw [EV_indicator, EV_const, r'.affine] at h
  dsimp [t] at h
  have hmul : ((r.R s).prob z - (r'.R s).prob z) * (r'.u p - r'.u q) = 0 := by
    nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hpq'))

end
end LotteryChoice


