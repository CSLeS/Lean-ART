import AnthropicRepresentation.Basic

set_option autoImplicit false
noncomputable section
namespace LotteryChoice
variable {X : Type} [Fintype X]
variable {Site S : Type} {Z : S → Type} [∀ s, Fintype (Z s)]
variable (site : S → Site)

omit [∀ s, Fintype (Z s)] in
theorem Axioms.nonempty_scenarios {pref : Ticket X Z → Ticket X Z → Prop}
    (ax : Axioms site pref) : Nonempty S := by
  obtain ⟨s, _⟩ := ax.nondeg
  exact ⟨s⟩

omit [∀ s, Fintype (Z s)] in
theorem Axioms.nonempty_prizes {pref : Ticket X Z → Ticket X Z → Prop}
    (ax : Axioms site pref) : Nonempty X := by
  obtain ⟨s, p, q, hp, hq⟩ := ax.nondeg
  by_contra h
  have : IsEmpty X := not_nonempty_iff.mp h
  have := p.sum_one
  simp at this

omit [∀ s, Fintype (Z s)] in
theorem Axioms.nonempty_terminals {pref : Ticket X Z → Ticket X Z → Prop}
    (ax : Axioms site pref) (s : S) : Nonempty (Z s) := by
  obtain ⟨s₀, p, q, hp, hq⟩ := ax.nondeg
  by_contra h
  have : IsEmpty (Z s) := not_nonempty_iff.mp h
  have heq : (fun _ : Z s => p) = (fun _ : Z s => q) := funext fun z => isEmptyElim z
  have hp' := (ax.common s₀ s p q).mp hp
  have hq' := (ax.common s₀ s q p).not.mp hq
  apply hq'
  simpa only [heq] using hp'

theorem EV_constant (u : Lottery X → ℝ) (R : ∀ s : S, Lottery (Z s))
    (s : S) (p : Lottery X) : EV u R ⟨s, fun _ => p⟩ = u p := by
  simp only [EV, ← Finset.sum_mul, (R s).sum_one, one_mul]

theorem EV_mixture (u : Lottery X → ℝ) (R : ∀ s : S, Lottery (Z s))
    (hu : ∀ (t : unitInterval) (p q : Lottery X),
      u (Lottery.mix t p q) = (t : ℝ) * u p + (1 - (t : ℝ)) * u q)
    (s : S) (t : unitInterval) (g h : Z s → Lottery X) :
    EV u R ⟨s, mixF t g h⟩ =
      (t : ℝ) * EV u R ⟨s, g⟩ + (1 - (t : ℝ)) * EV u R ⟨s, h⟩ := by
  simp only [EV, mixF, hu, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

theorem EV_affine_transform (u : Lottery X → ℝ)
    (R : ∀ s : S, Lottery (Z s)) (a b : ℝ) (g : Ticket X Z) :
    EV (fun p => a * u p + b) R g = a * EV u R g + b := by
  simp only [EV, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    (R g.1).sum_one, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intros
  ring

theorem axioms_of_representation [Nonempty S] (pref : Ticket X Z → Ticket X Z → Prop)
    (rep : Representation site pref) : Axioms site pref := by
  classical
  constructor
  · intro a b hab
    exact (le_total (EV rep.u rep.R b) (EV rep.u rep.R a)).imp
      ((rep.represents a b hab).mpr) ((rep.represents b a hab.symm).mpr)
  · intro a b c hab hbc hp hq
    exact (rep.represents a c (hab.trans hbc)).mpr
      (le_trans ((rep.represents b c hbc).mp hq) ((rep.represents a b hab).mp hp))
  · intro s s' h p
    apply (rep.represents _ _ h).mpr
    simp only [EV_constant]
    exact le_refl _
  · intro s s' p q
    rw [rep.represents ⟨s, fun _ => p⟩ ⟨s, fun _ => q⟩ rfl,
      rep.represents ⟨s', fun _ => p⟩ ⟨s', fun _ => q⟩ rfl]
    simp only [EV_constant]
  · obtain ⟨p, q, hpq⟩ := rep.nonconst
    let s : S := Classical.choice inferInstance
    rcases lt_or_gt_of_ne hpq with hpq | hpq
    · refine ⟨s, q, p, ?_, ?_⟩
      · apply (rep.represents ⟨s, fun _ => q⟩ ⟨s, fun _ => p⟩ rfl).mpr
        simpa only [EV_constant] using hpq.le
      · intro h
        have := (rep.represents ⟨s, fun _ => p⟩ ⟨s, fun _ => q⟩ rfl).mp h
        simp only [EV_constant] at this
        exact (not_le_of_gt hpq) this
    · refine ⟨s, p, q, ?_, ?_⟩
      · apply (rep.represents ⟨s, fun _ => p⟩ ⟨s, fun _ => q⟩ rfl).mpr
        simpa only [EV_constant] using hpq.le
      · intro h
        have := (rep.represents ⟨s, fun _ => q⟩ ⟨s, fun _ => p⟩ rfl).mp h
        simp only [EV_constant] at this
        exact (not_le_of_gt hpq) this
  · intro s g h k t ht ht'
    rw [rep.represents ⟨s, g⟩ ⟨s, h⟩ rfl,
      rep.represents ⟨s, mixF t g k⟩ ⟨s, mixF t h k⟩ rfl,
      EV_mixture _ _ rep.affine, EV_mixture _ _ rep.affine]
    exact (add_le_add_iff_right _).trans (mul_le_mul_iff_right₀ ht) |>.symm
  · intro s g h k
    have hc : Continuous (fun t : unitInterval =>
        (t : ℝ) * EV rep.u rep.R ⟨s, g⟩ +
          (1 - (t : ℝ)) * EV rep.u rep.R ⟨s, h⟩) := by fun_prop
    have he (t : unitInterval) := EV_mixture rep.u rep.R rep.affine s t g h
    simp_rw [rep.represents ⟨s, mixF _ g h⟩ ⟨s, k⟩ rfl,
      rep.represents ⟨s, k⟩ ⟨s, mixF _ g h⟩ rfl, he]
    exact ⟨isClosed_le continuous_const hc, isClosed_le hc continuous_const⟩
  · intro s g h hp
    apply (rep.represents ⟨s, g⟩ ⟨s, h⟩ rfl).mpr
    apply Finset.sum_le_sum
    intro z hz
    apply mul_le_mul_of_nonneg_left _ ((rep.R s).nonneg z)
    have := (rep.represents ⟨s, fun _ => g z⟩ ⟨s, fun _ => h z⟩ rfl).mp (hp z)
    simpa only [EV_constant] using this

def Representation.positiveAffine {pref : Ticket X Z → Ticket X Z → Prop}
    (rep : Representation site pref) (a b : ℝ) (ha : 0 < a) :
    Representation site pref where
  u p := a * rep.u p + b
  affine := by
    intro t p q
    rw [rep.affine]
    ring
  nonconst := by
    obtain ⟨p, q, hpq⟩ := rep.nonconst
    refine ⟨p, q, ?_⟩
    intro he
    apply hpq
    exact (mul_left_cancel₀ (ne_of_gt ha)) (add_right_cancel he)
  R := rep.R
  represents := by
    intro g h hsite
    rw [rep.represents _ _ hsite, EV_affine_transform, EV_affine_transform]
    exact ((add_le_add_iff_right b).trans (mul_le_mul_iff_right₀ ha)).symm

@[simp] theorem Representation.positiveAffine_u {pref : Ticket X Z → Ticket X Z → Prop}
    (rep : Representation site pref) (a b : ℝ) (ha : 0 < a) (p : Lottery X) :
    (Representation.positiveAffine site rep a b ha).u p = a * rep.u p + b := rfl

@[simp] theorem Representation.positiveAffine_R {pref : Ticket X Z → Ticket X Z → Prop}
    (rep : Representation site pref) (a b : ℝ) (ha : 0 < a) :
    (Representation.positiveAffine site rep a b ha).R = rep.R := rfl

end LotteryChoice
end
