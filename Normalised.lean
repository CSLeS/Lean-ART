import AnthropicRepresentation.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace LotteryChoice
variable {X N : Type} [Fintype X]

@[simp] theorem n_mixF_zero (g h : N → Lottery X) : mixF 0 g h = h := by
  funext z
  apply Lottery.ext
  funext x
  simp [mixF, Lottery.mix]

@[simp] theorem n_mixF_one (g h : N → Lottery X) : mixF 1 g h = g := by
  funext z
  apply Lottery.ext
  funext x
  simp [mixF, Lottery.mix]

@[simp] theorem n_mixF_self (t : unitInterval) (g : N → Lottery X) :
    mixF t g g = g := by
  funext z
  apply Lottery.ext
  funext x
  simp only [mixF, Lottery.mix]
  ring

theorem n_mixF_swap (t : unitInterval) (g h : N → Lottery X) :
    mixF t g h = mixF (unitInterval.symm t) h g := by
  funext z
  apply Lottery.ext
  funext x
  simp only [mixF, Lottery.mix, unitInterval.coe_symm_eq]
  ring

theorem n_mixF_nest (a b c : unitInterval) (hc : (c : ℝ) = (a : ℝ) * (b : ℝ))
    (g h : N → Lottery X) : mixF a (mixF b g h) h = mixF c g h := by
  funext z
  apply Lottery.ext
  funext x
  simp only [mixF, Lottery.mix, hc]
  ring

theorem n_mixF_combine (t a b c : unitInterval)
    (hc : (c : ℝ) = (t : ℝ) * (a : ℝ) + (1 - (t : ℝ)) * (b : ℝ))
    (g h : N → Lottery X) :
    mixF t (mixF a g h) (mixF b g h) = mixF c g h := by
  funext z
  apply Lottery.ext
  funext x
  simp only [mixF, Lottery.mix, hc]
  ring

theorem n_indep_le
    (r : (N → Lottery X) → (N → Lottery X) → Prop)
    (hcomp : ∀ g h, r g h ∨ r h g)
    (hind : ∀ g h k (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      (r g h ↔ r (mixF t g k) (mixF t h k)))
    (g h k : N → Lottery X) (t : unitInterval) (hgh : r g h) :
    r (mixF t g k) (mixF t h k) := by
  by_cases h0 : (t : ℝ) = 0
  · have ht : t = 0 := Subtype.ext h0
    subst t
    simpa using (hcomp k k).elim id id
  by_cases h1 : (t : ℝ) = 1
  · have ht : t = 1 := Subtype.ext h1
    subst t
    simpa using hgh
  exact (hind g h k t (lt_of_le_of_ne t.property.1 (Ne.symm h0))
    (lt_of_le_of_ne t.property.2 h1)).mp hgh

theorem n_mixF_congr_rel
    (r : (N → Lottery X) → (N → Lottery X) → Prop)
    (hcomp : ∀ g h, r g h ∨ r h g)
    (htrans : ∀ g h k, r g h → r h k → r g k)
    (hind : ∀ g h k (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      (r g h ↔ r (mixF t g k) (mixF t h k)))
    (g g' h h' : N → Lottery X) (t : unitInterval)
    (hgg' : r g g') (hhh' : r h h') : r (mixF t g h) (mixF t g' h') := by
  apply htrans _ (mixF t g' h) _
  · exact n_indep_le r hcomp hind g g' h t hgg'
  · rw [n_mixF_swap t g' h, n_mixF_swap t g' h']
    exact n_indep_le r hcomp hind h h' g' (unitInterval.symm t) hhh'

theorem n_benchmark_strict
    (r : (N → Lottery X) → (N → Lottery X) → Prop)
    (hind : ∀ g h k (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      (r g h ↔ r (mixF t g k) (mixF t h k)))
    (top bot : N → Lottery X) (hstrict : ¬ r bot top)
    (a b : unitInterval) (hab : (a : ℝ) < (b : ℝ)) :
    ¬ r (mixF a top bot) (mixF b top bot) := by
  have hbpos : 0 < (b : ℝ) := lt_of_le_of_lt a.property.1 hab
  have hb : ¬ r bot (mixF b top bot) := by
    by_cases hb1 : (b : ℝ) = 1
    · have : b = 1 := Subtype.ext hb1
      simpa [this] using hstrict
    intro h
    apply hstrict
    apply (hind bot top bot b hbpos (lt_of_le_of_ne b.property.2 hb1)).mpr
    simpa using h
  by_cases ha0 : (a : ℝ) = 0
  · have : a = 0 := Subtype.ext ha0
    simpa [this] using hb
  let c : unitInterval := ⟨(a : ℝ) / (b : ℝ),
    ⟨div_nonneg a.property.1 b.property.1, (div_le_one hbpos).mpr (le_of_lt hab)⟩⟩
  have hcpos : 0 < (c : ℝ) := div_pos (lt_of_le_of_ne a.property.1 (Ne.symm ha0)) hbpos
  have hclt : (c : ℝ) < 1 := (div_lt_one hbpos).mpr hab
  have heq : mixF c (mixF b top bot) bot = mixF a top bot := by
    apply n_mixF_nest
    dsimp [c]
    exact (div_mul_cancel₀ (a : ℝ) (ne_of_gt hbpos)).symm
  intro h
  apply hb
  apply (hind bot (mixF b top bot) (mixF b top bot)
    (unitInterval.symm c) (by simpa using sub_pos.mpr hclt)
    (by simpa using sub_lt_self (1 : ℝ) hcpos)).mpr
  rw [← n_mixF_swap c (mixF b top bot) bot, heq, n_mixF_self]
  exact h

/-- A bounded independent continuous ranking has an affine representation,
normalised at any strictly ranked global benchmarks. -/
theorem affine_rep_of_bounded_normalized
    (r : (N → Lottery X) → (N → Lottery X) → Prop)
    (hcomp : ∀ g h, r g h ∨ r h g)
    (htrans : ∀ g h k, r g h → r h k → r g k)
    (hind : ∀ g h k (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      (r g h ↔ r (mixF t g k) (mixF t h k)))
    (hcont : ∀ g h k, IsClosed {t : unitInterval | r (mixF t g h) k} ∧
      IsClosed {t : unitInterval | r k (mixF t g h)})
    (top bot : N → Lottery X)
    (htop : ∀ g, r top g) (hbot : ∀ g, r g bot)
    (hstrict : ¬ r bot top) :
    ∃ W : (N → Lottery X) → ℝ,
      (∀ g h, r g h ↔ W h ≤ W g) ∧
      (∀ (t : unitInterval) (g h : N → Lottery X),
        W (mixF t g h) = (t : ℝ) * W g + (1 - (t : ℝ)) * W h) ∧
      W bot = 0 ∧ W top = 1 ∧
      (∀ g, 0 ≤ W g ∧ W g ≤ 1) := by
  classical
  have hex : ∀ g : N → Lottery X, ∃ t : unitInterval,
      r (mixF t top bot) g ∧ r g (mixF t top bot) := by
    intro g
    obtain ⟨t, _, ht⟩ := (isPreconnected_closed_iff.mp
      (isPreconnected_univ : IsPreconnected (Set.univ : Set unitInterval)))
      {t | r (mixF t top bot) g} {t | r g (mixF t top bot)}
      (hcont top bot g).1 (hcont top bot g).2
      (by intro t _; exact hcomp _ _)
      ⟨1, Set.mem_univ _, by simpa using htop g⟩
      ⟨0, Set.mem_univ _, by simpa using hbot g⟩
    exact ⟨t, ht⟩
  choose w hw using hex
  have hbench : ∀ a b : unitInterval,
      r (mixF a top bot) (mixF b top bot) ↔ (b : ℝ) ≤ (a : ℝ) := by
    intro a b
    constructor
    · intro h
      by_contra hn
      exact n_benchmark_strict r hind top bot hstrict a b (lt_of_not_ge hn) h
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · exact (hcomp _ _).resolve_right
          (n_benchmark_strict r hind top bot hstrict b a hlt)
      · have : a = b := Subtype.ext heq.symm
        subst a
        exact (hcomp _ _).elim id id
  have hrepr : ∀ g h, r g h ↔ ((w h : unitInterval) : ℝ) ≤ (w g : ℝ) := by
    intro g h
    constructor
    · intro hgh
      exact (hbench _ _).mp
        (htrans _ g _ (hw g).1 (htrans _ h _ hgh (hw h).2))
    · intro hgh
      exact htrans _ (mixF (w g) top bot) _ (hw g).2
        (htrans _ (mixF (w h) top bot) _ ((hbench _ _).mpr hgh) (hw h).1)
  have hwbench : ∀ t : unitInterval, (w (mixF t top bot) : ℝ) = (t : ℝ) := by
    intro t
    exact le_antisymm ((hbench _ _).mp (hw (mixF t top bot)).2)
      ((hbench _ _).mp (hw (mixF t top bot)).1)
  refine ⟨fun g => (w g : ℝ), hrepr, ?_, ?_, ?_, fun g => (w g).property⟩
  · intro t g h
    let c : unitInterval := ⟨(t : ℝ) * (w g : ℝ) + (1 - (t : ℝ)) * (w h : ℝ),
      ⟨add_nonneg (mul_nonneg t.property.1 (w g).property.1)
          (mul_nonneg (sub_nonneg.mpr t.property.2) (w h).property.1),
        by nlinarith [(w g).property.2, (w h).property.2,
          mul_nonneg t.property.1 (sub_nonneg.mpr (w g).property.2),
          mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr (w h).property.2)]⟩⟩
    have heq : mixF t (mixF (w g) top bot) (mixF (w h) top bot) = mixF c top bot :=
      n_mixF_combine t (w g) (w h) c rfl top bot
    have h₁ := n_mixF_congr_rel r hcomp htrans hind
      g (mixF (w g) top bot) h (mixF (w h) top bot) t (hw g).2 (hw h).2
    have h₂ := n_mixF_congr_rel r hcomp htrans hind
      (mixF (w g) top bot) g (mixF (w h) top bot) h t (hw g).1 (hw h).1
    rw [heq] at h₁ h₂
    have hwc := le_antisymm ((hrepr _ _).mp h₂) ((hrepr _ _).mp h₁)
    rw [hwbench c] at hwc
    exact hwc
  · simpa using hwbench 0
  · simpa using hwbench 1

end LotteryChoice
end
