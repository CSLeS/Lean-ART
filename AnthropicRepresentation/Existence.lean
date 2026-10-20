import AnthropicRepresentation.Converse
import AnthropicRepresentation.Normalised
import AnthropicRepresentation.Finite
import AnthropicRepresentation.Uniqueness

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace LotteryChoice
variable {X : Type} [Fintype X]
variable {Site S : Type} {Z : S → Type} [∀ s, Fintype (Z s)]
variable (site : S → Site)

/-- Construct the common utility and the scenario probabilities from A1–A5. -/
theorem representation_of_axioms (pref : Ticket X Z → Ticket X Z → Prop)
    (ax : Axioms site pref) : Nonempty (Representation site pref) := by
  classical
  let : Nonempty X := ax.nonempty_prizes site
  let (s : S) : Nonempty (Z s) := ax.nonempty_terminals site s
  obtain ⟨s₀, p₀, q₀, hpq, hqp⟩ := ax.nondeg
  have trans_s (s : S) (g h k : Z s → Lottery X) :=
    ax.trans ⟨s, g⟩ ⟨s, h⟩ ⟨s, k⟩ rfl rfl
  let objective : Lottery X → Lottery X → Prop :=
    fun p q => pref ⟨s₀, fun _ => p⟩ ⟨s₀, fun _ => q⟩
  obtain ⟨top, bot, htop, hbot⟩ := exists_best_worst objective
    (fun p q => ax.complete ⟨s₀, fun _ => p⟩ ⟨s₀, fun _ => q⟩ rfl)
    (fun p q w hpq hqw => trans_s s₀ _ _ _ hpq hqw)
    (fun p q w t ht ht' => ax.indep s₀ (fun _ => p) (fun _ => q) (fun _ => w) t ht ht')
  have hstrict : ¬ objective bot top := by
    intro h
    exact hqp (trans_s s₀ _ _ _ (hbot q₀)
      (trans_s s₀ _ _ _ h (htop p₀)))
  have htop_s (s : S) (g : Z s → Lottery X) : pref ⟨s, fun _ => top⟩ ⟨s, g⟩ := by
    apply ax.mono
    intro z
    exact (ax.common s₀ s top (g z)).mp (htop (g z))
  have hbot_s (s : S) (g : Z s → Lottery X) : pref ⟨s, g⟩ ⟨s, fun _ => bot⟩ := by
    apply ax.mono
    intro z
    exact (ax.common s₀ s (g z) bot).mp (hbot (g z))
  have hstrict_s (s : S) : ¬ pref ⟨s, fun _ => bot⟩ ⟨s, fun _ => top⟩ := by
    intro h
    exact hstrict ((ax.common s₀ s bot top).mpr h)
  have hlocal (s : S) := affine_rep_of_bounded_normalized
    (fun g h : Z s → Lottery X => pref ⟨s, g⟩ ⟨s, h⟩)
    (fun g h => ax.complete ⟨s, g⟩ ⟨s, h⟩ rfl)
    (trans_s s)
    (ax.indep s) (ax.cont s)
    (fun _ => top) (fun _ => bot) (htop_s s) (hbot_s s) (hstrict_s s)
  choose W hW aW Wbot Wtop Wbounds using hlocal
  let u : Lottery X → ℝ := fun p => W s₀ (fun _ => p)
  have hu (p q : Lottery X) : objective p q ↔ u q ≤ u p := hW s₀ _ _
  have au (t : unitInterval) (p q : Lottery X) :
      u (Lottery.mix t p q) = (t : ℝ) * u p + (1 - (t : ℝ)) * u q :=
    aW s₀ t (fun _ => p) (fun _ => q)
  have ubot : u bot = 0 := Wbot s₀
  have utop : u top = 1 := Wtop s₀
  have ubounds (p : Lottery X) : 0 ≤ u p ∧ u p ≤ 1 := Wbounds s₀ (fun _ => p)
  have constants (s : S) (p : Lottery X) : W s (fun _ => p) = u p := by
    apply normalized_constants_agree objective u (W s) top bot hu
      (fun p q => (ax.common s₀ s p q).trans (hW s _ _))
      au (aW s) ubot utop (Wbot s) (Wtop s)
  have profiles (s : S) (g h : Z s → Lottery X)
      (heq : ∀ z, u (g z) = u (h z)) : W s g = W s h := by
    apply le_antisymm
    · apply (hW s h g).mp
      apply ax.mono
      intro z
      apply (ax.common s₀ s (h z) (g z)).mp
      apply (hu _ _).mpr
      exact (heq z).le
    · apply (hW s g h).mp
      apply ax.mono
      intro z
      apply (ax.common s₀ s (g z) (h z)).mp
      apply (hu _ _).mpr
      exact (heq z).ge
  have hprob (s : S) := finite_ticket_representation u (W s) top bot au (aW s)
    ubot utop ubounds (fun g => (Wbounds s g).1) (constants s) (profiles s)
  choose R hR using hprob
  refine ⟨{
    u := u
    affine := au
    nonconst := ?_
    R := R
    represents := ?_ }⟩
  · refine ⟨top, bot, ?_⟩
    rw [utop, ubot]
    norm_num
  · intro a b hab
    obtain ⟨s, g⟩ := a
    obtain ⟨s', h⟩ := b
    change site s = site s' at hab
    let t : unitInterval := ⟨W s' h, Wbounds s' h⟩
    let p : Lottery X := Lottery.mix t top bot
    have hup : u p = W s' h := by
      dsimp [p]
      rw [au, utop, ubot]
      simp [t]
    have heq' : W s' (fun _ => p) = W s' h := (constants s' p).trans hup
    have heq : W s (fun _ => p) = W s' h := (constants s p).trans hup
    have hforward : pref ⟨s', h⟩ ⟨s', fun _ => p⟩ := (hW s' _ _).mpr heq'.le
    have hbackward : pref ⟨s', fun _ => p⟩ ⟨s', h⟩ := (hW s' _ _).mpr heq'.ge
    change pref ⟨s, g⟩ ⟨s', h⟩ ↔
      (∑ z, (R s').prob z * u (h z)) ≤ (∑ z, (R s).prob z * u (g z))
    rw [← hR s' h, ← hR s g]
    constructor
    · intro hgh
      have hc : pref ⟨s, g⟩ ⟨s, fun _ => p⟩ :=
        ax.trans ⟨s, g⟩ ⟨s', h⟩ ⟨s, fun _ => p⟩ hab hab.symm hgh
          (ax.trans ⟨s', h⟩ ⟨s', fun _ => p⟩ ⟨s, fun _ => p⟩
            rfl hab.symm hforward (ax.calib s' s hab.symm p))
      simpa only [heq] using (hW s _ _).mp hc
    · intro hgh
      have hc : pref ⟨s, g⟩ ⟨s, fun _ => p⟩ :=
        (hW s _ _).mpr (by simpa only [heq] using hgh)
      exact ax.trans ⟨s, g⟩ ⟨s, fun _ => p⟩ ⟨s', h⟩ rfl hab hc
        (ax.trans ⟨s, fun _ => p⟩ ⟨s', fun _ => p⟩ ⟨s', h⟩
          hab rfl (ax.calib s s' hab p) hbackward)

end LotteryChoice
end
