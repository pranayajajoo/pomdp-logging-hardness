import PomdpLogging.SampleComplexity

noncomputable section
open scoped BigOperators
namespace PomdpLogging

theorem confidence_log_split {δ : ℝ} (hδ : 0 < δ) :
    Real.log (1/(2*δ)) = Real.log (1/δ)-Real.log 2 := by
  rw [Real.log_div one_ne_zero (mul_pos (by norm_num) hδ).ne',
    Real.log_div one_ne_zero hδ.ne', Real.log_mul (by norm_num) hδ.ne', Real.log_one]
  ring

theorem confidence_logs {δ : ℝ} (hδ : 0 < δ) (hu : δ ≤ 1/4) :
    1 ≤ Real.log (1/δ) ∧ Real.log (1/δ)/2 ≤ Real.log (1/(2*δ)) ∧
      Real.log (1/(2*δ)) ≤ Real.log (1/δ) := by
  have hi : (4 : ℝ) ≤ 1/δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hl := Real.log_le_log (show (0 : ℝ) < 4 by norm_num) hi
  have hfour : Real.log (4 : ℝ) = 2*Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  rw [hfour] at hl
  have htwo := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at htwo
  rw [confidence_log_split hδ]
  constructor
  · linarith
  constructor <;> linarith

theorem erasure_log_bound (k : ℕ) : -Real.log (1-survival k) ≤ (3/2)*survival k := by
  have hp := survival_pos k
  have hu := survival_le_third k
  have hr : 0 < 1-survival k := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hr
  have hi : (1-survival k)⁻¹ ≤ 1+(3/2)*survival k := by
    rw [← one_div]
    apply (div_le_iff₀ hr).mpr
    nlinarith [mul_nonneg hp.le (show 0 ≤ 1/3-survival k by linarith)]
  linarith

theorem sample_rate_lower (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hu : δ ≤ 1/4) :
    Real.log (1/δ)/(3*survival k) ≤ sampleComplexity k δ := by
  let n := sampleComplexity k δ
  have h := (minimax_risk_lower k n).trans (sampleComplexity_spec k hδ)
  have hr : 0 < 1-survival k := by linarith [survival_le_third k]
  have hh : (1-survival k)^n ≤ 2*δ := by linarith
  have hlog := Real.log_le_log (pow_pos hr n) hh
  rw [Real.log_pow] at hlog
  have hsplit : Real.log (1/(2*δ)) = -Real.log (2*δ) := by
    rw [one_div, Real.log_inv]
  have hc := (confidence_logs hδ hu).2.1
  rw [hsplit] at hc
  have hb := mul_le_mul_of_nonneg_left (erasure_log_bound k) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  apply (div_le_iff₀ (mul_pos (by norm_num) (survival_pos k))).mpr
  change Real.log (1/δ) ≤ (n : ℝ)*(3*survival k)
  nlinarith

theorem sample_rate_upper (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hu : δ ≤ 1/4) :
    (sampleComplexity k δ : ℝ) ≤ 9*Real.log (1/δ)/survival k := by
  let p := survival k
  let L := Real.log (1/δ)
  let D := -Real.log (1-affinityConstant*p)
  let X := Real.log (1/(2*δ))/D
  have hp : 0 < p := survival_pos k
  have hpu : p ≤ 1/3 := survival_le_third k
  have hc := confidence_logs hδ hu
  have hL : 1 ≤ L := hc.1
  have hD : p/8 ≤ D := by
    have ht := Real.log_le_sub_one_of_pos (affinity_base_bounds k).1
    have ha := affinityConstant_bounds
    dsimp [D, p]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha.1) (survival_pos k).le]
  have hDp : 0 < D := by linarith
  have hx0 : 0 ≤ X := by dsimp [X]; exact div_nonneg (by linarith [hc.2.1]) hDp.le
  have hx : X ≤ 8*L/p := by
    apply (div_le_iff₀ hDp).mpr
    have hm := mul_le_mul_of_nonneg_left hD (show 0 ≤ 8*L/p by positivity)
    have he : (8*L/p)*(p/8) = L := by field_simp
    rw [he] at hm
    exact hc.2.2.trans hm
  have hceil := (Nat.ceil_lt_add_one hx0).le
  have hn : (sampleComplexity k δ : ℝ) ≤ (sampleUpper k δ : ℝ) :=
    Nat.cast_le.mpr (sampleComplexity_le (sampleUpper_accurate k hδ))
  change (sampleComplexity k δ : ℝ) ≤ 9*L/p
  change (sampleComplexity k δ : ℝ) ≤ (⌈X⌉₊ : ℝ) at hn
  have hr : 1 ≤ L/p := (le_div_iff₀ hp).mpr (by linarith)
  have halg : 8*L/p + L/p = 9*L/p := by ring
  linarith

theorem survival_growth (k : ℕ) : survival k*(3/2 : ℝ)^(k+2) = 3/4 := by
  have hpow : (2/3 : ℝ)^k*(3/2 : ℝ)^k = 1 := by rw [← mul_pow]; norm_num
  unfold survival
  rw [pow_add]
  norm_num
  nlinarith

/-- Explicit universal constants establish the claimed uniform Theta rate. -/
theorem uniform_sample_rate (H : ℕ) (hH : 3 ≤ H) {δ : ℝ}
    (hδ : 0 < δ) (hu : δ ≤ 1/4) :
    (4/9 : ℝ)*(3/2 : ℝ)^H*Real.log (1/δ) ≤ sampleComplexity (H-2) δ ∧
      (sampleComplexity (H-2) δ : ℝ) ≤ 12*(3/2 : ℝ)^H*Real.log (1/δ) := by
  have hg := survival_growth (H-2)
  rw [show H-2+2 = H by omega] at hg
  have hp := (survival_pos (H-2)).ne'
  have hlo : Real.log (1/δ)/(3*survival (H-2)) =
      (4/9 : ℝ)*(3/2 : ℝ)^H*Real.log (1/δ) := by
    apply (div_eq_iff (mul_ne_zero (by norm_num) hp)).mpr
    nlinarith [congrArg (fun x : ℝ => x*Real.log (1/δ)) hg]
  have hhi : 9*Real.log (1/δ)/survival (H-2) =
      12*(3/2 : ℝ)^H*Real.log (1/δ) := by
    apply (div_eq_iff hp).mpr
    nlinarith [congrArg (fun x : ℝ => x*Real.log (1/δ)) hg]
  constructor
  · rw [← hlo]
    exact sample_rate_lower (H-2) hδ hu
  · rw [← hhi]
    exact sample_rate_upper (H-2) hδ hu

end PomdpLogging
