import PomdpLogging.FullDataMinimax
import PomdpLogging.ExactLowerBound

noncomputable section
open scoped BigOperators
namespace PomdpLogging

def sampleUpper (k : ℕ) (δ : ℝ) : ℕ :=
  ⌈Real.log (1/(2*δ)) / (-Real.log (1-affinityConstant*survival k))⌉₊

theorem affinity_base_bounds (k : ℕ) :
    0 < 1-affinityConstant*survival k ∧ 1-affinityConstant*survival k < 1 := by
  have hc := affinityConstant_bounds
  have hp := survival_pos k
  have hu := survival_le_third k
  constructor <;> nlinarith

theorem power_confidence {r δ : ℝ} (hr : 0 < r) (hr' : r < 1)
    (hδ : 0 < δ) (n : ℕ)
    (hn : Real.log (1/(2*δ))/(-Real.log r) ≤ n) : r^n/2 ≤ δ := by
  have hl : Real.log r < 0 := Real.log_neg hr hr'
  have hm := (div_le_iff₀ (neg_pos.mpr hl)).mp hn
  rw [one_div, Real.log_inv] at hm
  have hh : Real.log (r^n) ≤ Real.log (2*δ) := by rw [Real.log_pow]; nlinarith
  have hp := (Real.log_le_log_iff (pow_pos hr n) (show 0 < 2*δ by positivity)).mp hh
  linarith

theorem sampleUpper_accurate (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    minimaxRisk k (sampleUpper k δ) ≤ δ := by
  apply (minimax_risk_upper k _).trans
  exact power_confidence (affinity_base_bounds k).1 (affinity_base_bounds k).2 hδ
    _ (Nat.le_ceil _)

def sampleComplexity (k : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : ∃ n, minimaxRisk k n ≤ δ then Nat.find h else 0

theorem sampleComplexity_spec (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    minimaxRisk k (sampleComplexity k δ) ≤ δ := by
  have he : ∃ n, minimaxRisk k n ≤ δ := ⟨sampleUpper k δ, sampleUpper_accurate k hδ⟩
  simp only [sampleComplexity, dif_pos he]
  exact Nat.find_spec he

theorem sampleComplexity_le {k n : ℕ} {δ : ℝ} (hn : minimaxRisk k n ≤ δ) :
    sampleComplexity k δ ≤ n := by
  have he : ∃ n, minimaxRisk k n ≤ δ := ⟨n, hn⟩
  simp only [sampleComplexity, dif_pos he]
  exact Nat.find_min' he hn

theorem accuracy_iff_risk (k n : ℕ) (δ : ℝ) :
    (∃ A : ValueEstimator (Fin n → Episode k × Action),
      A.failure ((fullEpisodeLaw false k).iid n) (1/4) ≤ δ ∧
      A.failure ((fullEpisodeLaw true k).iid n) (3/4) ≤ δ) ↔ minimaxRisk k n ≤ δ := by
  constructor
  · rintro ⟨A, h0, h1⟩
    exact (full_data_minimax_estimator_lower k n A).trans (max_le h0 h1)
  · intro h
    exact ⟨majorityEstimator k n, by rw [(majorityEstimator_errors k n).1]; exact h,
      by rw [(majorityEstimator_errors k n).2]; exact h⟩

/-- Corollary 4.2, the exact sample-complexity sandwich. -/
theorem exact_sample_sandwich (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/2) :
    2*binaryKL (1-δ) δ / (survival k*Real.log 3) ≤ sampleComplexity k δ ∧
      sampleComplexity k δ ≤ sampleUpper k δ := by
  constructor
  · apply exact_estimation_sample_lower k _ (majorityEstimator k _) hδ hδ'
    · rw [(majorityEstimator_errors k _).1]
      exact sampleComplexity_spec k hδ
    · rw [(majorityEstimator_errors k _).2]
      exact sampleComplexity_spec k hδ
  · exact sampleComplexity_le (sampleUpper_accurate k hδ)

end PomdpLogging
