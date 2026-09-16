import PomdpLogging.Majority
import PomdpLogging.Affinity
import PomdpLogging.TestingEstimator

noncomputable section
open scoped BigOperators
namespace PomdpLogging

theorem likelihoodDecision_of_ratio {p q r s : ℝ} (hq : 0 < q) (hs : 0 < s)
    (he : p/q = r/s) : likelihoodDecision p q = likelihoodDecision r s := by
  have hlt : p < q ↔ r < s := by rw [← div_lt_one hq, he, div_lt_one hs]
  have hgt : q < p ↔ s < r := by rw [← one_lt_div hq, he, one_lt_div hs]
  simp only [likelihoodDecision, hlt, hgt]

theorem full_dataset_ratio (k n : ℕ) (xs : Fin n → Episode k × Action) :
    ((fullEpisodeLaw false k).iid n).mass xs / ((fullEpisodeLaw true k).iid n).mass xs =
      ((symbolLaw false k).iid n).mass (compressDataset xs) /
        ((symbolLaw true k).iid n).mass (compressDataset xs) := by
  change (∏ i, (fullEpisodeLaw false k).mass (xs i)) /
      (∏ i, (fullEpisodeLaw true k).mass (xs i)) =
    (∏ i, (symbolLaw false k).mass (compressFull (xs i))) /
      (∏ i, (symbolLaw true k).mass (compressFull (xs i)))
  simp only [← Finset.prod_div_distrib]
  simp_rw [full_likelihood_ratio]

theorem full_likelihood_compresses (k n : ℕ) (xs : Fin n → Episode k × Action) :
    (likelihoodTest ((fullEpisodeLaw false k).iid n) ((fullEpisodeLaw true k).iid n)).one xs =
      (likelihoodTest ((symbolLaw false k).iid n) ((symbolLaw true k).iid n)).one
        (compressDataset xs) :=
  likelihoodDecision_of_ratio
    (Law.iid_mass_pos _ (full_episode_mass_pos true k) n xs)
    (Law.iid_mass_pos _ (symbol_mass_pos true k) n (compressDataset xs))
    (full_dataset_ratio k n xs)

theorem full_likelihood_errors (k n : ℕ) :
    (likelihoodTest ((fullEpisodeLaw false k).iid n) ((fullEpisodeLaw true k).iid n)).errorZero
      ((fullEpisodeLaw false k).iid n) = minimaxRisk k n ∧
    (likelihoodTest ((fullEpisodeLaw false k).iid n) ((fullEpisodeLaw true k).iid n)).errorOne
      ((fullEpisodeLaw true k).iid n) = minimaxRisk k n := by
  have hb := balanced_likelihood_risk _ _ (symbol_likelihood_balanced k n)
  constructor
  · unfold Test.errorZero
    change ((fullEpisodeLaw false k).iid n).expect (fun xs =>
      (likelihoodTest ((fullEpisodeLaw false k).iid n) ((fullEpisodeLaw true k).iid n)).one xs) = _
    simp_rw [full_likelihood_compresses]
    rw [full_dataset_compression_expect false k n
      (likelihoodTest ((symbolLaw false k).iid n) ((symbolLaw true k).iid n)).one]
    exact hb.1
  · unfold Test.errorOne
    simp_rw [full_likelihood_compresses]
    rw [full_dataset_compression_expect true k n
      (fun ws => 1-(likelihoodTest ((symbolLaw false k).iid n) ((symbolLaw true k).iid n)).one ws)]
    exact hb.2.1

/-- The minimax risk is attained on the full observed data. -/
theorem full_data_minimax_test (k n : ℕ) (T : Test (Fin n → Episode k × Action)) :
    minimaxRisk k n ≤ T.worstError ((fullEpisodeLaw false k).iid n)
      ((fullEpisodeLaw true k).iid n) := by
  have he := full_likelihood_errors k n
  have h := balanced_likelihood_minimax _ _ (he.1.trans he.2.symm) T
  simpa only [Test.worstError, he.1, he.2, max_self] using h

theorem full_data_minimax_estimator_lower (k n : ℕ)
    (A : ValueEstimator (Fin n → Episode k × Action)) :
    minimaxRisk k n ≤ max (A.failure ((fullEpisodeLaw false k).iid n) (1/4))
      (A.failure ((fullEpisodeLaw true k).iid n) (3/4)) := by
  exact (full_data_minimax_test k n A.thresholdTest).trans
    (max_le_max (A.threshold_error_zero _) (A.threshold_error_one _))

def majorityEstimator (k n : ℕ) : ValueEstimator (Fin n → Episode k × Action) :=
  (likelihoodTest ((fullEpisodeLaw false k).iid n) ((fullEpisodeLaw true k).iid n)).valueEstimator

theorem majorityEstimator_errors (k n : ℕ) :
    (majorityEstimator k n).failure ((fullEpisodeLaw false k).iid n) (1/4) = minimaxRisk k n ∧
    (majorityEstimator k n).failure ((fullEpisodeLaw true k).iid n) (3/4) = minimaxRisk k n := by
  unfold majorityEstimator
  rw [Test.valueEstimator_failure_zero, Test.valueEstimator_failure_one]
  exact full_likelihood_errors k n

/-- Theorem 5.2: exact minimax characterization, expressed without an infimum:
every estimator has at least this risk, and the stated estimator attains it. -/
theorem exact_full_data_minimax (k n : ℕ) :
    (∀ A : ValueEstimator (Fin n → Episode k × Action),
      minimaxRisk k n ≤ max (A.failure ((fullEpisodeLaw false k).iid n) (1/4))
        (A.failure ((fullEpisodeLaw true k).iid n) (3/4))) ∧
    ((majorityEstimator k n).failure ((fullEpisodeLaw false k).iid n) (1/4) = minimaxRisk k n ∧
      (majorityEstimator k n).failure ((fullEpisodeLaw true k).iid n) (3/4) = minimaxRisk k n) :=
  ⟨full_data_minimax_estimator_lower k n, majorityEstimator_errors k n⟩

theorem minimax_risk_lower (k n : ℕ) : (1-survival k)^n/2 ≤ minimaxRisk k n := by
  have h := reduced_experiment_lower k n
    (likelihoodTest ((symbolLaw false k).iid n) ((symbolLaw true k).iid n))
  rw [(balanced_likelihood_risk _ _ (symbol_likelihood_balanced k n)).2.2] at h
  exact h

theorem minimax_risk_upper (k n : ℕ) :
    minimaxRisk k n ≤ (1-affinityConstant*survival k)^n/2 := by
  have h := overlapRisk_le_affinity ((symbolLaw false k).iid n) ((symbolLaw true k).iid n)
  rw [Law.affinity_iid, symbol_affinity] at h
  exact h

end PomdpLogging
