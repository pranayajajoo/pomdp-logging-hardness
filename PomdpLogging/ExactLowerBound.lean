import PomdpLogging.TestingInformation
import PomdpLogging.ProductInformation
import PomdpLogging.FullDataLowerBound

noncomputable section
open scoped BigOperators
namespace PomdpLogging

def Test.complement {α : Type*} (T : Test α) : Test α where
  one x := 1-T.one x
  nonneg x := sub_nonneg.mpr (T.le_one x)
  le_one x := by linarith [T.nonneg x]

theorem Test.expect_complement {α : Type*} [Fintype α] (T : Test α) (P : Law α) :
    P.expect T.complement.one = 1-P.expect T.one := by
  simp [Test.complement, Law.expect, mul_sub, Finset.sum_sub_distrib, P.total]

/-- The exact information-theoretic sample lower bound of Theorem 4.1.
The data are full recorded episodes and the estimator is an arbitrary
probability kernel into the real line, including continuous randomization. -/
theorem exact_estimation_sample_lower (k n : ℕ)
    (A : ValueEstimator (Fin n → Episode k × Action))
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/2)
    (h0 : A.failure ((fullEpisodeLaw false k).iid n) (1/4) ≤ δ)
    (h1 : A.failure ((fullEpisodeLaw true k).iid n) (3/4) ≤ δ) :
    2*binaryKL (1-δ) δ / (survival k*Real.log 3) ≤ n := by
  let P := (fullEpisodeLaw false k).iid n
  let Q := (fullEpisodeLaw true k).iid n
  let T := A.thresholdTest
  have hT0 : P.expect T.one ≤ δ := (A.threshold_error_zero P).trans h0
  have hT1 : Q.expect T.complement.one ≤ δ := (A.threshold_error_one Q).trans h1
  have hinfo := testing_kl_lower P Q
    (Law.iid_mass_pos _ (full_episode_mass_pos false k) n)
    (Law.iid_mass_pos _ (full_episode_mass_pos true k) n)
    T.complement hδ hδ'
    (by rw [T.expect_complement]; linarith) hT1
  change binaryKL (1-δ) δ ≤
    ((fullEpisodeLaw false k).iid n).kl ((fullEpisodeLaw true k).iid n) at hinfo
  rw [full_dataset_kl] at hinfo
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  apply (div_le_iff₀ (mul_pos (survival_pos k) hlog)).mpr
  nlinarith

end PomdpLogging
