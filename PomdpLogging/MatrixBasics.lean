import PomdpLogging.FiniteProbability

noncomputable section
open scoped BigOperators

namespace PomdpLogging

/-- Exactly the maximum absolute column sum, the induced matrix 1-norm in
the paper, specialized to its two physical states. -/
def matrixOneNorm (A : Matrix Bool Bool ℝ) : ℝ :=
  max (|A false false| + |A true false|) (|A false true| + |A true true|)

def symmetricStochastic (lam : ℝ) : Matrix Bool Bool ℝ :=
  fun i j => if i = j then (1+lam)/2 else (1-lam)/2

theorem symmetricStochastic_inv {lam : ℝ} (h : lam ≠ 0) :
    (symmetricStochastic lam)⁻¹ = symmetricStochastic (1/lam) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.mul_apply, symmetricStochastic, Matrix.one_apply] <;>
    field_simp <;> ring

theorem symmetricStochastic_inv_norm {lam : ℝ} (hp : 0 < lam) (hu : lam ≤ 1) :
    matrixOneNorm ((symmetricStochastic lam)⁻¹) = 1/lam := by
  rw [symmetricStochastic_inv (ne_of_gt hp)]
  have hi : 1 ≤ 1/lam := (le_div_iff₀ hp).mpr (by linarith)
  have hd : 0 ≤ (1 + 1/lam)/2 := by positivity
  have ho : (1 - 1/lam)/2 ≤ 0 := by linarith
  simp only [matrixOneNorm, symmetricStochastic, Bool.false_eq_true, Bool.true_eq_false,
    ite_true, ite_false, abs_of_nonneg hd, abs_of_nonpos ho]
  convert (max_self (1/lam)) using 1 <;> ring

theorem uniform_revealing_constant {lam : ℝ} (hl : 9/35 ≤ lam) (hu : lam ≤ 1) :
    matrixOneNorm ((symmetricStochastic lam)⁻¹) ≤ 35/9 := by
  have hp : 0 < lam := by linarith
  rw [symmetricStochastic_inv_norm hp hu]
  apply (div_le_iff₀ hp).mpr
  linarith

theorem terminal_revealing_norm :
    matrixOneNorm ((symmetricStochastic (1/4))⁻¹) = 4 := by
  rw [symmetricStochastic_inv_norm (by norm_num) (by norm_num)]
  norm_num

end PomdpLogging
