import PomdpLogging.MatrixBasics

noncomputable section
namespace PomdpLogging

def columnStochastic (a b : ℝ) : Matrix Bool Bool ℝ :=
  fun s t => if s then (if t then 1-b else a) else (if t then b else 1-a)

def columnStochasticInverse (a b : ℝ) : Matrix Bool Bool ℝ :=
  fun s t => (if s then (if t then 1-a else -a) else (if t then -b else 1-b)) /
    (1-a-b)

theorem columnStochastic_inv (a b : ℝ) (h : 1-a-b ≠ 0) :
    (columnStochastic a b)⁻¹ = columnStochasticInverse a b := by
  apply Matrix.inv_eq_left_inv
  ext s t
  cases s <;> cases t <;>
    simp [Matrix.mul_apply, columnStochastic, columnStochasticInverse] <;>
    field_simp <;> ring

theorem columnStochastic_inv_bound {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 2/9 ≤ 1-a-b) :
    matrixOneNorm ((columnStochastic a b)⁻¹) ≤ 9 := by
  have hp : 0 < 1-a-b := by linarith
  have ha' : 0 ≤ 1-a := by linarith
  have hb' : 0 ≤ 1-b := by linarith
  rw [columnStochastic_inv a b hp.ne']
  simp only [matrixOneNorm, columnStochasticInverse, Bool.false_eq_true,
    ite_false, ite_true, abs_div, abs_of_pos hp,
    abs_of_nonneg ha', abs_of_nonneg hb', abs_neg,
    abs_of_nonneg ha, abs_of_nonneg hb]
  apply max_le
  · rw [← add_div]
    apply (div_le_iff₀ hp).mpr
    linarith
  · rw [← add_div]
    apply (div_le_iff₀ hp).mpr
    linarith

end PomdpLogging
