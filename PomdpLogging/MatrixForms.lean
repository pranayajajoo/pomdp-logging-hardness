import PomdpLogging.WeightedRevealing

noncomputable section
open scoped BigOperators
namespace PomdpLogging
namespace PositiveChannel

variable {F : Type*} [Fintype F] [DecidableEq F]

def matrix (U : PositiveChannel F) : Matrix F Bool ℝ := U.entry

theorem positive_diagonal_inverse (d : F → ℝ) (hd : ∀ f, 0 < d f) :
    (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun f => (d f)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal_apply, (hd i).ne', Matrix.one_apply]
  · simp [Matrix.diagonal_apply, hij, Matrix.one_apply]

/-- The componentwise definition is literally the matrix product in the paper. -/
theorem gram_matrix_formula (U : PositiveChannel F) :
    U.gram = Matrix.transpose U.matrix *
      (Matrix.diagonal (Matrix.mulVec U.matrix (fun _ => 1)))⁻¹ * U.matrix := by
  classical
  rw [positive_diagonal_inverse _ (by
    intro f
    simpa [matrix, Matrix.mulVec, dotProduct, denominator, add_comm] using U.denominator_pos f)]
  ext s t
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, Matrix.transpose_apply]
  simp only [gram, Matrix.mulVec, dotProduct, matrix, Fintype.sum_bool, mul_one]
  apply Finset.sum_congr rfl
  intro f _
  unfold denominator
  rw [div_eq_mul_inv]
  ring

theorem weightedGram_matrix_formula (U : PositiveChannel F) (ρ : ℝ)
    (hρ : 0 < ρ) (hρ' : ρ < 1) :
    U.weightedGram ρ =
      Matrix.diagonal (fun s : Bool => if s then ρ else 1-ρ) * Matrix.transpose U.matrix *
        (Matrix.diagonal (Matrix.mulVec U.matrix (fun s : Bool => if s then ρ else 1-ρ)))⁻¹ *
          U.matrix := by
  classical
  have hd (f : F) : (Matrix.mulVec U.matrix (fun s : Bool => if s then ρ else 1-ρ)) f =
      U.weightedDenominator ρ f := by
    simp [matrix, Matrix.mulVec, dotProduct, weightedDenominator, mul_comm, add_comm]
  rw [positive_diagonal_inverse _ (fun f => by
    rw [hd]
    exact U.weightedDenominator_pos hρ hρ' f)]
  ext s t
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply, hd]
  unfold weightedGram
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  simp only [matrix, div_eq_mul_inv]
  ring

end PositiveChannel

theorem stateMass_sum (θ : Bool) (k : ℕ) : stateMass θ k false + stateMass θ k true = 1 := by
  cases θ <;> simp [stateMass] <;> ring

theorem stateMass_as_prior (θ : Bool) (k : ℕ) :
    stateMass θ k = (fun s : Bool => if s then stateMass θ k true else 1-stateMass θ k true) := by
  funext s
  cases s
  · simp only [Bool.false_eq_true, ite_false]
    linarith [stateMass_sum θ k]
  · rfl

end PomdpLogging
