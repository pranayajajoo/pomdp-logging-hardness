import PomdpLogging.LogSum

noncomputable section
open scoped BigOperators
namespace PomdpLogging

theorem Law.expect_affine {α : Type*} [Fintype α] (P : Law α)
    (w : α → ℝ) (c t : ℝ) :
    P.expect (fun x => c+t*w x) = c+t*P.expect w := by
  simp only [Law.expect, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, P.total, one_mul]
  simp_rw [mul_left_comm (P.mass _) t, ← Finset.mul_sum]

theorem Test.expect_bounds {α : Type*} [Fintype α] (T : Test α) (P : Law α) :
    0 ≤ P.expect T.one ∧ P.expect T.one ≤ 1 := by
  constructor
  · exact P.expect_nonneg T.nonneg
  · simpa only [Law.expect_const] using P.expect_mono T.le_one

/-- Any test with both errors at most delta can be randomized further to give
exact success probabilities (1-delta, delta). This avoids endpoint cases in KL. -/
theorem calibrate_test {α : Type*} [Fintype α] (P Q : Law α) (T : Test α)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/2)
    (ha : 1-δ ≤ P.expect T.one) (hb : Q.expect T.one ≤ δ) :
    ∃ S : Test α, P.expect S.one = 1-δ ∧ Q.expect S.one = δ := by
  let a := P.expect T.one
  let b := Q.expect T.one
  have hab : 0 < a-b := by dsimp [a, b]; linarith
  have ha0 := (T.expect_bounds P).1
  have ha1 := (T.expect_bounds P).2
  have hb0 := (T.expect_bounds Q).1
  have hb1 := (T.expect_bounds Q).2
  let t := (1-2*δ)/(a-b)
  let c := (δ*a-(1-δ)*b)/(a-b)
  have ht : 0 ≤ t := by dsimp [t]; apply div_nonneg <;> linarith
  have hc : 0 ≤ c := by
    apply div_nonneg _ hab.le
    dsimp [a, b]
    nlinarith [mul_nonneg (show 0 ≤ δ by linarith) (sub_nonneg.mpr ha),
      mul_nonneg (show 0 ≤ 1-δ by linarith) (sub_nonneg.mpr hb)]
  have hct : c+t ≤ 1 := by
    dsimp [c, t]
    rw [← add_div]
    apply (div_le_iff₀ hab).mpr
    dsimp [a, b]
    nlinarith [mul_nonneg (show 0 ≤ 1-δ by linarith) (sub_nonneg.mpr ha),
      mul_nonneg (show 0 ≤ δ by linarith) (sub_nonneg.mpr hb)]
  let S : Test α := {
    one := fun x => c+t*T.one x
    nonneg := fun x => add_nonneg hc (mul_nonneg ht (T.nonneg x))
    le_one := by
      intro x
      have hx := mul_le_mul_of_nonneg_left (T.le_one x) ht
      nlinarith
  }
  refine ⟨S, ?_, ?_⟩
  · change P.expect (fun x => c+t*T.one x) = 1-δ
    rw [P.expect_affine]
    change c+t*a = 1-δ
    dsimp [c, t]
    field_simp
    ring
  · change Q.expect (fun x => c+t*T.one x) = δ
    rw [Q.expect_affine]
    change c+t*b = δ
    dsimp [c, t]
    field_simp
    ring

theorem testing_kl_lower {α : Type*} [Fintype α] (P Q : Law α)
    (hP : ∀ x, 0 < P.mass x) (hQ : ∀ x, 0 < Q.mass x)
    (T : Test α) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/2)
    (ha : 1-δ ≤ P.expect T.one) (hb : Q.expect T.one ≤ δ) :
    binaryKL (1-δ) δ ≤ P.kl Q := by
  obtain ⟨S, hS0, hS1⟩ := calibrate_test P Q T hδ hδ' ha hb
  have h := binary_data_processing P Q hP hQ S
    (by rw [hS0]; linarith) (by rw [hS0]; linarith)
    (by rw [hS1]; exact hδ) (by rw [hS1]; linarith)
  simpa only [hS0, hS1] using h

end PomdpLogging
