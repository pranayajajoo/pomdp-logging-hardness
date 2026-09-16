import PomdpLogging.MatrixBasics

noncomputable section
open scoped BigOperators

namespace PomdpLogging

theorem sum_partition {F : Type*} [Fintype F] (E : F → Prop) [DecidablePred E] (g : F → ℝ) :
    (∑ f ∈ Finset.univ.filter E, g f) +
      (∑ f ∈ Finset.univ.filter (fun f => ¬ E f), g f) = ∑ f, g f := by
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f _
  by_cases h : E f <;> simp [h]

structure PositiveChannel (F : Type*) [Fintype F] where
  entry : F → Bool → ℝ
  positive : ∀ f s, 0 < entry f s
  total : ∀ s, ∑ f, entry f s = 1

namespace PositiveChannel

variable {F : Type*} [Fintype F]

def denominator (U : PositiveChannel F) (f : F) := U.entry f false + U.entry f true

theorem denominator_pos (U : PositiveChannel F) (f : F) : 0 < U.denominator f :=
  add_pos (U.positive f false) (U.positive f true)

/-- Entrywise expansion of U-transpose diag(U 1) inverse U. -/
def gram (U : PositiveChannel F) : Matrix Bool Bool ℝ :=
  fun s t => ∑ f, U.entry f s * U.entry f t / U.denominator f

theorem gram_symm (U : PositiveChannel F) (s t : Bool) : U.gram s t = U.gram t s := by
  simp only [gram, mul_comm]

theorem gram_nonneg (U : PositiveChannel F) (s t : Bool) : 0 ≤ U.gram s t :=
  Finset.sum_nonneg (fun f _ =>
    div_nonneg (mul_nonneg (U.positive f s).le (U.positive f t).le) (U.denominator_pos f).le)

theorem gram_row_sum (U : PositiveChannel F) (s : Bool) :
    U.gram s false + U.gram s true = 1 := by
  unfold gram
  rw [← Finset.sum_add_distrib, ← U.total s]
  apply Finset.sum_congr rfl
  intro f _
  have hd := (U.denominator_pos f).ne'
  unfold denominator at *
  field_simp

theorem gram_form (U : PositiveChannel F) :
    U.gram = symmetricStochastic (2 * U.gram false false - 1) := by
  have h0 := U.gram_row_sum false
  have h1 := U.gram_row_sum true
  have hs := U.gram_symm false true
  ext s t
  cases s <;> cases t <;> simp only [symmetricStochastic] <;> norm_num <;> linarith

theorem gram_parameter_le_one (U : PositiveChannel F) : 2 * U.gram false false - 1 ≤ 1 := by
  linarith [U.gram_row_sum false, U.gram_nonneg false true]

/-- The scalar Cauchy-Schwarz step in the paper's coarsening argument. -/
theorem gram_diag_lower (U : PositiveChannel F) (E : F → Prop) [DecidablePred E]
    (hq : (∑ f ∈ Finset.univ.filter E, U.entry f false) = 1/6)
    (hr : (∑ f ∈ Finset.univ.filter E, U.entry f true) = 2/3) :
    22/35 ≤ U.gram false false := by
  have hn0 : (∑ f ∈ Finset.univ.filter (fun f => ¬ E f), U.entry f false) = 5/6 := by
    have h := sum_partition E (fun f => U.entry f false)
    rw [hq, U.total false] at h
    linarith
  have hn1 : (∑ f ∈ Finset.univ.filter (fun f => ¬ E f), U.entry f true) = 1/3 := by
    have h := sum_partition E (fun f => U.entry f true)
    rw [hr, U.total true] at h
    linarith
  have hd0 : (∑ f ∈ Finset.univ.filter E, U.denominator f) = 5/6 := by
    simp only [denominator, Finset.sum_add_distrib, hq, hr]
    norm_num
  have hd1 : (∑ f ∈ Finset.univ.filter (fun f => ¬ E f), U.denominator f) = 7/6 := by
    simp only [denominator, Finset.sum_add_distrib, hn0, hn1]
    norm_num
  have hc0 := Finset.sq_sum_div_le_sum_sq_div (Finset.univ.filter E)
    (fun f => U.entry f false) (g := U.denominator) (fun f _ => U.denominator_pos f)
  have hc1 := Finset.sq_sum_div_le_sum_sq_div (Finset.univ.filter (fun f => ¬ E f))
    (fun f => U.entry f false) (g := U.denominator) (fun f _ => U.denominator_pos f)
  rw [hq, hd0] at hc0
  rw [hn0, hd1] at hc1
  have hs := sum_partition E (fun f => U.entry f false ^ 2 / U.denominator f)
  simp only [pow_two] at hc0 hc1 hs
  change _ = U.gram false false at hs
  norm_num at hc0 hc1
  linarith

theorem uniform_bound (U : PositiveChannel F) (E : F → Prop) [DecidablePred E]
    (hq : (∑ f ∈ Finset.univ.filter E, U.entry f false) = 1/6)
    (hr : (∑ f ∈ Finset.univ.filter E, U.entry f true) = 2/3) :
    matrixOneNorm U.gram⁻¹ ≤ 35/9 := by
  rw [U.gram_form]
  apply uniform_revealing_constant
  · linarith [U.gram_diag_lower E hq hr]
  · exact U.gram_parameter_le_one

theorem gram_swap_entry (U : PositiveChannel F) (s t : Bool) :
    U.gram (!s) (!t) = U.gram s t := by
  rw [U.gram_form]
  cases s <;> cases t <;> rfl

end PositiveChannel
end PomdpLogging
