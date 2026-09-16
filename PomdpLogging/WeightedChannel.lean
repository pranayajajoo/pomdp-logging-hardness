import PomdpLogging.UniformChannel

noncomputable section
open scoped BigOperators
namespace PomdpLogging
namespace PositiveChannel

variable {F : Type*} [Fintype F]

def weightedDenominator (U : PositiveChannel F) (ρ : ℝ) (f : F) : ℝ :=
  (1-ρ) * U.entry f false + ρ * U.entry f true

theorem weightedDenominator_pos (U : PositiveChannel F) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ' : ρ < 1) (f : F) : 0 < U.weightedDenominator ρ f := by
  unfold weightedDenominator
  exact add_pos (mul_pos (sub_pos.mpr hρ') (U.positive f false))
    (mul_pos hρ (U.positive f true))

theorem weightedDenominator_total (U : PositiveChannel F) (ρ : ℝ) :
    ∑ f, U.weightedDenominator ρ f = 1 := by
  simp [weightedDenominator, Finset.sum_add_distrib, ← Finset.mul_sum, U.total]

def overlap (U : PositiveChannel F) (ρ : ℝ) : ℝ :=
  ∑ f, U.entry f false * U.entry f true / U.weightedDenominator ρ f

def contrast (U : PositiveChannel F) (ρ : ℝ) : ℝ :=
  ∑ f, (U.entry f true - U.entry f false)^2 / U.weightedDenominator ρ f

/-- The row prior in this formula is essential: columns, not rows, sum to one. -/
def weightedGram (U : PositiveChannel F) (ρ : ℝ) : Matrix Bool Bool ℝ :=
  fun s t => (if s then ρ else 1-ρ) *
    ∑ f, U.entry f s * U.entry f t / U.weightedDenominator ρ f

theorem overlap_nonneg (U : PositiveChannel F) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ' : ρ < 1) : 0 ≤ U.overlap ρ :=
  Finset.sum_nonneg (fun f _ => div_nonneg
    (mul_nonneg (U.positive f false).le (U.positive f true).le)
    (U.weightedDenominator_pos hρ hρ' f).le)

theorem contrast_identity (U : PositiveChannel F) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ' : ρ < 1) :
    ρ*(1-ρ)*U.contrast ρ + U.overlap ρ = 1 := by
  unfold contrast overlap
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  have he (f : F) :
      ρ*(1-ρ)*((U.entry f true-U.entry f false)^2 / U.weightedDenominator ρ f) +
        U.entry f false*U.entry f true / U.weightedDenominator ρ f =
      ρ*U.entry f false + (1-ρ)*U.entry f true := by
    have hd := (U.weightedDenominator_pos hρ hρ' f).ne'
    field_simp
    unfold weightedDenominator
    ring
  simp_rw [he]
  simp [Finset.sum_add_distrib, ← Finset.mul_sum, U.total]

theorem weightedGram_column_sum (U : PositiveChannel F) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ' : ρ < 1) (t : Bool) :
    U.weightedGram ρ false t + U.weightedGram ρ true t = 1 := by
  unfold weightedGram
  simp only [Bool.false_eq_true, ite_false, ite_true]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  conv_rhs => rw [← U.total t]
  apply Finset.sum_congr rfl
  intro f _
  have hd := (U.weightedDenominator_pos hρ hρ' f).ne'
  field_simp
  unfold weightedDenominator
  ring

theorem weightedGram_cross (U : PositiveChannel F) (ρ : ℝ) :
    U.weightedGram ρ true false = ρ * U.overlap ρ ∧
      U.weightedGram ρ false true = (1-ρ) * U.overlap ρ := by
  constructor
  · simp only [weightedGram, ite_true, overlap, mul_comm]
  · rfl

/-- The event and its complement together force contrast at least one. -/
theorem contrast_lower (U : PositiveChannel F) {ρ q r : ℝ}
    (hρ : 0 < ρ) (hρ' : ρ < 1)
    (E : F → Prop) [DecidablePred E]
    (hq : (∑ f ∈ Finset.univ.filter E, U.entry f false) = q)
    (hr : (∑ f ∈ Finset.univ.filter E, U.entry f true) = r)
    (hq0 : 0 < q) (hq1 : q < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (hdiff : (r-q)^2 = 1/4) : 1 ≤ U.contrast ρ := by
  let m := (1-ρ)*q + ρ*r
  have hm : 0 < m := by dsimp [m]; positivity
  have hm' : 0 < 1-m := by
    have h : 0 < (1-ρ)*(1-q) + ρ*(1-r) := by positivity
    dsimp [m]
    nlinarith
  have hd0 : (∑ f ∈ Finset.univ.filter E, U.weightedDenominator ρ f) = m := by
    simp only [weightedDenominator, Finset.sum_add_distrib, ← Finset.mul_sum, hq, hr, m]
  have hd1 : (∑ f ∈ Finset.univ.filter (fun f => ¬ E f),
      U.weightedDenominator ρ f) = 1-m := by
    have h := sum_partition E (U.weightedDenominator ρ)
    rw [hd0, U.weightedDenominator_total] at h
    linarith
  have he0 : (∑ f ∈ Finset.univ.filter E, (U.entry f true-U.entry f false)) = r-q := by
    rw [Finset.sum_sub_distrib, hr, hq]
  have he1 : (∑ f ∈ Finset.univ.filter (fun f => ¬ E f),
      (U.entry f true-U.entry f false)) = -(r-q) := by
    have h := sum_partition E (fun f => U.entry f true-U.entry f false)
    have ht : (∑ f, (U.entry f true-U.entry f false)) = 0 := by
      rw [Finset.sum_sub_distrib, U.total true, U.total false, sub_self]
    rw [he0, ht] at h
    linarith
  have hc0 := Finset.sq_sum_div_le_sum_sq_div (Finset.univ.filter E)
    (fun f => U.entry f true-U.entry f false) (g := U.weightedDenominator ρ)
    (fun f _ => U.weightedDenominator_pos hρ hρ' f)
  have hc1 := Finset.sq_sum_div_le_sum_sq_div (Finset.univ.filter (fun f => ¬ E f))
    (fun f => U.entry f true-U.entry f false) (g := U.weightedDenominator ρ)
    (fun f _ => U.weightedDenominator_pos hρ hρ' f)
  rw [he0, hd0, hdiff] at hc0
  rw [he1, hd1, neg_sq, hdiff] at hc1
  have hs := sum_partition E
    (fun f => (U.entry f true-U.entry f false)^2 / U.weightedDenominator ρ f)
  change _ = U.contrast ρ at hs
  have hscalar : 1 ≤ (1/4 : ℝ)/m + (1/4 : ℝ)/(1-m) := by
    have he : (1/4 : ℝ)/m + (1/4 : ℝ)/(1-m) = (1/4 : ℝ)/(m*(1-m)) := by
      field_simp
      ring
    rw [he]
    apply (le_div_iff₀ (mul_pos hm hm')).mpr
    nlinarith [sq_nonneg (m-1/2)]
  linarith

end PositiveChannel
end PomdpLogging
