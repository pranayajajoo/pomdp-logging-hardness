import PomdpLogging.ThreeSymbol

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace PomdpLogging

theorem Law.iid_expect_product {α : Type*} [Fintype α] (P : Law α) (n : ℕ) (f : α → ℝ) :
    (P.iid n).expect (fun xs => ∏ i, f (xs i)) = (P.expect f)^n := by
  simp only [Law.expect, Law.iid]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.sum_pow (fun a => P.mass a * f a) n).symm

theorem Test.common_weight_lower {α : Type*} [Fintype α] (T : Test α) (P Q : Law α)
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a ∧ w a ≤ 1)
    (hPQ : ∀ a, w a ≠ 0 → P.mass a = Q.mass a) :
    P.expect w / 2 ≤ T.worstError P Q := by
  have hi (a : α) : P.mass a * w a ≤ min (P.mass a) (Q.mass a) := by
    by_cases ha : w a = 0
    · simp only [ha, mul_zero]
      exact le_min (P.nonneg a) (Q.nonneg a)
    · rw [← hPQ a ha, min_self]
      simpa using mul_le_mul_of_nonneg_left (hw a).2 (P.nonneg a)
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hi a)
  change P.expect w ≤ ∑ a, min (P.mass a) (Q.mass a) at hs
  linarith [T.overlap_lower P Q]

def erasedWeight {k : ℕ} (e : Episode k × Action) : ℝ :=
  if compressFull e = .erased then 1 else 0

theorem erasedWeight_bounds {k : ℕ} (e : Episode k × Action) :
    0 ≤ erasedWeight e ∧ erasedWeight e ≤ 1 := by
  unfold erasedWeight
  split_ifs <;> norm_num

theorem erasedWeight_expect (θ : Bool) (k : ℕ) :
    (fullEpisodeLaw θ k).expect erasedWeight = 1-survival k := by
  rw [show erasedWeight = (fun e => if compressFull e = .erased then (1 : ℝ) else 0) from rfl,
    full_compression_expect θ k (fun w => if w = .erased then 1 else 0)]
  simp [Law.expect, symbolLaw, symbolMass]

theorem erased_likelihood_equal {k : ℕ} (e : Episode k × Action)
    (he : erasedWeight e ≠ 0) :
    (fullEpisodeLaw false k).mass e = (fullEpisodeLaw true k).mass e := by
  have hr : e.1.1 ≠ allHold (k+1) := by
    intro hh
    have hz : erasedWeight e = 0 := by
      cases hy : e.1.2 <;> simp [erasedWeight, compressFull, compress, hh, hy]
    exact he hz
  change (episodeLaw false k).mass e.1 * _ = (episodeLaw true k).mass e.1 * _
  rw [reset_episode_likelihood_equal e.1 hr]

/-- A lower bound on arbitrary randomized tests of the *full* recorded data.
This theorem does not assume that the estimator only sees the compressed data. -/
theorem full_data_testing_lower (k n : ℕ) (T : Test (Fin n → Episode k × Action)) :
    (1-survival k)^n / 2 ≤ T.worstError ((fullEpisodeLaw false k).iid n)
      ((fullEpisodeLaw true k).iid n) := by
  let w : (Fin n → Episode k × Action) → ℝ := fun xs => ∏ i, erasedWeight (xs i)
  have hw (xs) : 0 ≤ w xs ∧ w xs ≤ 1 := by
    constructor
    · exact Finset.prod_nonneg (fun i _ => (erasedWeight_bounds (xs i)).1)
    · exact Finset.prod_le_one₀ (fun i _ => (erasedWeight_bounds (xs i)).1)
        (fun i _ => (erasedWeight_bounds (xs i)).2)
  have hPQ (xs) (hx : w xs ≠ 0) :
      ((fullEpisodeLaw false k).iid n).mass xs = ((fullEpisodeLaw true k).iid n).mass xs := by
    change (∏ i, (fullEpisodeLaw false k).mass (xs i)) =
      ∏ i, (fullEpisodeLaw true k).mass (xs i)
    apply Finset.prod_congr rfl
    intro i _
    have hi : erasedWeight (xs i) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i)
    exact erased_likelihood_equal (xs i) hi
  have hb := T.common_weight_lower ((fullEpisodeLaw false k).iid n)
    ((fullEpisodeLaw true k).iid n) w hw hPQ
  simpa only [w, Law.iid_expect_product, erasedWeight_expect] using hb

/-- An arbitrary real-valued randomized estimator on a finite data space.
The conditional output distributions may be continuous. -/
abbrev ValueEstimator (α : Type*) := α → ProbabilityMeasure ℝ

namespace ValueEstimator

variable {α : Type*} [Fintype α]

def failure (A : ValueEstimator α) (P : Law α) (value : ℝ) : ℝ :=
  P.expect (fun x => (A x : Measure ℝ).real {y | |y-value| > 1/8})

def thresholdTest (A : ValueEstimator α) : Test α where
  one x := (A x : Measure ℝ).real (Set.Ioi (1/2))
  nonneg _ := measureReal_nonneg
  le_one _ := measureReal_le_one

theorem threshold_error_zero (A : ValueEstimator α) (P : Law α) :
    (thresholdTest A).errorZero P ≤ A.failure P (1/4) := by
  apply P.expect_mono
  intro x
  refine measureReal_mono ?_ (by finiteness)
  intro y hy
  change 1/8 < |y-1/4|
  have hy' : 1/2 < y := hy
  have ha : y-1/4 ≤ |y-1/4| := le_abs_self _
  linarith

theorem threshold_error_one (A : ValueEstimator α) (P : Law α) :
    (thresholdTest A).errorOne P ≤ A.failure P (3/4) := by
  apply P.expect_mono
  intro x
  change 1 - (A x : Measure ℝ).real (Set.Ioi (1/2)) ≤ _
  have hc : (A x : Measure ℝ).real ((Set.Ioi (1/2))ᶜ) =
      1 - (A x : Measure ℝ).real (Set.Ioi (1/2)) := by
    rw [measureReal_compl measurableSet_Ioi, probReal_univ]
  rw [← hc]
  refine measureReal_mono ?_ (by finiteness)
  intro y hy
  have hy' : y ≤ 1/2 := by simpa using hy
  change 1/8 < |y-3/4|
  have ha : -(y-3/4) ≤ |y-3/4| := neg_le_abs _
  linarith

end ValueEstimator

/-- Exact full-data lower bound at the paper's accuracy, already quantifying
over all real-valued randomized estimators. The sharper KL constant is separate. -/
theorem full_data_estimation_lower (k n : ℕ)
    (A : ValueEstimator (Fin n → Episode k × Action)) :
    (1-survival k)^n / 2 ≤
      max (A.failure ((fullEpisodeLaw false k).iid n) (1/4))
          (A.failure ((fullEpisodeLaw true k).iid n) (3/4)) := by
  have h := full_data_testing_lower k n (A.thresholdTest)
  exact h.trans (max_le_max (A.threshold_error_zero _) (A.threshold_error_one _))

end PomdpLogging
