import PomdpLogging.DeterministicRisk

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace PomdpLogging

def Test.unitValueEstimator {α : Type*} (T : Test α) : ValueEstimator α :=
  fun x => ⟨bernoulliMeasure (1 : ℝ) 0 ⟨T.one x, T.nonneg x, T.le_one x⟩,
    inferInstance⟩

theorem Test.unitValueEstimator_failure_zero {α : Type*} [Fintype α]
    (T : Test α) (P : Law α) : T.unitValueEstimator.failure P 0 = T.errorZero P := by
  unfold ValueEstimator.failure Test.errorZero
  congr 1
  funext x
  change (bernoulliMeasure (1 : ℝ) 0
    ⟨T.one x, T.nonneg x, T.le_one x⟩).real {y : ℝ | |y-0| > 1/8} = T.one x
  exact bernoulliMeasure_real_apply_of_mem_of_notMem _
    (measurableSet_lt measurable_const ((measurable_id.sub_const _).abs))
    (by norm_num) (by norm_num)

theorem Test.unitValueEstimator_failure_one {α : Type*} [Fintype α]
    (T : Test α) (Q : Law α) : T.unitValueEstimator.failure Q 1 = T.errorOne Q := by
  unfold ValueEstimator.failure Test.errorOne
  congr 1
  funext x
  change (bernoulliMeasure (1 : ℝ) 0
    ⟨T.one x, T.nonneg x, T.le_one x⟩).real {y : ℝ | |y-1| > 1/8} = 1-T.one x
  exact bernoulliMeasure_real_apply_of_notMem_of_mem _
    (measurableSet_lt measurable_const ((measurable_id.sub_const _).abs))
    (by norm_num) (by norm_num)

theorem ValueEstimator.threshold_unit_zero {α : Type*} [Fintype α]
    (A : ValueEstimator α) (P : Law α) : A.thresholdTest.errorZero P ≤ A.failure P 0 := by
  apply P.expect_mono
  intro x
  refine measureReal_mono ?_ (by finiteness)
  intro y hy
  change 1/8 < |y-0|
  have hy' : 1/2 < y := hy
  have ha : y-0 ≤ |y-0| := le_abs_self _
  linarith

theorem ValueEstimator.threshold_unit_one {α : Type*} [Fintype α]
    (A : ValueEstimator α) (P : Law α) : A.thresholdTest.errorOne P ≤ A.failure P 1 := by
  apply P.expect_mono
  intro x
  change 1-(A x : Measure ℝ).real (Set.Ioi (1/2)) ≤ _
  have hc : (A x : Measure ℝ).real ((Set.Ioi (1/2))ᶜ) =
      1-(A x : Measure ℝ).real (Set.Ioi (1/2)) := by
    rw [measureReal_compl measurableSet_Ioi, probReal_univ]
  rw [← hc]
  refine measureReal_mono ?_ (by finiteness)
  intro y hy
  have hy' : y ≤ 1/2 := by simpa using hy
  change 1/8 < |y-1|
  have ha : -(y-1) ≤ |y-1| := neg_le_abs _
  linarith

def deterministicEstimator (k n : ℕ) : ValueEstimator (Fin n → Episode k × Action) :=
  (likelihoodTest ((deterministicFullLaw false k).iid n)
    ((deterministicFullLaw true k).iid n)).unitValueEstimator

/-- Exact full-data minimax estimation risk for Appendix E, including arbitrary
real-valued randomized estimators and attainment at accuracy 1/8. -/
theorem deterministic_exact_minimax (k n : ℕ) :
    (∀ A : ValueEstimator (Fin n → Episode k × Action), (1-survival k)^n/2 ≤
      max (A.failure ((deterministicFullLaw false k).iid n) 0)
        (A.failure ((deterministicFullLaw true k).iid n) 1)) ∧
    max ((deterministicEstimator k n).failure ((deterministicFullLaw false k).iid n) 0)
      ((deterministicEstimator k n).failure ((deterministicFullLaw true k).iid n) 1) =
        (1-survival k)^n/2 := by
  constructor
  · intro A
    exact ((deterministic_minimax_test k n).1 A.thresholdTest).trans
      (max_le_max (A.threshold_unit_zero _) (A.threshold_unit_one _))
  · unfold deterministicEstimator
    rw [Test.unitValueEstimator_failure_zero, Test.unitValueEstimator_failure_one]
    exact (deterministic_minimax_test k n).2

end PomdpLogging
