import PomdpLogging.FullDataLowerBound

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace PomdpLogging

/-- Return 3/4 with the test's probability of model one, and 1/4 otherwise. -/
def Test.valueEstimator {α : Type*} (T : Test α) : ValueEstimator α :=
  fun x => ⟨bernoulliMeasure (3/4 : ℝ) (1/4) ⟨T.one x, T.nonneg x, T.le_one x⟩,
    inferInstance⟩

theorem Test.valueEstimator_failure_zero {α : Type*} [Fintype α] (T : Test α) (P : Law α) :
    T.valueEstimator.failure P (1/4) = T.errorZero P := by
  unfold ValueEstimator.failure Test.errorZero
  congr 1
  funext x
  change (bernoulliMeasure (3/4 : ℝ) (1/4)
    ⟨T.one x, T.nonneg x, T.le_one x⟩).real {y : ℝ | |y-1/4| > 1/8} = T.one x
  exact bernoulliMeasure_real_apply_of_mem_of_notMem _
    (measurableSet_lt measurable_const ((measurable_id.sub_const _).abs))
    (by norm_num) (by norm_num)

theorem Test.valueEstimator_failure_one {α : Type*} [Fintype α] (T : Test α) (Q : Law α) :
    T.valueEstimator.failure Q (3/4) = T.errorOne Q := by
  unfold ValueEstimator.failure Test.errorOne
  congr 1
  funext x
  change (bernoulliMeasure (3/4 : ℝ) (1/4)
    ⟨T.one x, T.nonneg x, T.le_one x⟩).real {y : ℝ | |y-3/4| > 1/8} = 1-T.one x
  exact bernoulliMeasure_real_apply_of_notMem_of_mem _
    (measurableSet_lt measurable_const ((measurable_id.sub_const _).abs))
    (by norm_num) (by norm_num)

end PomdpLogging
