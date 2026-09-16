import PomdpLogging.OptimalTesting
import PomdpLogging.ProductCompression

noncomputable section
open scoped BigOperators
namespace PomdpLogging

def Symbol.swap : Symbol → Symbol
  | .erased => .erased
  | .zero => .one
  | .one => .zero

theorem Symbol.swap_swap (w : Symbol) : w.swap.swap = w := by cases w <;> rfl

def symbolDatasetSwap (n : ℕ) : (Fin n → Symbol) ≃ (Fin n → Symbol) where
  toFun xs i := (xs i).swap
  invFun xs i := (xs i).swap
  left_inv xs := funext (fun i => Symbol.swap_swap (xs i))
  right_inv xs := funext (fun i => Symbol.swap_swap (xs i))

theorem symbol_swap_mass (θ : Bool) (k : ℕ) (w : Symbol) :
    (symbolLaw θ k).mass w.swap = (symbolLaw (!θ) k).mass w := by
  cases θ <;> cases w <;> rfl

theorem symbol_dataset_swap_mass (θ : Bool) (k n : ℕ) (xs : Fin n → Symbol) :
    ((symbolLaw θ k).iid n).mass (symbolDatasetSwap n xs) =
      ((symbolLaw (!θ) k).iid n).mass xs := by
  change (∏ i, (symbolLaw θ k).mass (xs i).swap) = _
  simp_rw [symbol_swap_mass]
  rfl

theorem symbol_likelihood_balanced (k n : ℕ) :
    (likelihoodTest ((symbolLaw false k).iid n) ((symbolLaw true k).iid n)).errorZero
      ((symbolLaw false k).iid n) =
    (likelihoodTest ((symbolLaw false k).iid n) ((symbolLaw true k).iid n)).errorOne
      ((symbolLaw true k).iid n) :=
  likelihood_balanced _ _ (symbolDatasetSwap n)
    (symbol_dataset_swap_mass false k n) (symbol_dataset_swap_mass true k n)

def score : Symbol → ℤ
  | .erased => 0
  | .zero => -1
  | .one => 1

def scoreSum {n : ℕ} (xs : Fin n → Symbol) : ℤ := ∑ i, score (xs i)

theorem symbol_reverse_ratio (k : ℕ) (w : Symbol) :
    (symbolLaw true k).mass w / (symbolLaw false k).mass w = (3 : ℝ)^score w := by
  have hp := (survival_pos k).ne'
  have he := (symbol_mass_pos false k .erased).ne'
  cases w with
  | erased =>
    change (1-survival k)/(1-survival k) = (3 : ℝ)^(0 : ℤ)
    rw [zpow_zero]
    exact div_self he
  | zero =>
    change (survival k*(1/4))/(survival k*(3/4)) = (3 : ℝ)^(-1 : ℤ)
    norm_num
    field_simp
  | one =>
    change (survival k*(3/4))/(survival k*(1/4)) = (3 : ℝ)^(1 : ℤ)
    norm_num
    field_simp

theorem prod_three_zpow {I : Type*} (s : Finset I) (f : I → ℤ) :
    (∏ i ∈ s, (3 : ℝ)^(f i)) = (3 : ℝ)^(∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, zpow_add₀ (show (3 : ℝ) ≠ 0 by norm_num)]

theorem symbol_dataset_reverse_ratio (k n : ℕ) (xs : Fin n → Symbol) :
    ((symbolLaw true k).iid n).mass xs / ((symbolLaw false k).iid n).mass xs =
      (3 : ℝ)^scoreSum xs := by
  change (∏ i, (symbolLaw true k).mass (xs i))/(∏ i, (symbolLaw false k).mass (xs i)) = _
  rw [← Finset.prod_div_distrib]
  simp_rw [symbol_reverse_ratio]
  exact prod_three_zpow Finset.univ (fun i => score (xs i))

def majorityDecision {n : ℕ} (xs : Fin n → Symbol) : ℝ :=
  if 0 < scoreSum xs then 1 else if scoreSum xs < 0 then 0 else 1/2

theorem likelihood_is_majority (k n : ℕ) (xs : Fin n → Symbol) :
    (likelihoodTest ((symbolLaw false k).iid n) ((symbolLaw true k).iid n)).one xs =
      majorityDecision xs := by
  have hp := Law.iid_mass_pos _ (symbol_mass_pos false k) n xs
  have hgt : ((symbolLaw false k).iid n).mass xs < ((symbolLaw true k).iid n).mass xs ↔
      0 < scoreSum xs := by
    rw [← one_lt_div hp, symbol_dataset_reverse_ratio, one_lt_zpow_iff_right₀ (by norm_num)]
  have hlt : ((symbolLaw true k).iid n).mass xs < ((symbolLaw false k).iid n).mass xs ↔
      scoreSum xs < 0 := by
    rw [← div_lt_one hp, symbol_dataset_reverse_ratio, zpow_lt_one_iff_right₀ (by norm_num)]
  simp only [likelihoodTest, likelihoodDecision, majorityDecision, hgt, hlt]

def minimaxRisk (k n : ℕ) : ℝ :=
  overlapRisk ((symbolLaw false k).iid n) ((symbolLaw true k).iid n)

theorem majority_risk_formula (k n : ℕ) :
    minimaxRisk k n =
      ((symbolLaw false k).iid n).expect (fun xs => if 0 < scoreSum xs then 1 else 0) +
      (1/2)*((symbolLaw false k).iid n).expect (fun xs => if scoreSum xs = 0 then 1 else 0) := by
  have h := (balanced_likelihood_risk _ _ (symbol_likelihood_balanced k n)).1
  change _ = minimaxRisk k n at h
  rw [← h]
  unfold Test.errorZero Law.expect
  simp_rw [likelihood_is_majority]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro xs _
  rcases lt_trichotomy (scoreSum xs) 0 with hs | hs | hs
  · simp [majorityDecision, hs, ne_of_lt hs, not_lt.mpr hs.le]
  · simp [majorityDecision, hs, mul_comm]
  · simp [majorityDecision, hs, ne_of_gt hs, not_lt.mpr hs.le]

end PomdpLogging
