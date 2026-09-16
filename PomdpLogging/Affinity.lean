import PomdpLogging.OptimalTesting
import PomdpLogging.ProductInformation

noncomputable section
open scoped BigOperators
namespace PomdpLogging

def Law.affinity {α : Type*} [Fintype α] (P Q : Law α) : ℝ :=
  ∑ x, Real.sqrt (P.mass x*Q.mass x)

theorem min_le_geometric {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    min p q ≤ Real.sqrt (p*q) := by
  apply Real.le_sqrt_of_sq_le
  rcases le_total p q with h | h
  · rw [min_eq_left h, pow_two]
    exact mul_le_mul_of_nonneg_left h hp
  · rw [min_eq_right h, pow_two]
    exact mul_le_mul_of_nonneg_right h hq

theorem overlapRisk_le_affinity {α : Type*} [Fintype α] (P Q : Law α) :
    overlapRisk P Q ≤ P.affinity Q / 2 := by
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact Finset.sum_le_sum (fun x _ => min_le_geometric (P.nonneg x) (Q.nonneg x))

theorem Law.affinity_iid {α : Type*} [Fintype α] (P Q : Law α) (n : ℕ) :
    (P.iid n).affinity (Q.iid n) = (P.affinity Q)^n := by
  unfold affinity iid
  simp only
  simp_rw [← Finset.prod_mul_distrib,
    Real.sqrt_prod Finset.univ (fun i _ => mul_nonneg (P.nonneg _) (Q.nonneg _))]
  exact (Fintype.sum_pow (fun x => Real.sqrt (P.mass x*Q.mass x)) n).symm

def affinityConstant : ℝ := 1-Real.sqrt 3/2

theorem symbol_affinity (k : ℕ) :
    (symbolLaw false k).affinity (symbolLaw true k) = 1-affinityConstant*survival k := by
  let p := survival k
  have hp : 0 ≤ p := (survival_pos k).le
  have hu : 0 ≤ 1-p := by dsimp [p]; linarith [survival_le_third k]
  have he : Real.sqrt ((1-p)*(1-p)) = 1-p := Real.sqrt_mul_self hu
  have hf : Real.sqrt ((p*(3/4))*(p*(1/4))) = p*Real.sqrt 3/4 := by
    have halg : (p*(3/4))*(p*(1/4)) = (p^2*3)/16 := by ring
    rw [halg, Real.sqrt_div (mul_nonneg (sq_nonneg p) (by norm_num)),
      Real.sqrt_mul (sq_nonneg p), Real.sqrt_sq hp]
    norm_num
  unfold Law.affinity
  rw [sum_symbol]
  change Real.sqrt ((1-p)*(1-p)) + Real.sqrt ((p*(3/4))*(p*(1/4))) +
    Real.sqrt ((p*(1/4))*(p*(3/4))) = _
  rw [he, hf, mul_comm (p*(1/4)) (p*(3/4)), hf]
  dsimp [affinityConstant, p]
  ring

theorem affinityConstant_bounds : 1/8 ≤ affinityConstant ∧ affinityConstant ≤ 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hp := Real.sqrt_nonneg (3 : ℝ)
  unfold affinityConstant
  constructor <;> nlinarith

end PomdpLogging
