import PomdpLogging.Information

noncomputable section
open scoped BigOperators
namespace PomdpLogging
namespace Law

variable {α : Type*} [Fintype α]

theorem iid_expect_factors (P : Law α) (n : ℕ) (f : Fin n → α → ℝ) :
    (P.iid n).expect (fun xs => ∏ i, f i (xs i)) = ∏ i, P.expect (f i) := by
  simp only [expect, iid]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => P.mass a*f i a)).symm

theorem iid_expect_coordinate (P : Law α) (n : ℕ) (i : Fin n) (f : α → ℝ) :
    (P.iid n).expect (fun xs => f (xs i)) = P.expect f := by
  have h := iid_expect_factors P n (fun j a => if i = j then f a else 1)
  simp only [Fintype.prod_ite_eq] at h
  have he (j : Fin n) : P.expect (fun a => if i = j then f a else 1) =
      if i = j then P.expect f else 1 := by
    by_cases hj : i = j <;> simp [hj, expect_const]
  simp_rw [he, Fintype.prod_ite_eq] at h
  exact h

theorem iid_mass_pos (P : Law α) (hP : ∀ x, 0 < P.mass x) (n : ℕ) (xs : Fin n → α) :
    0 < (P.iid n).mass xs := by
  change 0 < ∏ i, P.mass (xs i)
  exact Finset.prod_pos (fun i _ => hP (xs i))

theorem kl_iid (P Q : Law α) (hP : ∀ x, 0 < P.mass x) (hQ : ∀ x, 0 < Q.mass x)
    (n : ℕ) : (P.iid n).kl (Q.iid n) = n * P.kl Q := by
  have hlog (xs : Fin n → α) :
      Real.log ((P.iid n).mass xs/(Q.iid n).mass xs) =
        ∑ i, Real.log (P.mass (xs i)/Q.mass (xs i)) := by
    change Real.log ((∏ i, P.mass (xs i))/(∏ i, Q.mass (xs i))) = _
    rw [← Finset.prod_div_distrib]
    exact Real.log_prod (fun i _ => (div_pos (hP (xs i)) (hQ (xs i))).ne')
  unfold kl
  simp_rw [hlog]
  unfold expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  change (∑ i, (P.iid n).expect (fun xs => Real.log (P.mass (xs i)/Q.mass (xs i)))) = _
  simp_rw [iid_expect_coordinate P n _ (fun a => Real.log (P.mass a/Q.mass a))]
  simp [expect, Finset.mul_sum]

end Law

theorem full_dataset_kl (k n : ℕ) :
    ((fullEpisodeLaw false k).iid n).kl ((fullEpisodeLaw true k).iid n) =
      n * (survival k / 2 * Real.log 3) := by
  rw [Law.kl_iid _ _ (full_episode_mass_pos false k) (full_episode_mass_pos true k),
    full_trajectory_kl]

end PomdpLogging
