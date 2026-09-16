import PomdpLogging.Information

noncomputable section
open scoped BigOperators
namespace PomdpLogging

theorem log_ratio_tangent {p q A B : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hA : 0 < A) (hB : 0 < B) :
    p*Real.log (A/B) + p - (A/B)*q ≤ p*Real.log (p/q) := by
  have hx := Real.log_le_sub_one_of_pos (show 0 < q*A/(p*B) by positivity)
  rw [Real.log_div (mul_pos hq hA).ne' (mul_pos hp hB).ne',
    Real.log_mul hq.ne' hA.ne', Real.log_mul hp.ne' hB.ne'] at hx
  have hm := mul_le_mul_of_nonneg_left hx hp.le
  have he : p*(q*A/(p*B)) = (A/B)*q := by field_simp
  simp only [mul_sub, he, mul_one] at hm
  rw [Real.log_div hA.ne' hB.ne', Real.log_div hp.ne' hq.ne']
  nlinarith

/-- Finite log-sum inequality with an arbitrary nonnegative randomization weight. -/
theorem weighted_log_sum {α : Type*} [Fintype α] (P Q : Law α)
    (hP : ∀ x, 0 < P.mass x) (hQ : ∀ x, 0 < Q.mass x)
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hA : 0 < P.expect w) (hB : 0 < Q.expect w) :
    P.expect w * Real.log (P.expect w / Q.expect w) ≤
      P.expect (fun x => w x * Real.log (P.mass x / Q.mass x)) := by
  let A := P.expect w
  let B := Q.expect w
  have hpoint (x : α) :
      P.mass x*w x*Real.log (A/B) + P.mass x*w x - (A/B)*(Q.mass x*w x) ≤
        P.mass x*(w x*Real.log (P.mass x/Q.mass x)) := by
    have h := mul_le_mul_of_nonneg_left
      (log_ratio_tangent (hP x) (hQ x) hA hB) (hw x)
    dsimp [A, B]
    nlinarith
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum] at hs
  change A*Real.log (A/B) + A - (A/B)*B ≤ _ at hs
  rw [div_mul_cancel₀ _ hB.ne'] at hs
  change A*Real.log (A/B) ≤ ∑ x, P.mass x*(w x*Real.log (P.mass x/Q.mass x))
  linarith

def binaryKL (a b : ℝ) : ℝ :=
  a*Real.log (a/b) + (1-a)*Real.log ((1-a)/(1-b))

theorem binary_data_processing {α : Type*} [Fintype α] (P Q : Law α)
    (hP : ∀ x, 0 < P.mass x) (hQ : ∀ x, 0 < Q.mass x)
    (T : Test α)
    (ha : 0 < P.expect T.one) (ha' : P.expect T.one < 1)
    (hb : 0 < Q.expect T.one) (hb' : Q.expect T.one < 1) :
    binaryKL (P.expect T.one) (Q.expect T.one) ≤ P.kl Q := by
  have he (R : Law α) : R.expect (fun x => 1-T.one x) = 1-R.expect T.one := by
    simp [Law.expect, mul_sub, Finset.sum_sub_distrib, R.total]
  have h0 := weighted_log_sum P Q hP hQ T.one T.nonneg ha hb
  have h1 := weighted_log_sum P Q hP hQ (fun x => 1-T.one x)
    (fun x => sub_nonneg.mpr (T.le_one x))
    (by rw [he]; linarith) (by rw [he]; linarith)
  rw [he, he] at h1
  have hs : P.expect (fun x => T.one x*Real.log (P.mass x/Q.mass x)) +
      P.expect (fun x => (1-T.one x)*Real.log (P.mass x/Q.mass x)) = P.kl Q := by
    rw [← Law.expect_add]
    congr 1
    funext x
    ring
  unfold binaryKL
  linarith

end PomdpLogging
