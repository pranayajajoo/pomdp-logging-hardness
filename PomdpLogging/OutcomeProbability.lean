import PomdpLogging.Futures

noncomputable section
open scoped BigOperators

namespace PomdpLogging

theorem Law.fst_mass {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (P : Law (α × β)) (a : α) :
    (P.map Prod.fst).mass a = ∑ b, P.mass (a,b) := by
  classical
  rw [Law.map_mass]
  unfold Law.expect
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp [mul_ite]

theorem Law.slice_expect {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (P : Law (α × β)) (a : α) (g : β → ℝ) :
    P.expect (fun ab => if a = ab.1 then g ab.2 else 0) =
      ∑ b, P.mass (a,b) * g b := by
  classical
  unfold Law.expect
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp [mul_ite]

/-- The denominator used in `outcome` equals the actual physical-state marginal. -/
theorem stateFuture_prior (θ : Bool) (k L : ℕ) (s : Bool) :
    ((stateFutureLaw θ k L).map Prod.fst).mass s = stateMass θ k s := by
  classical
  rw [Law.map_mass]
  rw [stateFuture_expect θ k L (fun s' _ => if s = s' then 1 else 0)]
  simp only [Law.expect_const]
  cases θ <;> cases s <;> simp [stateMass] <;> ring

theorem outcome_nonneg (θ : Bool) (k L : ℕ) (f : Future L) (s : Bool) :
    0 ≤ outcome θ k L f s := by
  apply div_nonneg (Law.nonneg _ _)
  linarith [stateMass_ge_third θ k s]

theorem outcome_total (θ : Bool) (k L : ℕ) (s : Bool) :
    ∑ f, outcome θ k L f s = 1 := by
  unfold outcome
  rw [← Finset.sum_div, ← Law.fst_mass, stateFuture_prior]
  apply div_self
  linarith [stateMass_ge_third θ k s]

/-- A conditional expectation under an outcome column, expressed by the
actual memory masses. This retains the logger-memory mixture explicitly. -/
theorem outcome_expect (θ : Bool) (k L : ℕ) (s : Bool) (g : Future L → ℝ) :
    (∑ f, outcome θ k L f s * g f) =
      (survival k * (if s = θ then (futureLaw θ .fresh L).expect g else 0) +
       (1-survival k)/2 * (if s = false then (futureLaw false .zero L).expect g else 0) +
       (1-survival k)/2 * (if s = true then (futureLaw true .one L).expect g else 0)) /
        stateMass θ k s := by
  classical
  calc
    _ = (stateFutureLaw θ k L).expect
        (fun sf => if s = sf.1 then g sf.2 else 0) / stateMass θ k s := by
      rw [Law.slice_expect]
      simp only [outcome, div_mul_eq_mul_div, Finset.sum_div]
    _ = _ := by
      rw [stateFuture_expect θ k L (fun s' f => if s = s' then g f else 0)]
      cases θ <;> cases s <;> simp

theorem outcome_memory_formula (θ : Bool) (k L : ℕ) (s : Bool) (f : Future L) :
    outcome θ k L f s =
      (survival k * (if s = θ then (futureLaw θ .fresh L).mass f else 0) +
       (1-survival k)/2 * (if s = false then (futureLaw false .zero L).mass f else 0) +
       (1-survival k)/2 * (if s = true then (futureLaw true .one L).mass f else 0)) /
        stateMass θ k s := by
  classical
  have h := outcome_expect θ k L s (fun f' => if f' = f then 1 else 0)
  simpa [Law.expect, mul_ite] using h

theorem outcome_pos (θ : Bool) (k L : ℕ) (f : Future L) (s : Bool) :
    0 < outcome θ k L f s := by
  have hw : 0 < survival k := survival_pos k
  have hv : 0 < (1-survival k)/2 := by linarith [survival_le_third k]
  have hp : 0 < stateMass θ k s := by linarith [stateMass_ge_third θ k s]
  rw [outcome_memory_formula]
  apply div_pos _ hp
  have hf := future_mass_pos θ .fresh L f
  have h₀ := future_mass_pos false .zero L f
  have h₁ := future_mass_pos true .one L f
  cases θ <;> cases s <;> simp <;> positivity

end PomdpLogging
