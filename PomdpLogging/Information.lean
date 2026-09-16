import PomdpLogging.Reconstruction

noncomputable section
open scoped BigOperators

namespace PomdpLogging

/-- The discrete KL sum. Theorems using this expression below establish
strictly positive denominator masses, so no extended-real singular case is hidden. -/
def Law.kl {α : Type*} [Fintype α] (P Q : Law α) : ℝ :=
  P.expect (fun a => Real.log (P.mass a / Q.mass a))

def symbolRatio : Symbol → ℝ
  | .erased => 1
  | .zero => 3
  | .one => 1/3

theorem symbol_likelihood_ratio (k : ℕ) (w : Symbol) :
    (symbolLaw false k).mass w / (symbolLaw true k).mass w = symbolRatio w := by
  have hp := (survival_pos k).ne'
  have he := (symbol_mass_pos false k .erased).ne'
  cases w with
  | erased => exact div_self he
  | zero =>
    change (survival k * (3/4)) / (survival k * (1/4)) = 3
    field_simp
  | one =>
    change (survival k * (1/4)) / (survival k * (3/4)) = 1/3
    field_simp

theorem full_likelihood_ratio (k : ℕ) (e : Episode k × Action) :
    (fullEpisodeLaw false k).mass e / (fullEpisodeLaw true k).mass e =
      (symbolLaw false k).mass (compressFull e) / (symbolLaw true k).mass (compressFull e) := by
  apply (div_eq_div_iff (full_episode_mass_pos true k e).ne'
    (symbol_mass_pos true k (compressFull e)).ne').mpr
  simpa [mul_comm] using (likelihood_cross true k e).symm

theorem symbol_kl (k : ℕ) :
    (symbolLaw false k).kl (symbolLaw true k) = survival k / 2 * Real.log 3 := by
  unfold Law.kl
  simp_rw [symbol_likelihood_ratio]
  simp only [Law.expect, sum_symbol, symbolRatio, symbolLaw, symbolMass]
  norm_num [emission, Real.log_div]
  ring

/-- Lemma A.6: the exact one-episode KL, derived from the full trajectory law. -/
theorem full_trajectory_kl (k : ℕ) :
    (fullEpisodeLaw false k).kl (fullEpisodeLaw true k) = survival k / 2 * Real.log 3 := by
  unfold Law.kl
  simp_rw [full_likelihood_ratio]
  rw [full_compression_expect false k
    (fun w => Real.log ((symbolLaw false k).mass w / (symbolLaw true k).mass w))]
  exact symbol_kl k

end PomdpLogging
