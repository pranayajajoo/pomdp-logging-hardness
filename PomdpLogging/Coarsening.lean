import PomdpLogging.WeightedChannel
import PomdpLogging.FiniteProbability

noncomputable section
open scoped BigOperators
namespace PomdpLogging

theorem sum_kernel_fibers {F Z : Type*} [Fintype F] [Fintype Z]
    (T : F → Z) (K : Z → Law F)
    (hsupport : ∀ z f, z ≠ T f → (K z).mass f = 0) (g : Z → ℝ) :
    (∑ f, (K (T f)).mass f*g (T f)) = ∑ z, g z := by
  classical
  calc
    (∑ f, (K (T f)).mass f*g (T f)) = ∑ f, ∑ z, (K z).mass f*g z := by
      apply Finset.sum_congr rfl
      intro f _
      rw [Finset.sum_eq_single (T f)]
      · intro z _ hz
        rw [hsupport z f hz, zero_mul]
      · simp
    _ = ∑ z, ∑ f, (K z).mass f*g z := Finset.sum_comm
    _ = ∑ z, g z := by simp [← Finset.sum_mul, Law.total]

namespace PositiveChannel

variable {F Z : Type*} [Fintype F] [Fintype Z]

/-- A state-independent reconstruction kernel preserves the unweighted Gram
exactly. This theorem is used with the first-reset statistic in Appendix D. -/
theorem gram_reconstruction (U : PositiveChannel F) (V : PositiveChannel Z)
    (T : F → Z) (K : Z → Law F)
    (hsupport : ∀ z f, z ≠ T f → (K z).mass f = 0)
    (hfactor : ∀ f s, U.entry f s = (K (T f)).mass f * V.entry (T f) s) :
    U.gram = V.gram := by
  have hk (f : F) : (K (T f)).mass f ≠ 0 := by
    intro hz
    have h := hfactor f false
    rw [hz, zero_mul] at h
    exact (U.positive f false).ne' h
  ext s t
  unfold gram
  have he (f : F) : U.entry f s*U.entry f t/U.denominator f =
      (K (T f)).mass f*(V.entry (T f) s*V.entry (T f) t/V.denominator (T f)) := by
    unfold denominator
    simp_rw [hfactor]
    have hd := (V.denominator_pos (T f)).ne'
    unfold denominator at hd
    field_simp
  simp_rw [he]
  exact sum_kernel_fibers T K hsupport (fun z => V.entry z s*V.entry z t/V.denominator z)

theorem weightedGram_reconstruction (U : PositiveChannel F) (V : PositiveChannel Z)
    (T : F → Z) (K : Z → Law F)
    (hsupport : ∀ z f, z ≠ T f → (K z).mass f = 0)
    (hfactor : ∀ f s, U.entry f s = (K (T f)).mass f * V.entry (T f) s)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < 1) : U.weightedGram ρ = V.weightedGram ρ := by
  have hk (f : F) : (K (T f)).mass f ≠ 0 := by
    intro hz
    have h := hfactor f false
    rw [hz, zero_mul] at h
    exact (U.positive f false).ne' h
  ext s t
  unfold weightedGram
  congr 1
  have he (f : F) : U.entry f s*U.entry f t/U.weightedDenominator ρ f =
      (K (T f)).mass f*(V.entry (T f) s*V.entry (T f) t/V.weightedDenominator ρ (T f)) := by
    unfold weightedDenominator
    simp_rw [hfactor]
    have hd := (V.weightedDenominator_pos hρ hρ' (T f)).ne'
    unfold weightedDenominator at hd
    field_simp
  simp_rw [he]
  exact sum_kernel_fibers T K hsupport
    (fun z => V.entry z s*V.entry z t/V.weightedDenominator ρ z)

end PositiveChannel
end PomdpLogging
