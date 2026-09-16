import PomdpLogging.Coarsening
import PomdpLogging.Reconstruction

noncomputable section
open scoped BigOperators
namespace PomdpLogging
namespace PositiveChannel

variable {F Z : Type*} [Fintype F] [Fintype Z] [DecidableEq Z]

def columnLaw (U : PositiveChannel F) (s : Bool) : Law F where
  mass f := U.entry f s
  nonneg f := (U.positive f s).le
  total := U.total s

theorem coarse_mass_pos (U : PositiveChannel F) (T : F → Z) (hT : Function.Surjective T)
    (s : Bool) (z : Z) : 0 < ((U.columnLaw s).map T).mass z := by
  rw [← Law.fiber_mass]
  obtain ⟨f, hf⟩ := hT z
  have hs := Finset.single_le_sum (s := Finset.univ)
    (f := fun g => if T g = z then (U.columnLaw s).mass g else 0)
    (fun g _ => by split_ifs; exact (U.positive g s).le; rfl) (Finset.mem_univ f)
  rw [if_pos hf] at hs
  exact (U.positive f s).trans_le hs

def coarse (U : PositiveChannel F) (T : F → Z) (hT : Function.Surjective T) : PositiveChannel Z where
  entry z s := ((U.columnLaw s).map T).mass z
  positive z s := U.coarse_mass_pos T hT s z
  total s := Law.total _

def fiberKernel (U : PositiveChannel F) (T : F → Z) (hT : Function.Surjective T) (z : Z) : Law F :=
  (U.columnLaw false).onFiber T z (U.coarse_mass_pos T hT false z)

theorem fiberKernel_support (U : PositiveChannel F) (T : F → Z) (hT : Function.Surjective T)
    (z : Z) (f : F) (hz : z ≠ T f) : (U.fiberKernel T hT z).mass f = 0 := by
  simp [fiberKernel, Law.onFiber, Ne.symm hz]

theorem coarse_fiber_cross (U : PositiveChannel F) (T : F → Z) (hT : Function.Surjective T)
    (hcross : ∀ f g, T f = T g → ∀ s,
      U.entry f s*U.entry g false = U.entry f false*U.entry g s) (f : F) (s : Bool) :
    U.entry f s*(U.coarse T hT).entry (T f) false =
      U.entry f false*(U.coarse T hT).entry (T f) s := by
  simp only [coarse]
  rw [← Law.fiber_mass, ← Law.fiber_mass, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : T g = T f
  · simp only [hg, ite_true, columnLaw]
    exact hcross f g hg.symm s
  · simp [hg]

theorem sufficient_reconstruction_factor (U : PositiveChannel F) (T : F → Z)
    (hT : Function.Surjective T)
    (hcross : ∀ f g, T f = T g → ∀ s,
      U.entry f s*U.entry g false = U.entry f false*U.entry g s) (f : F) (s : Bool) :
    U.entry f s = (U.fiberKernel T hT (T f)).mass f*(U.coarse T hT).entry (T f) s := by
  have hh := U.coarse_fiber_cross T hT hcross f s
  have hp := (U.coarse_mass_pos T hT false (T f)).ne'
  simp only [fiberKernel, Law.onFiber, ite_true, columnLaw]
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff hp).mpr hh

theorem sufficient_gram (U : PositiveChannel F) (T : F → Z) (hT : Function.Surjective T)
    (hcross : ∀ f g, T f = T g → ∀ s,
      U.entry f s*U.entry g false = U.entry f false*U.entry g s) :
    U.gram = (U.coarse T hT).gram :=
  U.gram_reconstruction _ T (U.fiberKernel T hT) (U.fiberKernel_support T hT)
    (U.sufficient_reconstruction_factor T hT hcross)

theorem sufficient_weightedGram (U : PositiveChannel F) (T : F → Z) (hT : Function.Surjective T)
    (hcross : ∀ f g, T f = T g → ∀ s,
      U.entry f s*U.entry g false = U.entry f false*U.entry g s)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < 1) :
    U.weightedGram ρ = (U.coarse T hT).weightedGram ρ :=
  U.weightedGram_reconstruction _ T (U.fiberKernel T hT) (U.fiberKernel_support T hT)
    (U.sufficient_reconstruction_factor T hT hcross) hρ hρ'

end PositiveChannel
end PomdpLogging
