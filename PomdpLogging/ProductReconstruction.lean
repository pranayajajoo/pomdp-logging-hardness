import PomdpLogging.ProductCompression

noncomputable section
open scoped BigOperators
namespace PomdpLogging
namespace Law

def independent {I α : Type*} [Fintype I] [DecidableEq I] [Fintype α]
    (P : I → Law α) : Law (I → α) where
  mass xs := ∏ i, (P i).mass (xs i)
  nonneg xs := Finset.prod_nonneg (fun i _ => (P i).nonneg (xs i))
  total := by
    classical
    rw [← Fintype.prod_sum]
    simp [Law.total]

theorem iid_bind {α β : Type*} [Fintype α] [Fintype β] (P : Law α) (K : α → Law β) (n : ℕ) :
    (P.iid n).bind (fun xs => independent (fun i => K (xs i))) = (P.bind K).iid n := by
  classical
  ext ys
  simp only [Law.bind, Law.iid, independent]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => P.mass x*(K x).mass (ys i))).symm

end Law

def datasetReconstruction (k n : ℕ) (ws : Fin n → Symbol) : Law (Fin n → Episode k × Action) :=
  Law.independent (fun i => reconstruction k (ws i))

/-- Proposition 5.1 for arbitrary sample size: the same reconstruction kernel
works under both models, so compression loses no statistical decision information. -/
theorem reconstructs_full_dataset (θ : Bool) (k n : ℕ) :
    ((symbolLaw θ k).iid n).bind (datasetReconstruction k n) = (fullEpisodeLaw θ k).iid n := by
  unfold datasetReconstruction
  rw [Law.iid_bind, reconstructs_full_law]

end PomdpLogging
