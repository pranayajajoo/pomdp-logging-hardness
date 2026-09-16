import PomdpLogging.ProductInformation

noncomputable section
open scoped BigOperators
namespace PomdpLogging
namespace Law

theorem iid_map {α β : Type*} [Fintype α] [Fintype β]
    (P : Law α) (f : α → β) (n : ℕ) :
    (P.iid n).map (fun xs i => f (xs i)) = (P.map f).iid n := by
  classical
  ext ys
  rw [map_mass]
  have hind (xs : Fin n → α) :
      (if ys = (fun i => f (xs i)) then (1 : ℝ) else 0) =
        ∏ i, if ys i = f (xs i) then (1 : ℝ) else 0 := by
    rw [Fintype.prod_boole]
    split_ifs with h0 h1 h1 <;> simp_all [funext_iff]
  simp_rw [hind]
  rw [iid_expect_factors P n (fun i a => if ys i = f a then 1 else 0)]
  change (∏ i, P.expect (fun a => if ys i = f a then 1 else 0)) =
    ∏ i, (P.map f).mass (ys i)
  simp_rw [map_mass]

end Law

def compressDataset {k n : ℕ} (xs : Fin n → Episode k × Action) : Fin n → Symbol :=
  fun i => compressFull (xs i)

theorem full_dataset_compression (θ : Bool) (k n : ℕ) :
    ((fullEpisodeLaw θ k).iid n).map compressDataset = (symbolLaw θ k).iid n := by
  rw [show compressDataset = (fun xs i => compressFull (xs i)) from rfl,
    Law.iid_map, full_actual_symbol_law]

theorem full_dataset_compression_expect (θ : Bool) (k n : ℕ)
    (g : (Fin n → Symbol) → ℝ) :
    ((fullEpisodeLaw θ k).iid n).expect (fun xs => g (compressDataset xs)) =
      ((symbolLaw θ k).iid n).expect g := by
  rw [← full_dataset_compression, Law.expect_map]

end PomdpLogging
