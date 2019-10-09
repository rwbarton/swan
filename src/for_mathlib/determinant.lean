import data.mv_polynomial linear_algebra.determinant
import for_mathlib.ring_hom_coe
noncomputable theory

universes w u

namespace matrix

section Det

variables {α : Type u} [comm_ring α] {σ : Type w} [fintype σ] [decidable_eq σ]

def Det : mv_polynomial (σ × σ) α := det (λ i j, mv_polynomial.X (i, j))

lemma Det_eval (M : matrix σ σ α) : Det.eval (λ ⟨i,j⟩, M i j) = det M :=
-- TODO: There should be simp lemmas for `mv_polynomial.eval` so we don't have to unfold it here
by { unfold Det det mv_polynomial.eval, simp }

end Det

end matrix
