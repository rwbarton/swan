import data.mv_polynomial linear_algebra.determinant
import for_mathlib.ring_hom_coe
noncomputable theory

universes w u

namespace matrix

section Det

variables {α : Type u} [comm_ring α] {σ : Type w} [fintype σ] [decidable_eq σ]

def Det : mv_polynomial (σ × σ) α := det (λ i j, mv_polynomial.X (i, j))

-- lemma Det_eval (M : matrix σ σ α) : Det.eval (λ ⟨i,j⟩, M i j) = det M :=

-- lemma Det_eval (M : matrix σ σ α) : (ring_hom.to_fun (mv_polynomial.eval (λ (⟨i,j⟩ : (σ × σ)), M i j))) _ = det M :=
-- TODO: There should be simp lemmas for `mv_polynomial.eval` so we don't have to unfold it here
-- by { unfold Det det mv_polynomial.eval, simp }

@[reducible]def foo (M : matrix σ σ α) : σ × σ → α := (λ ⟨i,j⟩, M i j) -- god bless lean
lemma Det_eval (M : matrix σ σ α) : det M = ring_hom.to_fun (mv_polynomial.eval $ foo M) Det := sorry
-- by { tidy,  }

end Det

end matrix
