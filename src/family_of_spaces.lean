import topology.homeomorph
import for_mathlib.embedding

universe u

structure family_of_spaces (B : Type u) [topological_space B] : Type (u+1) :=
(F : B → Type u)
(τF : Π b, topological_space (F b))
(τE : topological_space (sigma F))
(hp : continuous (sigma.fst : sigma F → B))
(hτF : ∀ b, embedding (sigma.mk b : F b → sigma F))

section trivial
-- Trivial family

variables (B : Type u) [topological_space B]
variables (F : Type u) [τF : topological_space F]

include τF
lemma fiber_embedding (b : B) : embedding (λ f, (b, f) : F → B × F) :=
let i' : unit × F → B × F := λ p, (b, p.2) in
have embedding i', from embedding.prod_mk embedding_punit embedding_id,
this.comp homeomorph.punit_prod.symm.embedding

def trivial_family : family_of_spaces B :=
{ F := λ _, F,
  τF := λ _, τF,

  τE := sorry,
  -- Need the product topology on (Σ b, F) ≃ B × F.
  -- Could define directly, or induce along this equiv

  hp := sorry,
  hτF := sorry

}
end trivial

-- Pullback

