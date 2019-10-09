import
  data.mv_polynomial
  topology.instances.polynomial
  linear_algebra.determinant
  tactic

noncomputable theory

universes u v w u' v' w'

namespace finset

section sum_congr₂

open_locale classical

variables {α : Type u} {α' : Type u'} {β : Type v} {s₁ : finset α} {s₂ : finset α'} {f : α → β} {g : α' → β} [add_comm_monoid β]

lemma sum_congr₂ (ϕ : (↑s₁ : set α) → (↑s₂ : set α')) (Hϕ : function.bijective ϕ) (H_eq : ∀ (x : (↑s₁ : set α)), f x = g (ϕ x)) : s₁.sum f = s₂.sum g :=
begin
  revert s₂ f g ϕ Hϕ H_eq, apply finset.induction_on s₁,
    { intros s₂ f g ϕ H_bih H_eq, suffices : s₂ = ∅, by subst this; simp,
      ext, refine ⟨_,_⟩; intro H,
        { cases H_bih.right ⟨a, by simp*⟩, repeat{auto_cases} },
        { cases H }
      },
    { intros a s H_not_mem IH s₂ f g ϕ Hϕ H_eq,
      rw sum_insert ‹_›, specialize @IH (s₂.erase $ ϕ ⟨a, by tidy⟩) f g _ _,
      rw IH, have := H_eq ⟨a, _⟩, dsimp at this, rw this,
      repeat {sorry} }
end

end sum_congr₂

end finset

namespace mv_polynomial

section continuous_eval
variables
  {α : Type u} {β : Type v} {σ : Type*}
  [comm_semiring α]
  [comm_semiring β]
  [topological_space α]
  [topological_space β]
  [topological_semiring α]
  [topological_semiring β]

lemma continuous_eval₂ (ϕ : α → β) [is_semiring_hom ϕ] (p : mv_polynomial σ α) : continuous (λ v : σ → β, p.eval₂ ϕ v) :=
begin
  sorry
end

lemma continuous_eval (p : mv_polynomial σ α) : continuous (λ v : σ → α, p.eval v) :=
continuous_eval₂ id p

end continuous_eval

end mv_polynomial

