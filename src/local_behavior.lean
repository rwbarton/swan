import
  data.mv_polynomial
  topology.instances.polynomial

universes u v w

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
  

#print mv_polynomial.induction_on

lemma continuous_eval₂ (ϕ : α → β) (ϕ_cts : continuous ϕ) (p : mv_polynomial σ α) : continuous (λ v : σ → β, p.eval₂ ϕ v) :=
begin
  sorry
end

lemma continuous_eval (p : mv_polynomial σ α) : continuous (λ v : σ → α, p.eval v) :=
continuous_eval₂ id continuous_id p

end continuous_eval

end mv_polynomial

