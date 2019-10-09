import
  data.mv_polynomial
  topology.instances.polynomial
  linear_algebra.determinant
  tactic

noncomputable theory

universes u v w u' v' w'

namespace finsupp

section from_finset
variables {α : Type*} {β : Type*} [has_zero β]

def from_finset (s : finset α) (f : (↑s : set α) → β) [decidable_pred (↑s : set α)] : α →₀ β :=
on_finset s
  (λ x, if h : x ∈ (↑s : set α) then f ⟨x,h⟩ else 0) $ by {intro x, split_ifs, tidy}

end from_finset

end finsupp


namespace equiv.perm
open equiv

section perm_graph
variables {α : Type*} [fintype α] (σ : perm α)

include σ
def graph : finset (α × α) := sorry

end perm_graph
end equiv.perm

namespace matrix

section Det

open_locale classical

open equiv equiv.perm finsupp
variables {α : Type u} [comm_ring α] {X : Type w} [fintype X]

instance : fintype (perm X) := sorry -- by apply_instance -- ?

def perm_term (σ : perm X) : (X × X) →₀ ℕ :=
{ support := σ.graph,
  to_fun := λ _, 1,
  mem_support_to_fun := sorry }

-- do we already know that every unit of ℤ is 1 or -1?
def unit_coe : units ℤ → units α := sorry

def Det : mv_polynomial (X × X) α :=
from_finset
  (finset.image perm_term (finset.univ : finset $ perm X))
  begin
    rintro ⟨x,Hx⟩, simp at Hx,
    exact (unit_coe $ sign $ classical.some Hx).val
  end

end Det

end matrix


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

lemma continuous_eval₂ (ϕ : α → β) (ϕ_cts : continuous ϕ) (p : mv_polynomial σ α) : continuous (λ v : σ → β, p.eval₂ ϕ v) :=
begin
  sorry
end

lemma continuous_eval (p : mv_polynomial σ α) : continuous (λ v : σ → α, p.eval v) :=
continuous_eval₂ id continuous_id p

end continuous_eval

end mv_polynomial

