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
variables {α : Type u} [comm_ring α] {σ : Type w} [fintype σ]

def indeterminate_matrix : matrix σ σ $ mv_polynomial (σ × σ) α :=
λ i j, mv_polynomial.X (i, j)

def Det : mv_polynomial (σ × σ) α := det indeterminate_matrix

def valuation_of_matrix (M : matrix σ σ α) : σ × σ → α :=
λ ⟨i,j⟩, M i j

-- TODO: characterize Det.support
lemma Det_eval (M : matrix σ σ α) : Det.eval (λ ⟨i,j⟩, M i j) = det M :=
begin
  unfold det, unfold mv_polynomial.eval mv_polynomial.eval₂ finsupp.sum,
  refine finset.sum_congr₂ _ _ _,
    { sorry },
    { sorry },
    { sorry }
end

end Det

section Det₂

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

def Det₂ : mv_polynomial (X × X) α :=
from_finset
  (finset.image perm_term (finset.univ : finset $ perm X))
  begin
    rintro ⟨x,Hx⟩, simp at Hx,
    exact (unit_coe $ sign $ classical.some Hx).val
  end

end Det₂

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

lemma continuous_eval₂ (ϕ : α → β) [is_semiring_hom ϕ] (p : mv_polynomial σ α) : continuous (λ v : σ → β, p.eval₂ ϕ v) :=
begin
  sorry
end

lemma continuous_eval (p : mv_polynomial σ α) : continuous (λ v : σ → α, p.eval v) :=
continuous_eval₂ id p

end continuous_eval

end mv_polynomial

