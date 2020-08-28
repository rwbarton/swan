import
  data.mv_polynomial
  topology.algebra.polynomial
  linear_algebra.determinant
  tactic
  data.list

noncomputable theory



universes u v w u' v' w'

namespace finset

section sum_congr₂

open_locale classical

variables {α : Type u} {α' : Type u'} {β : Type v} {s₁ : finset α} {s₂ : finset α'} {f : α → β} {g : α' → β} [add_comm_monoid β]

lemma insert_comm {a a' : α} {s : finset α} : insert a (insert a' s) = insert a' (insert a s ) :=
by ext; finish

lemma erase_insert_eq_insert_erase {a a' : α} {s : finset α} (H_neq : a ≠ a') (H_mem : a' ∈ s) : erase (insert a s) a' = insert a (erase s a') :=
begin
  ext x, refine ⟨_,_⟩; intro H,
    { rw mem_erase at H, cases H with H₁ H₂, rw mem_insert at ⊢ H₂, cases H₂,
      { from or.inl ‹_› },
      { right, rw mem_erase, from ⟨‹_›,‹_›⟩ } },
    { rw mem_insert at H, cases H,
      { subst H, rw mem_erase, refine ⟨‹_›, _⟩, rw mem_insert, from or.inl rfl },
      { rw mem_erase at H ⊢, rw mem_insert, from ⟨H.left, or.inr H.right⟩ }}
end

-- lemma sum_erase {a : α} (Ha : a ∈ s₁) : f a + sum (erase s₁ a) f = sum s₁ f :=
-- begin
--   revert f a Ha, apply finset.induction_on s₁,
--     { tidy },
--     { intros a s H_new ih f a' Ha', rw mem_insert at Ha', cases Ha',
--       { subst Ha', simp[*, erase_insert] },
--       { specialize @ih f _ Ha', rw sum_insert ‹_›, rw ← ih,
--         have H_neq : a ≠ a',
--           by { intro H_eq, cc },
--         have : erase (insert a s) a' = insert a (erase s a'),
--           by exact erase_insert_eq_insert_erase H_neq ‹_›,
--         rw this, rw sum_insert _,
--           { simp },
--           { finish }}}
-- end

-- TODO: this compiles, but reformulate this in a way that avoids subtypes
-- lemma sum_congr₂ (ϕ : (↑s₁ : set α) → (↑s₂ : set α')) (Hϕ : function.bijective ϕ) (H_eq : ∀ (x : (↑s₁ : set α)), f x = g (ϕ x)) : s₁.sum f = s₂.sum g :=
-- begin
--   revert s₂ f g ϕ Hϕ H_eq, apply finset.induction_on s₁,
--     { intros s₂ f g ϕ H_bih H_eq, suffices : s₂ = ∅, by subst this; simp,
--       ext, refine ⟨_,_⟩; intro H,
--         { cases H_bih.right ⟨a, by simp*⟩, repeat{auto_cases} },
--         { cases H } },
--     { intros a s H_not_mem IH s₂ f g ϕ Hϕ H_eq,
--       rw sum_insert ‹_›, specialize @IH (s₂.erase $ ϕ ⟨a, by tidy⟩) f g _ _,
--       rotate,
--         { intro x, refine ⟨ϕ ⟨x.1, by {simp, right, from x.2}⟩, _⟩, simp,
--           refine ⟨_,_⟩,
--             { let p := _, change ↑p ∈ _, exact p.2 },
--             { intro H_eq, have := Hϕ.left (subtype.eq H_eq),
--               replace this := (congr_arg subtype.val this), dsimp at this,
--               rw ←this at H_not_mem, exact absurd x.2 ‹_› }},
--         { refine ⟨_,_⟩,
--           { intros a₁ a₂ H_eq', cases Hϕ with H_inj,
--             have := (@H_inj ⟨a₁, _⟩ ⟨a₂, _⟩ _),
--             replace this := congr_arg (λ x, subtype.val x) this,
--             dsimp at this, exact subtype.eq this,
--             {simp, right, exact a₁.2},
--             {simp, right, exact a₂.2},
--             simp at H_eq', exact subtype.eq H_eq'},
--           { rintro ⟨b, Hb⟩, simp at Hb, cases Hb with Hb₁ Hb₂,
--             cases Hϕ with _ H_surj, rcases @H_surj ⟨b, Hb₁⟩ with ⟨⟨a',Ha'₁⟩, Ha'₂⟩, simp at Ha'₁,
--             cases Ha'₁ with Ha'₁ Ha'₁,
--               { subst Ha'₁, exfalso, refine Hb₂ _,
--                 have := (congr_arg subtype.val Ha'₂), dsimp at this, rw ←this, refl },
--               { use ⟨a', ‹_›⟩, simp* } } },

--     rw IH, have := H_eq ⟨a, by tidy⟩, dsimp at this, rw this,
--     apply sum_erase,
--       { let p := _, change ↑p ∈ _, exact p.2 },
--       { rintro ⟨x,Hx_mem⟩, simp, exact H_eq ⟨x, _⟩ } }
-- end

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

lemma continuous_eval₂ (ϕ : α →+* β) [is_semiring_hom ϕ] (p : mv_polynomial σ α) : continuous (λ v : σ → β, p.eval₂ ϕ v) :=
begin
  apply mv_polynomial.induction_on p; clear p,
    { intro a, simp [continuous_const] },
    { intros p q Hp Hq, simp [continuous_add, *], continuity },
    { intros p v Hp, simp only [eval₂_mul, eval₂_X], continuity }
end

lemma continuous_eval (p : mv_polynomial σ α) : continuous (λ v : σ → α, mv_polynomial.eval v p) :=
continuous_eval₂ _ _

end continuous_eval

end mv_polynomial
