import data.mv_polynomial       -- I don't know where the coe ℤ → a ring is, but it's somewhere under here

-- lemma ring_hom_coe {α : Type*} {β : Type*} [comm_ring α] [comm_ring β] (f : α → β) [is_ring_hom f]
--   (n : ℤ) : f n = n :=
-- begin
--   sorry
-- end

-- #check int.eq_cast
-- congr_fun (int.eq_cast' (λ n, f n)) n

-- @[simp] lemma mv_polynomial.eval₂_coe {σ : Type*} {α : Type*} {β : Type*}
--   [comm_ring α] [comm_ring β] (f : α → β) [is_ring_hom f] (g : σ → β)
--   (n : ℤ) : (n : mv_polynomial σ α).eval₂ f g = n :=
-- ring_hom_coe _ _
