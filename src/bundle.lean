/-
Copyright (c) 2019 Jesse Michael Han. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Jesse Michael Han

Experimental definitions of vector bundles.
-/

import topology.basic topology.opens linear_algebra.finite_dimensional

universe u

-- a fiber function F : α → Type u has the structure of a vector bundle if it satisfies the following properties:
-- Σ (a : α), F a is a topological space (the total space)
-- each fiber has the structure of a finite-dimensional vector space
-- such that sigma.fst : Σ (a : α), F a → α → α is continuous
-- for every a : α, there exists a trivialization of F at a

structure vector_bundle {α} [topological_space α] (F : α → Type u) [Π a : α, add_comm_group (F a)] [Π a : α, vector_space ℝ (F a)] :=
(total_space : topological_space (Σ a : α, F a)) -- maybe we should first develop a theory of spaces over X via fiber functions
(proj_cts : continuous (sigma.fst : (Σ a : α, F a) → α))
(U : α → topological_space.opens α) -- fixed choice of trivializing cover
-- (ϕ (a : α) : U a × sorry → F a)

-- TODO: finish stating trivialization 
