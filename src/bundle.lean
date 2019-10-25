/-
Copyright (c) 2019 Jesse Michael Han. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Jesse Michael Han

Experimental definitions of vector bundles.
-/

import
  topology.basic
  topology.opens
  topology.algebra.module
  linear_algebra.finite_dimensional
  .family_of_spaces

universe u

section family_of_spaces

open function

variables {B : Type u} [topological_space B] (𝓕₁ 𝓕₂ : family_of_spaces B)

structure family_homeomorphism' :=
(to_fun : family_morphism 𝓕₁ 𝓕₂)
(inv_fun : family_morphism 𝓕₂ 𝓕₁)
(left_inv : left_inverse (total_map (inv_fun).f) (total_map (to_fun).f))
(right_inv : right_inverse (total_map (inv_fun).f) (total_map (to_fun).f))

structure family_homeomorphism := -- equivalent to isomorphism in Top/B?
(to_fun : family_morphism 𝓕₁ 𝓕₂)
(inv_fun : family_morphism 𝓕₂ 𝓕₁)
(left_inv : family_morphism.comp inv_fun to_fun = (family_morphism.id _))
(right_inv : family_morphism.comp to_fun inv_fun  = (family_morphism.id _))

end family_of_spaces

section fiber_bundle

variables {B : Type u} [topological_space B]

@[reducible]def pullback_of_subset (𝓕 : family_of_spaces B) (U : set B) : family_of_spaces U :=
pullback (subtype.val : U → B) 𝓕

local infix `|_`:70 := pullback_of_subset

-- a "fiber bundle" is a locally trivial family of spaces
variable (B)
structure fiber_bundle :=
(𝓕 : family_of_spaces B) -- bundled fiber bundle
(triv_nbhd : B → set B)
(triv_nbhd_open : Π b, is_open $ triv_nbhd b)
(triv_nbhd_mem : Π b, b ∈ triv_nbhd b)
(triv_fiber : B → Type u) -- this is redundant, I think? but maybe we want to be able to specify an un-definitionally equal fiber
(triv_fiber_space : Π b, topological_space $ triv_fiber b)
(triv_homeo : Π b, (family_homeomorphism
                     (𝓕 |_ (triv_nbhd b))
                     (trivial_family _ (triv_fiber b))))

end fiber_bundle

section vector_bundle
variables {B : Type u} [topological_space B] {α : Type u} [discrete_field α] [topological_space α]

local infix `|_`:70 := pullback_of_subset

local notation `Tot` := family_of_spaces.total_space

instance trivial_fiber.add_comm_group {F : Type u} [topological_space F] [H : add_comm_group F] {b : B} : add_comm_group ((trivial_family B F).F b) := -- by apply_instance -- fails??
H

instance pullback_subset.add_comm_group {𝓑 : fiber_bundle B} {b : B} [H : add_comm_group (𝓑.𝓕.F b)] : add_comm_group (family_of_spaces.F (𝓑.𝓕|_ (𝓑.triv_nbhd b)) ⟨b, 𝓑.triv_nbhd_mem _⟩) := H

instance trivial_fiber.vector_space {F : Type u} [topological_space F] [H_F : add_comm_group F] [H : vector_space α F] {b : B} : vector_space α ((trivial_family B F).F b) := -- by apply_instance -- fails??
H

instance pullback_subset.vector_space {𝓑 : fiber_bundle B} {b : B} [H_F : add_comm_group (𝓑.𝓕.F b)][H : vector_space α (𝓑.𝓕.F b)] : vector_space α (family_of_spaces.F (𝓑.𝓕|_ (𝓑.triv_nbhd b)) ⟨b, 𝓑.triv_nbhd_mem _⟩) := H

/- a vector bundle over a topological field α is a fiber bundle whose fibers are all topological vector spaces over α,
and whose local trivializations' fibers are topological vector spaces and triv_homeo is a fiberwise linear map -/
structure vector_bundle extends fiber_bundle B :=
(vF1 : Π b, add_comm_group (𝓕.F b))
(vF2 : Π b, vector_space α (𝓕.F b))
(vF3 : Π b, topological_vector_space α (𝓕.F b))
(vF4 : Π b, add_comm_group (triv_fiber b)) -- maybe turn these into typecass arguments?
(vF5 : Π b, vector_space α (triv_fiber b))
(vF6 : Π b, topological_vector_space α (triv_fiber b))
(vF7 : Π b, is_linear_map α ((triv_homeo b).to_fun.f ⟨b, triv_nbhd_mem _⟩) )

end vector_bundle
