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
  analysis.normed_space.basic
  linear_algebra.finite_dimensional
  .family_of_spaces

universes u v

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
variables {𝕜 : Type u} [discrete_field 𝕜] [topological_space 𝕜] {B : Type u} [topological_space B]

local infix `|_`:70 := pullback_of_subset

local notation `Tot` := family_of_spaces.total_space

instance trivial_fiber.add_comm_group {F : Type u} [topological_space F] [H : add_comm_group F] {b : B} : add_comm_group ((trivial_family B F).F b) := -- by apply_instance -- fails??
H

instance pullback_subset.add_comm_group {𝓑 : fiber_bundle B} {b : B} [H : add_comm_group (𝓑.𝓕.F b)] : add_comm_group (family_of_spaces.F (𝓑.𝓕|_ (𝓑.triv_nbhd b)) ⟨b, 𝓑.triv_nbhd_mem _⟩) := H

instance trivial_fiber.vector_space {F : Type u} [topological_space F] [H_F : add_comm_group F] [H : vector_space 𝕜 F] {b : B} : vector_space 𝕜 ((trivial_family B F).F b) := -- by apply_instance -- fails??
H

instance pullback_subset.vector_space {𝓑 : fiber_bundle B} {b : B} [H_F : add_comm_group (𝓑.𝓕.F b)][H : vector_space 𝕜 (𝓑.𝓕.F b)] : vector_space 𝕜 (family_of_spaces.F (𝓑.𝓕|_ (𝓑.triv_nbhd b)) ⟨b, 𝓑.triv_nbhd_mem _⟩) := H

/- a 𝕜-vector bundle over a base space B is a fiber bundle whose fibers are all topological vector spaces over 𝕜,
and whose local trivializations' fibers are topological vector spaces and triv_homeo is a fiberwise linear map -/

variables (𝕜) (B)
structure vector_bundle extends fiber_bundle B :=
(vF1 : Π b, add_comm_group (𝓕.F b))
(vF2 : Π b, vector_space 𝕜 (𝓕.F b))
(vF3 : Π b, topological_vector_space 𝕜 (𝓕.F b))
(vF4 : Π b, add_comm_group (triv_fiber b)) -- maybe turn these into typecass arguments?
(vF5 : Π b, vector_space 𝕜 (triv_fiber b))
(vF6 : Π b, topological_vector_space 𝕜 (triv_fiber b))
(vF7 : Π b, is_linear_map 𝕜 ((triv_homeo b).to_fun.f ⟨b, triv_nbhd_mem _⟩) )

end vector_bundle

variables {𝕜 : Type u} (B : Type u) [topological_space B] [normed_field 𝕜]

def trivial_line_bundle_homeo : family_homeomorphism (pullback_of_subset (trivial_family B 𝕜) set.univ) (trivial_family (↥(set.univ : set B)) 𝕜) :=
{ to_fun := { f := λ b, id,
  hf := by { intros U HU, sorry  } },
  inv_fun := { f := λ b, id,
  hf := by { intros U HU, sorry } },
  left_inv := rfl,
  right_inv := rfl }

lemma is_linear_map_id {α R : Type*} [add_comm_group α] [comm_ring R] [module R α] : is_linear_map R (id : α → α) :=
begin
  rw [show (id : α → α) = λ x, (1 : R) • x, by ext; simp],
  exact is_linear_map.is_linear_map_smul _
end

def trivial_line_bundle  : vector_bundle 𝕜 B :=
{ 𝓕 := trivial_family B 𝕜,
  triv_nbhd := λ _, set.univ,
  triv_nbhd_open := λ _, is_open_univ,
  triv_nbhd_mem := λ _, set.mem_univ _,
  triv_fiber := λ _, 𝕜,
  triv_fiber_space := by apply_instance,
  triv_homeo :=  λ b,
    trivial_line_bundle_homeo B,
  vF1 := by apply_instance,
  vF2 := by apply_instance,
  vF3 := by sorry, -- a normed field is a topological vector space over itself
  vF4 := by apply_instance,
  vF5 := by apply_instance,
  vF6 := by sorry, -- same as vF3
  vF7 := by { intro b, simp, apply is_linear_map_id } }
