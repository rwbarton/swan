import topology.homeomorph
import for_mathlib.embedding
import for_mathlib.homeo
import for_mathlib.induced

universe u

section
-- Definition

variables (B : Type u) [topological_space B]

section data

structure family_of_spaces_data : Type (u+1) :=
(F : B → Type u)
(τF : Π b, topological_space (F b))
(τE : topological_space (sigma F))

variables {B} (p : family_of_spaces_data B) -- is `p` the best letter?

def family_of_spaces_data.total_space : Type u :=
sigma p.F

def family_of_spaces_data.p : p.total_space → B :=
sigma.fst

def family_of_spaces_data.i (b : B) : p.F b → p.total_space :=
sigma.mk b

instance family_of_spaces_data.F.topological_space (b : B) : topological_space (p.F b) :=
p.τF b

instance family_of_spaces_data.total_space.topological_space : topological_space p.total_space :=
p.τE

end data

structure family_of_spaces : Type (u+1) :=
(d : family_of_spaces_data B)
(hp : continuous d.p)
(hτF : ∀ b, embedding (d.i b))  -- We could also just use `inducing`, since it's automatically injective

variables {B} (p : family_of_spaces B)

def family_of_spaces.total_space : Type u :=
p.d.total_space

def family_of_spaces.F (b : B) : Type u :=
p.d.F b

def family_of_spaces.p : p.total_space → B :=
sigma.fst

def family_of_spaces.i (b : B) : p.F b → p.total_space :=
sigma.mk b

instance family_of_spaces.F.topological_space (b : B) : topological_space (p.F b) :=
family_of_spaces_data.F.topological_space p.d b

instance family_of_spaces.total_space.topological_space : topological_space p.total_space :=
family_of_spaces_data.total_space.topological_space p.d

end

section trivial
-- Trivial family

variables (B : Type u) [topological_space B]
variables (F : Type u) [τF : topological_space F]

include τF
lemma fiber_embedding (b : B) : embedding (λ f, (b, f) : F → B × F) :=
let i' : unit × F → B × F := λ p, (b, p.2) in
have embedding i', from embedding.prod_mk embedding_punit embedding_id,
this.comp homeomorph.punit_prod.symm.embedding

def trivial_family_data : family_of_spaces_data B :=
{ F := λ _, F,
  τF := λ _, τF,
  τE := (by apply_instance : topological_space (B × F)).induced (equiv.sigma_equiv_prod B F) }

def my_homeo : (trivial_family_data B F).total_space ≃ₜ B × F :=
homeomorph.of_equiv_induced (equiv.sigma_equiv_prod B F)

def trivial_family : family_of_spaces B :=
{ d := trivial_family_data B F,
  hp := begin
    convert continuous_fst.comp (my_homeo B F).continuous,
    exact funext (λ ⟨_, _⟩, rfl)
  end,
  hτF := λ b, (my_homeo B F).symm.embedding.comp (fiber_embedding B F b) }
end trivial

section pullback
-- Pullback/base change
-- actually, we could also define a trivial family as a pullback of a family over a point

variables {B B' : Type u} [topological_space B] [topological_space B']
variables (φ : B' → B) (hφ : continuous φ) -- hφ is unused? is that okay?
variables (p : family_of_spaces B)

def pullback : family_of_spaces B' :=
{ d :=
  { F := λ b', p.F (φ b'),
    τF := λ b', by apply_instance,
    -- E' is supposed to be the pullback B' ×_B E.
    -- That means the topology is induced by the maps E' → B', E' → E.
    τE := (by apply_instance : topological_space B').induced sigma.fst ⊓
          (by apply_instance : topological_space p.total_space).induced (λ z, ⟨φ z.1, z.2⟩) },
  hp := continuous_iff_le_induced.mpr lattice.inf_le_left,
  hτF := λ b', begin
    split,
    { constructor,
      convert induced_inf.symm using 1,
      rw [induced_compose, induced_compose],
      refine eq.trans (p.hτF (φ b')).induced _,
      refine (lattice.inf_of_le_right _).symm,
      convert lattice.le_top,
      convert induced_const,
      ext x,
      exact eq.refl b' },
    { apply injective_sigma_mk }
  end }

end pullback

section morphism

variables {B : Type u} [topological_space B] {p p' : family_of_spaces B}

def total_map (f : Π b, p.F b → p'.F b) : p.total_space → p'.total_space :=
sigma.map id f

variables (p p')

structure family_morphism :=
(f : Π b, p.F b → p'.F b)
(hf : continuous (total_map f))

def family_morphism.id : family_morphism p p :=
{ f := λ b, id,
  hf := by { convert continuous_id, ext x, cases x, refl } }

variables {p p'} {p'' : family_of_spaces B}

def family_morphism.comp (f : family_morphism p p') (g : family_morphism p' p'') :
  family_morphism p p'' :=
{ f := λ b, g.f b ∘ f.f b,
  hf := by { convert g.hf.comp f.hf, ext x, cases x, refl } }

-- Should generalize this to arbitrary families of subspaces of fibers of a family
-- (for example, also equalizer of two morphisms)
def family_morphism.range (f : family_morphism p p') : family_of_spaces B :=
{ d :=
  { F := λ b, set.range (f.f b),
    τF := by apply_instance,
    -- The image is topologized as a subspace of the total space of p'
    τE := p'.d.τE.induced (sigma.map id (λ b, subtype.val)) },
  hp := begin
    have : continuous (p'.p ∘ sigma.map id (λ b, subtype.val)), from
      p'.hp.comp (continuous_iff_le_induced.mpr (le_refl _)),
    swap,
    convert this, ext x, cases x, refl
  end,
  hτF := λ b, begin
    split,
    { constructor,
      have := (p'.hτF b).induced,
      dsimp only [family_of_spaces_data.F.topological_space, family_of_spaces_data.i,
        family_of_spaces_data.total_space.topological_space, subtype.topological_space,
        family_of_spaces.F.topological_space] at ⊢ this,
      rw [this, induced_compose, induced_compose],
      refl },
    { apply injective_sigma_mk }
  end }

end morphism
