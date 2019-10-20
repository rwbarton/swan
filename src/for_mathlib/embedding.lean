import topology.homeomorph

instance : topological_space punit := ⊥
instance : discrete_topology punit := ⟨rfl⟩


variables {α : Type*}

lemma discrete_of_singletons_open [t : topological_space α] (h : ∀ x, t.is_open {x}) :
  discrete_topology α :=
⟨eq_bot_of_singletons_open h⟩

-- Any topology on a subsingleton is discrete.
instance subsingleton.discrete_topology
  {α : Type*} [topological_space α] [subsingleton α] :
  discrete_topology α :=
discrete_of_singletons_open $ λ x, begin
  convert is_open_univ,
  exact set.eq_univ_of_forall (λ y, set.mem_singleton_of_eq (subsingleton.elim _ _))
end

instance {α : Type*} [topological_space α] [subsingleton α] :
  unique (topological_space α) :=
{ default := ⊥,
  uniq := λ t, by exactI discrete_topology.eq_bot α }

lemma embedding_subsingleton {α : Type*} [topological_space α] [subsingleton α]
  {β : Type*} [topological_space β] {f : α → β} : embedding f :=
{ induced := subsingleton.elim _ _,
  inj := λ x y _, subsingleton.elim x y }

lemma continuous_subsingleton {α : Type*} [topological_space α] [subsingleton α]
  {β : Type*} [topological_space β] {f : α → β} : continuous f :=
embedding_subsingleton.continuous

lemma embedding_punit {β : Type*} [topological_space β] {b : β} :
  embedding (λ _, b : punit → β) :=
embedding_subsingleton

def homeomorph.punit_prod {α : Type*} [topological_space α] : punit × α ≃ₜ α :=
{ continuous_to_fun := continuous_snd,
  continuous_inv_fun := show continuous (λ a, ((), a)), from
    continuous.prod_mk continuous_const continuous_id,
  .. equiv.punit_prod α }

def homeomorph.prod_punit {α : Type*} [topological_space α] : α × punit ≃ₜ α :=
{ continuous_to_fun := continuous_fst,
  continuous_inv_fun := show continuous (λ a, (a, ())), from
    continuous.prod_mk continuous_id continuous_const,
  .. equiv.prod_punit α }
