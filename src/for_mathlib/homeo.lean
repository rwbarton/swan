import topology.homeomorph

namespace homeomorph

variables {α : Type*} {β : Type*} [t : topological_space β] (e : α ≃ β)

def of_equiv_induced : @homeomorph α β (t.induced e) t :=
{ continuous_to_fun := continuous_iff_le_induced.mpr (le_refl _),
  continuous_inv_fun := begin
    rw [continuous_iff_le_induced],
    convert le_refl _,
    rw [induced_compose],
    convert induced_id,
    ext x,
    exact e.right_inv x
  end,
  .. e}

end homeomorph
