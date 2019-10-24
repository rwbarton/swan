import for_mathlib.embedding

lemma induced_const {α : Type*} {β : Type*} [t : topological_space β] {b : β} :
  t.induced (λ (_ : α), b) = ⊤ :=
begin
  change t.induced ((λ (_ : unit), b) ∘ (λ _, ())) = ⊤,
  rw ←induced_compose,
  convert induced_top,
  exact λ _, ()                 -- why is this needed?
end

-- plus coinduced_const
