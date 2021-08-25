import tactic 

section tactics

  open interactive lean.parser

  meta def tactic.interactive.ss := tactic.interactive.squeeze_simp
  meta def tactic.interactive.dsimp' := tactic.interactive.squeeze_dsimp
  meta def tactic.interactive.ls := tactic.interactive.library_search

  meta def tactic.interactive.by_ext (a b x : interactive.parse lean.parser.ident) :=
  `[apply subsingleton.intro, intros a b, ext x]

end tactics

@[reducible, simp] def typeof {α : Sort*} (a : α) := α

@[reducible] def default' {α : Type*} [inhabited α] : α := default α

instance {α β : Type*} [unique α] [unique β] : unique (α × β) := 
{ default := ⟨default _, default _⟩, uniq := λ x, subsingleton.elim x (default (α × β)) }

def sum_to_prop {α β : Type*} : α ⊕ β → Prop
| (sum.inl _) := false 
| (sum.inr _) := true

def sum_imp {α β : Type*} (x y : α ⊕ β) := sum_to_prop x → sum_to_prop y


