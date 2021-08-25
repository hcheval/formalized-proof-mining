

inductive lterm 
| var : string → lterm 
| app : lterm → lterm → lterm 
| lam : string → lterm → lterm 

inductive skterm 
| var : string → skterm
| s : skterm 
| k : skterm 
| i : skterm
| app : skterm → skterm → skterm 

namespace lterm 

def is_free_var (name : string) : lterm → bool 
| (var x) := x = name
| (app t u) := is_free_var t ∨ is_free_var u 
| (lam x t) := if x = name then false else is_free_var t

instance var_to_lterm : has_coe string lterm := ⟨λ x, var x⟩

end lterm 

meta def bracket : string -> lterm → skterm 
| x (lterm.var .(x)) := skterm.i 
| x (lterm.var y) := skterm.app skterm.k (skterm.var y)
| x (lterm.app t u) := (skterm.s.app (bracket x t)).app (bracket x u)

open lterm 

meta def t : skterm := bracket "x" $ "x"

#reduce t