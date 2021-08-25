

inductive formula
| prime (p : Prop) [decidable p] : formula 

open formula 

def interpret : formula → Type  
| (@prime p _) := (unit, unit)
/-
infer type failed, unknown variable
  __mlocal__fresh_115_16
-/

