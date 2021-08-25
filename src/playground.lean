-- import system.io
import tactic
-- import data.equiv.basic

#print proof_irrel

def f (p q : Prop) : p ∨ q → ℕ 
| (or.inl _) := 0
| (or.inr _) := 1

def f (x : Π {n : ℕ}, n < 0) : ℕ := sorry 

def g (x : Π {n : ℕ}, n < 0) : ℕ := f x


--   example (α β γ δ ε: Type*) [unique β] [unique γ] [unique δ] [unique ε] 
--   : (α → ((ℕ → β) → (ℕ → γ → δ) → (Σ (x_1 : ℕ), ε)) × ((ℕ → β) → (Σ (x_1 : ℕ), γ))) ≃
--   (α → ℕ × ℕ)

-- open io 


example (α : Type) (x : α) : cast _ x = x := by {
  exact cast_eq rfl x,
}

example (α : Type) (a b c : α) (h : a = b) (h' : b = c) : a = c := by {
}

#check cast_cast
set_option pp.proofs true
example (α β : Type) (x : α) (h : α = β) : cast h.symm (cast h x) = x := by {
  have := cast_cast h h.symm x,
  exact this,
}
set_option pp.proofs false

-- inductive formula 
-- | conj : formula → formula → formula 
-- | disj : formula → formula → formula 

-- infixl `⋀` : 50 := formula.conj
-- infixl `⋁` : 50 := formula.disj

-- def formula.interpret : formula → Prop 
-- | (A ⋀ B) := A.interpret ∧ B.interpret 
-- | (A ⋁ B) := A.interpret ∨ B.interpret 

-- notation `∥` A `∥` := formula.interpret A

-- example (A : formula) : ∥A∥ → true := by {
--   induction A,
--   case conj {

--   }
-- }

-- example (α β : Type) (p : α → β → Prop) [unique α] [unique β] : (∃ x, ∀ y, p x y) ↔ p (default _) (default _) :=
-- begin 
--   -- obvious
--   tidy?,
-- end

-- end 


--   inductive type 
--   | ground : type 
--   | arrow : type → type → type 

--   universes u 

--   inductive is_grf : ∀ {α β : Type u}, (α → β) → Type (u + 1) 
--   | k : ∀ {α β : Type u}, is_grf (λ (x : α) (y : β), x)

--   def interpret : type → Type u
--   | type.ground := ulift ℕ 
--   | (type.arrow σ τ) := is_grf (interpret σ → interpret τ)


-- #check @grf ℕ ℕ 

-- def main : io unit := do 
--   return ()


-- section 
--   inductive T 
--   | zero : T 
--   | suc : T 
-- end 


-- section 
--   variables α β : Type* 
--   #check equiv
--   example (a : α) (p : equiv α β) : β := p a
-- end


-- example : false → false :=
-- begin 
--   my_tac h,
-- end

-- -- example (α β : Type) : subsingleton (α → β) → subsingleton β :=
-- -- begin 
-- --   intros h,
-- --   apply subsingleton.intro,
-- --   intros a b,
-- --   by_contra,
-- --   set f₁ := λ _ : α, a,
-- --   set f₂ := λ _ : α, b,
-- -- end



-- example (α : Type*) (p : α → Prop) (q : Prop) : (∀ x : α, p x → q) ↔ ((∀ x : α, p x) → q) :=
-- by {
--   split,
--   {
--     intros h h',
--     have : (∀ x : α, p x → q) ↔ (∀ x : α, ∃ _ : p x, q) := by finish,
--     have : (∀ x : α, (∃ _ : p x, q) ↔ (p x → q)) := by finish,
--     dedup,
--     simp_rw this_1 at this, 
--     have := forall_iff
--   }
-- }



-- example (α : Type) (β : α → Type) : subsingleton (Π a : α, β a) → (∀ a : α, subsingleton (β a)) := 
-- begin
  
--   intros h a,
--   apply subsingleton.intro,
--   intros x y,
--   have := @subsingleton.elim _ h,
--   by_cases h' : nonempty (Π x : α, β x),
--   {
--     rcases h' with ⟨f⟩,
--     have : x ≠ y → false := 
--     begin 
      
--     end
--     -- by_contra,
--   }
--   -- by_contradiction,
-- end



-- section 

--   -- mutual inductive even, odd 
--   -- with even : ℕ → Prop 
--   -- | even_zero : even 0 
--   -- | even_succ : ∀ n, odd n → even (n + 1)
--   -- with odd : ℕ → Prop 
--   -- | odd_succ : ∀n, even n → odd (n + 1)

--   -- #print even._mut_

-- inductive even_odd : bool → ℕ → Prop
-- | even_zero : even_odd tt 0
-- | even_succ : ∀ n, even_odd ff n → even_odd tt (n + 1)
-- | odd_succ  : ∀ n, even_odd tt n → even_odd ff (n + 1)

-- end






-- inductive bad : Π {α : Type}, α → Type 1
-- | app {α β : Type} {f : α → β} {x : α} : @bad (α → β) f → bad x → bad (f x)

-- /-
-- type mismatch at application
--   bad (α → β) f
-- term
--   f
-- has type
--   α_1 → β
-- but is expected to have type
--   α → β
-- types contain aliased name(s): α
-- remark: the tactic `dedup` can be used to rename aliases
-- -/



-- inductive ok : Π {α : Type}, α → Type 1
-- | app {α β : Type} {f : α → β} {x : α} : @ok (α → β) f → ok x → ok ((id f) x)


-- p = y₂ w₁ w₂
-- q = w₂₂ p₁
-- r = p₂ q₁ q₂


-- (A y₁ w₁).dia 
--   p₁
--   (w₂₁ p₁ p₂)


-- (A r₁ (q₁ r₁)).dia
--   (q₂ r₁)
--   r₂