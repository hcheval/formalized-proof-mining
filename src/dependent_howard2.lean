import tactic 



namespace hidden₂

  inductive simple_type 
  | natural : simple_type 
  | arrow : simple_type → simple_type → simple_type 

  local notation `𝕆` := simple_type.natural
  local infixr `↣` : 50 := simple_type.arrow
  local notation `𝕋` := simple_type

  @[simp]
  def simple_type.interpret : simple_type → Type 
  | simple_type.natural := ℕ 
  | (simple_type.arrow σ τ) := σ.interpret → τ.interpret

  local notation `∥` σ `∥` := σ.interpret

  lemma simple_type.arrow_interpret_fun {σ τ : 𝕋} : ∥σ ↣ τ∥ = (∥σ∥ → ∥τ∥) := by simp

  inductive term : 𝕋 → Type 
  | zero : term 𝕆
  | K {σ τ : 𝕋} : term $ σ ↣ τ ↣ σ 
  | S {σ τ ρ : 𝕋} : term $ (σ ↣ τ ↣ ρ) ↣ (σ ↣ τ) ↣ σ ↣ ρ  
  | R {σ : 𝕋} : term $ 𝕆 ↣ σ ↣ (𝕆 ↣ σ ↣ σ) ↣ σ
  | app {σ τ : 𝕋} : term (σ ↣ τ) → term σ → term τ 

  def recursor {α : Type} : ℕ → α → (ℕ → α → α) → α
  | 0 y _ := y
  | (n + 1) y x := x n (recursor n y x)

  def term.interpret : Π {σ : 𝕋}, term σ → ∥σ∥
  | _ term.zero := (0 : ℕ)
  | _ (@term.K σ τ) := λ (x) (y), x 
  | _ (@term.S σ τ ρ) := λ x y z, x z (y z)
  | _ (@term.R σ) := λ n x₀ x, nat.rec_on n x₀ x 
  | τ (@term.app σ .(τ) f x) := f.interpret x.interpret

  inductive type 
  | simple : 𝕋 → type 
  | pi {σ : 𝕋} : (∥σ∥ → type) → type  
  
  def type.interpret : type → Type 
  | (type.simple σ) := ∥σ∥
  | (@type.pi σ τ) := Π x : ∥σ∥, ∥τ x∥

  def howard_simple : Π {σ : 𝕋}, ∥σ∥ → ∥σ∥ → Prop
  | 𝕆 x y := nat.le x y 
  | (σ ↣ τ) x y := ∀ z₁ z₂ : ∥σ∥, howard_simple z₁ z₂ → howard_simple (x z₁) (x z₂)  

  inductive howard_aux : Π {σ : type} {β : ∥σ∥ → type} {a₁ a₂ : ∥σ∥}, ∥β a₁∥ → ∥β a₂∥ → Prop
  | of_pi {σ : 𝕋} {β : ∥σ∥ → type} (x y : ∥type.pi β∥) : 
    (∀ z₁ z₂ : ∥σ∥, howard_simple z₁ z₂ → @howard_aux (type.simple σ) β z₁ z₂ (x z₁) (y z₂)) →
    @howard_aux (@type.pi σ β) _ x y x y
 
end hidden₂



namespace hidden₁ 

  def typeof {α : Type} (x : α) := α

  def K {α β : Type} : α → β → α := 
    λ x y, x

  def S  {α β γ : Type} : ((α → β → γ) → (α → β) → α → γ) := 
    (λ x y z, x z (y z))

  def R {α : Type} : ℕ → α → (α → ℕ → α) → α
  | 0 y _ := y
  | (n + 1) y x := x (R n y x) n

  -- Godel primitive recursive functionals
  inductive gpr : Π {α : Type}, α → Type 1
  | natural (n : ℕ) : gpr n
  | K {α β : Type} : @gpr (α → β → α) K
  | S {α β γ : Type} : @gpr ((α → β → γ) → (α → β) → α → γ) S
  | R {α : Type} : @gpr (ℕ → α → (α → ℕ → α) → α) R
  -- the `id` bug
  | app {α β : Type 0} {f : α → β} {x : α} : @gpr (α → β) f → gpr x → gpr ((id f) x)

  -- which to chose?
  -- the Σ-version will cause universe issues, can we work around?
  def godel_primitive_recursive₁ (α : Type) := {f : α // nonempty $ gpr f}
  def godel_primitive_recursive₂ (α : Type) := Σ f : α, gpr f  
  
  @[reducible, simp] def gpr.app' {α β : Type} {f : α → β} {x : α} : gpr f → gpr x → gpr (f x) := by {
    intros h₁ h₂,
    apply gpr.app,
    { exact h₁},
    { exact h₂},
  }

  @[reducible, simp] def I {α : Type} : α → α := 
    S K (@K _ unit)

  example {α : Type} : @I α = @id α := by ext; simp [S, K]

  example : gpr (@I ℕ) :=
  begin 
    simp [I],
    repeat  {apply gpr.app' };
    constructor,
  end 

  example : ∀ {α : Type}, gpr (@id α) :=
  begin 
    intros α,
    have h₁ : @I α = @id α := by ext; simp [S, K],
    have h₂ : gpr (@I α) := by {
      simp only [I],
      repeat { apply gpr.app' };
      constructor,
    },
    rw h₁ at h₂,
    exact h₂,
  end


  #check godel_primitive_recursive₁
  inductive simple_type : Type → Type 1
  | natural : simple_type ℕ 
  | function {α β} : simple_type α → simple_type β → simple_type (godel_primitive_recursive₁ $ α → β)

  inductive type : Type → Type 1
  | natural : type ℕ 
  | function {α β} : type α → type β → type (godel_primitive_recursive₁ $ α → β)
  | pi {α : Type} {β : α → Type} : simple_type α → (Π a : α, type (β a)) → type (Π a : α, β a) 

  def howard_simple : Π {α : Type}, simple_type α → α → α → Prop 
  | _ (simple_type.natural) x y := nat.le x y
  | _ (@simple_type.function α β hα hβ) x y := 
    ∀ z₁ z₂ : α, howard_simple hα z₁ z₁ → howard_simple hβ (x.1 z₁) (y.1 z₂)

  inductive howard_aux : Π {α : Type} {β : α → Type} {a₁ a₂ : α}, β a₁ → β a₂ → Prop
  | pi {α : Type} {β : α → Type} {hα : simple_type α} (x y : Π a : α, β a) : 
    (∀ z₁ z₂ : α, howard_simple hα z₁ z₂ → howard_aux (x z₁) (y z₂)) → 
    @howard_aux (Π a : α, β a) (λ _, (Π a : α, β a)) x y x y

  def howard : Π {α : Type}, type α → α → α → Prop 
  | _ type.natural x y := nat.le x y
  | _ (@type.function α β hα hβ) x y := ∀ z₁ z₂ : α, howard hα z₁ z₂ → howard hβ (x.1 z₁) (y.1 z₂) 
  | _ (@type.pi α β hα hβ) x y := @howard_aux (Π a : α, β a) (λ _, (Π a : α, β a)) x y x y

end hidden₁


