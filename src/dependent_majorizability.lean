import dialectica 

variables {ι : Type} [decidable_eq ι] {gri : ground_interpretation ι} 
local notation `𝔽` := formula ι gri
local notation `𝕋` := type ι gri
variables {greq : Π {i : ι}, ∥𝕏 i // gri ∥ → ∥𝕏 i // gri ∥ → 𝔽}
local infixr `≅` : 35 := formula.eqext @greq




section 
  -- a "reverse embedding" of a fragment of Lean types into 𝕋 types,
  -- so that we may recurse on them
  inductive simple_type : Type → Type 1 
  | of_zero : simple_type ∥𝕆 // gri∥
  | of_ground (i : ι) : simple_type ∥𝕏 i // gri∥
  | of_fun {α β : Type} : simple_type α → simple_type β → simple_type (α → β)

  -- all witness and counter types are of this structure
  -- so that we may recurse on them
  inductive type_struct : Type → Type 1 
  | of_simple {α : Type} : @simple_type ι _ gri α → type_struct α
  | of_unit : type_struct unit 
  | of_prod {α β : Type} : type_struct α → type_struct β → type_struct (α × β)
  | of_sum {α β : Type} : type_struct α → type_struct β → type_struct (α ⊕ β)
  | of_fun {α β : Type} : type_struct α → type_struct β → type_struct (α → β)
  | of_pi {α : Type} {β : α → Type} : @simple_type ι _ gri α → (Π a : α, type_struct (β a)) → type_struct (Π a : α, β a)
  | of_sigma {α : Type} {β : α → Type} : @simple_type ι _ gri α → (Π a : α, type_struct (β a)) → type_struct (Σ a : α, β a)

  def simple_type_type : ∀ σ : 𝕋, @simple_type ι _ gri ∥σ∥ :=
  begin 
    intros σ,
    induction σ,
    { apply simple_type.of_zero, },
    { apply simple_type.of_ground, },
    { 
      apply simple_type.of_fun;
      assumption, 
    },
  end

  def type_struct_mwc : ∀ A : 𝔽, (@type_struct ι _ gri A.𝕎) × (@type_struct ι _ gri A.ℂ) :=
  begin 
    intros A,
    induction A,
    case prime {
      apply prod.mk; apply type_struct.of_unit,
    },
    case conjunction: B C ihB ihC {
      cases ihB, cases ihC,
      apply prod.mk;
      { apply type_struct.of_prod; assumption, }
    },
    case disjunction: B C ihB ihC {
      cases ihB, cases ihC,
      apply prod.mk,
      { apply type_struct.of_sum; assumption, },
      { apply type_struct.of_prod; assumption, },
    },
    case implication: B C ihB ihC {
      cases ihB, cases ihC,
      apply prod.mk, 
      { 
        apply type_struct.of_prod,
        { repeat {apply type_struct.of_fun}; assumption, },
        { apply type_struct.of_fun; assumption, }
      },
      { apply type_struct.of_prod; assumption, },
    },
    case universal: σ B ihB {
      change (Π (x : σ.interpret), _) at ihB,
      apply prod.mk,
      {
        apply type_struct.of_pi,
        { apply simple_type_type, },
        { intros a, specialize ihB a, exact ihB.1,},
      },
      {
        apply type_struct.of_sigma,
        { apply simple_type_type, },
        { intros a, specialize ihB a, exact ihB.2, },
      }
    },
    case existential: σ B ihB {
      change (Π (x : σ.interpret), _) at ihB,
      apply prod.mk,
      {
        apply type_struct.of_sigma,
        { apply simple_type_type, },
        { intros a, exact (ihB a).1, },
      },
      {
        apply type_struct.of_pi,
        { apply simple_type_type, },
        { 
          intros a, 
          specialize ihB a, 
          cases ihB, 
          apply type_struct.of_fun; 
          assumption, 
        },
      }
    },
  end

  -- TODO: add further type dependencies
  --       change from Π α : Type, α → α → Prop to Π (α : Type) (β γ : α → Type) (a : α), β a → γ a → Prop

  def howard_simple_type : Π {α : Type} (h : @simple_type ι _ gri α), α → α → Prop 
  | _ (simple_type.of_zero) := nat.le 
  | _ (simple_type.of_ground i) := sorry 
  | _ (@simple_type.of_fun ι _ gri α β hα hβ) := 
    λ x y, ∀ z₁ z₂ : α, howard_simple_type hα z₁ z₂ → howard_simple_type hβ (x z₁) (y z₂)

  inductive howard : Π {α : Type} {β : α → Type} {a₁ a₂ : α}, β a₁ → β a₂ → Prop 
  | of_pi {α : Type} {hα : @simple_type ι _ gri α} {β : α → Type} (x y : Π a : α, β a) :
    (∀ z₁ z₂ : α, @howard_simple_type ι _ gri α hα z₁ z₂ → @howard α β z₁ z₂ (x z₁) (y z₂)) → 
    @howard (Π a: α, β a) (λ _, (Π a : α, β a)) x y x y


  -- def howard_type_struct : Π {α : Type} {β : α → Type}
  -- works, but is not finalized (non-exhaustive)
  def howard_type_struct : Π {α : Type} {hα : @type_struct ι _ gri α}, α → α → Prop
  | _ (@type_struct.of_pi ι _ gri α β hα hβ) x y := 
    @howard ι _ gri (Π a : α, β a) (λ _, (Π a : α, β a)) x y x y
  
  -- def howard_formula (A : 𝔽) (M : A.𝕎 → Type): A.𝕎 → A.𝕎 → Prop := @howard_type_struct ι _ gri A.𝕎 M (type_struct_mwc A).1
  def howard_formula (A : 𝔽) : A.𝕎 → A.𝕎 → Prop := @howard_type_struct ι _ gri A.𝕎 (type_struct_mwc A).1

  structure major :=
  (𝕄 : Type → Type)
  (𝕄' {α : Type} : (α → Type) → (𝕄 α → Type))
  (m₁ : 𝕄 ℕ = ℕ)
  (m₂ : ∀ {α β : Type}, 𝕄 (α → β) = (𝕄 α → 𝕄 β))
  (m₃ : ∀ {α : Type} {β : α → Type}, 𝕄 (Π a : α, β a) = (Π a : 𝕄 α, 𝕄 (𝕄' β a)))

  local attribute [simp] major.m₁ major.m₂ 


  variables m : major

  def howard_simple_type' : Π {α : Type} (h : @simple_type ι _ gri α), α → m.𝕄 α → Prop
  | _ (simple_type.of_zero) := λ x y, nat.le x (cast (by simp) y)
  | _ (simple_type.of_ground i) := sorry 
  | _ (@simple_type.of_fun ι _ gri α β hα hβ) := 
    λ x y, ∀ (z₁ : α) (z₂ : m.𝕄 α), howard_simple_type' hα z₁ z₂ → howard_simple_type' hβ (x z₁) ((@cast _ (m.𝕄 α → m.𝕄 β) (by simp) y) z₂)

  set_option pp.all true

  inductive howard' : Π {α : Type} {β : α → Type} {a₁ : α} {a₂ : m.𝕄 α}, β a₁ → m.𝕄 (m.𝕄' β a₂) → Prop
  | of_pi {α : Type} {hα : @simple_type ι _ gri α} {β : α → Type} (x : Π a : α, β a) (y : m.𝕄 (Π a : α, β a)) :
    (∀ (z₁ : α) (z₂ : m.𝕄 α), howard_simple_type' m hα z₁ z₂ → @howard' α β z₁ z₂ (x z₁) ((@cast _ (Π a : m.𝕄 α, m.𝕄 (m.𝕄' β a)) (by apply major.m₃) y) z₂) → 
    @howard' (Π (a : α), β a) (λ _, (Π a : α, β a)) x _ x y

end