import tactic 
import utils


structure ground_interpretation (ι : Type) :=
(interpretation : ι → Type)
(inh : Π i : ι, interpretation i)

instance (ι : Type) : has_coe_to_fun (ground_interpretation ι) :=
  ⟨_, (λ gri, gri.interpretation)⟩

-- @[derive decidable_eq]
inductive type (ι : Type) (gri : ground_interpretation ι)
| zero : type 
| ground : ι → type
| arrow : type → type → type
| times : type → type → type

section basics 

  namespace type

  notation `𝕆` := zero 
  notation `𝕏` := ground 
  infixr `↣` : 50 := arrow
  infixl `⊗` : 55 := times  

  def type_plain := type empty ⟨empty.elim, (λ i, i.elim)⟩

  variables {ι : Type} {gri : ground_interpretation ι}
  local notation `𝕋` := type ι gri

  @[simp, pp_nodot]
  def interpret : 𝕋 → Type
  | 𝕆 := ℕ 
  | (𝕏 i) := gri i
  | (σ ↣ τ) := σ.interpret → τ.interpret
  | (σ ⊗ τ) := σ.interpret × τ.interpret

  -- instance : has_coe_to_sort 𝕋 := ⟨_, interpret⟩

  notation `∥` σ `∥` := type.interpret σ 
  notation `∥` σ `//` gri `∥` := @interpret _  gri σ 

  instance : has_zero ∥𝕆 // gri∥ := ⟨nat.zero⟩

  instance : linear_order ∥𝕆 // gri∥ := nat.linear_order

  -- instance (σ τ : 𝕋) : has_coe ∥σ ↣ τ∥ (∥σ∥ → ∥τ∥) := 

  def inh : Π (σ : 𝕋), ∥σ∥
  | 𝕆 := nat.zero
  | (𝕏 i) := gri.inh i 
  | (σ ↣ τ) := λ _, τ.inh
  | (σ ⊗ τ) := ⟨σ.inh, τ.inh⟩

  instance (σ : 𝕋) : inhabited ∥σ∥ := ⟨σ.inh⟩

  def cast {σ τ : 𝕋} (h : σ = τ) : ∥σ∥ → ∥τ∥ := λ x, cast (congr_arg _ h) x

  end type

end basics 

