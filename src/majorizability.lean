import dialectica 


open formula 

section 

parameters {ι : Type} {gri : ground_interpretation ι}
local notation `𝔽` := formula ι gri
local notation `𝕋` := type ι gri

-- structure majorizability :=
-- (𝕄 : 𝕋 → 𝕋)
-- (𝕄_inh : ∀ {σ : 𝕋}, ∥𝕄 σ∥)
-- (𝕄_𝕆 : 𝕄 𝕆 = 𝕆)
-- (𝕄_app : ∀ (σ τ : 𝕋), 𝕄 (σ ↣ τ) = ((𝕄 σ) ↣ (𝕄 τ)))
-- (majorizable : ∀ {σ : 𝕋}, ∥σ∥ → Prop)
-- (majorizes : ∀ {σ : 𝕋}, ∥σ∥ → ∥𝕄 σ∥ → Prop)
-- (majorizer : ∀ {σ : 𝕋} (x : ∥σ∥), {x' : ∥𝕄 σ∥ // majorizable x → majorizes x x'})
-- (majorizer_app : ∀ (σ τ : 𝕋) (x : σ) (x' : 𝕄 σ) (y : σ ↣ τ) (y' : 𝕄 (σ ↣ τ)), majorizes x x' → majorizes y y' → majorizes (y x) (y' x'))

class maj_type (𝕄 : 𝕋 → 𝕋) :=
(𝕄_𝕆 : 𝕄 𝕆 = 𝕆)
(𝕄_app (σ τ : 𝕋) : 𝕄 (σ ↣ τ) = (𝕄 σ ↣ 𝕄 τ))

attribute [simp] maj_type.𝕄_app

@[simp]
lemma l' {𝕄 : 𝕋 → 𝕋} [maj_type 𝕄] : ∥𝕄 𝕆∥ = ℕ := sorry

@[simp]
lemma l {𝕄 : 𝕋 → 𝕋} [maj_type 𝕄] {σ τ : 𝕋} : ∥𝕄 (σ ↣ τ)∥ = (∥𝕄 σ∥ → ∥𝕄 τ∥) := sorry

instance i {𝕄 : 𝕋 → 𝕋} [maj_type 𝕄] : linear_order ∥𝕄 𝕆∥ := by {
  simp only [l'],
  exact nat.linear_order,
}

structure majorizability (𝕄 : 𝕋 → 𝕋) [maj_type 𝕄] :=
(majorizes : ∀ {σ : 𝕋}, ∥σ∥ → ∥𝕄 σ∥ → Prop)
(majorizes_le : ∀ {x : ∥𝕆∥} {x' : ∥𝕄 𝕆∥}, majorizes x x' → x ≤ type.cast (maj_type.𝕄_𝕆) x')
(majorizes_app : ∀ {σ τ : 𝕋} (x : ∥σ∥) (x' : ∥𝕄 σ∥) (y : ∥σ ↣ τ∥) (y' : ∥𝕄 (σ ↣ τ)∥), 
  majorizes x x' → majorizes y y' → majorizes (y x) ((type.cast (maj_type.𝕄_app _ _) y') x'))
(majorizer : Π {σ : 𝕋}, ∥σ∥ → ∥𝕄 σ∥)
(majorizer_majorizes : ∀ {σ : 𝕋} (x : ∥σ∥), majorizes x (majorizer x))
-- attribute [simp, reducible] majorizability.𝕄_𝕆


end 

#check maj_type




