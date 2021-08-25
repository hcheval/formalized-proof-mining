import formula 
import proof 

section basics 

  variables {ι : Type} [decidable_eq ι] {gri : ground_interpretation ι} 
  local notation `𝔽` := formula ι gri
  local notation `𝕋` := type ι gri
  variables {greq : Π {i : ι}, ∥𝕏 i // gri ∥ → ∥𝕏 i // gri ∥ → 𝔽}
  local infixr `≅` : 35 := formula.eqext @greq

  namespace formula 

  def nn : 𝔽 → 𝔽
  | (@prime _ _ _ p decp) := @prime _ _ _ p decp
  | (A ⋀ B) := A.nn ⋀ B.nn 
  | (A ⋁ B) := A.nn ⋁ B.nn 
  | (A ⟹ B) := A.nn ⟹ B.nn
  | (universal' σ A) := ∀∀ (x : ∥σ∥), ∼∼(A x).nn
  | (existential' σ A) := ∃∃ (x : ∥σ∥), (A x).nn

  @[reducible, simp]
  def dnt (A : 𝔽) := ∼∼A.nn

  end formula 

end basics 

section soundness 

  variables {ι : Type} [decidable_eq ι] {gri : ground_interpretation ι} 
  local notation `𝔽` := formula ι gri
  local notation `𝕋` := type ι gri
  variables {greq : Π {i : ι}, ∥𝕏 i // gri ∥ → ∥𝕏 i // gri ∥ → 𝔽}
  local infixr `≅` : 35 := formula.eqext @greq

  def clsc : principles := {with_lem := tt, with_markov := ff, with_ip := ff, with_ac := ff}
  def intu : principles := {with_lem := ff, with_markov := tt, with_ip := ff, with_ac := ff}

  open proof formula 

  local attribute [simp] nn

  #check and_contr

  example : Π (Γ) (A : 𝔽), (proof @greq intu Γ (A ⇔ A.dnt)) :=
  begin 
    intros Γ A,
    induction A,
    case prime {
      simp,
      
    }
  end 

  def dnt_sound (Γ : premises ι gri) : Π A : 𝔽,
    proof @greq clsc Γ A → 
    proof @greq intu Γ A.dnt
  | _ (lem A _):= 
  begin 
    simp,
    dsimp [dnt] at dnt_sound,
  end
    

end soundness