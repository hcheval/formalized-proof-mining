import dialectica 
import proof
import realizers
import majorizability
import data.equiv.basic

section 

  parameters {ΞΉ : Type} {gri : ground_interpretation ΞΉ}
  local notation `π½` := formula ΞΉ gri
  local notation `π` := type ΞΉ gri
  variables {greq : Ξ  {i : ΞΉ}, β₯π i // gri β₯ β β₯π i // gri β₯ β π½}
  local infixr `β` : 35 := formula.eqext @greq
  

  
  open formula (π_inh' β_inh')
  set_option pp.proofs true 
  def metatheorem 
    (π : π β π) [maj_type π] (maj : majorizability π) (admissible : admissible_greq @greq)
    (Ο : π) (A B : β₯π // griβ₯ β β₯Οβ₯ β π½)
    (trivialA : β a b x y, (A a b).dia x y β β₯A a bβ₯)
    (trivialB : β a b x y, (B a b).dia x y β β₯B a bβ₯)
    (Ξ : premises')
    (premise_realizer : Ξ  {Ξ³ : π½}, Ξ³ β Ξ β dia.realizer Ξ³) 
    (prf : proof @greq {with_markov := tt, with_ip := tt} Ξ $ ββ x : β₯Οβ₯, ((ββ u : β₯πβ₯, A u x) βΉ (ββv : β₯πβ₯, B v x))) :
    {Ο : β₯π Οβ₯ β β // β (x : β₯Οβ₯) (x' : β₯π Οβ₯) (_ : maj.majorizes x x'), (β u : β, u β€ Ο x' β β₯A u xβ₯) β (β v : β, v β€ Ο x' β§ β₯B v xβ₯)}
    := 
    let β¨t, hβ© := prf.dia_realize admissible @premise_realizer in
    let y : β₯Οβ₯ β (Ξ£ (x : β₯Οβ₯), (Ξ  (x_1 : β), (A x_1 x).mwc.fst) Γ Ξ  (x_1 : β), (B x_1 x).mwc.fst β (B x_1 x).mwc.snd) 
      := Ξ» x, sigma.mk x β¨(Ξ» _, π_inh'), (Ξ» _ _, β_inh')β© in
    let tβ : β₯Οβ₯ β β := Ξ» x, ((t x).1 (Ξ» _, π_inh') (Ξ» _ _, β_inh')).1 in
    let tβ : β₯Οβ₯ β β := Ξ» x, ((t x).2 (Ξ» _, π_inh')).1 in
    have h' : (β₯Οβ₯ β β) = β₯Ο β£ πβ₯ := rfl,
    let mβ := maj.majorizer (cast h' tβ) in 
    let mβ := maj.majorizer (cast h' tβ) in 
    let mβ' := type.cast (maj_type.π_app Ο π) mβ in
    let mβ' := type.cast (maj_type.π_app Ο π) mβ in
    let mβ'' : β₯π Οβ₯ β β := Ξ» x', type.cast maj_type.π_π (type.cast (maj_type.π_app Ο π) mβ x') in 
    let mβ'' : β₯π Οβ₯ β β := Ξ» x', type.cast maj_type.π_π (type.cast (maj_type.π_app Ο π) mβ x') in
    let Ξ¦ : β₯π Οβ₯ β β := Ξ» x', (max (mβ'' x') (mβ'' x')) in 
    β¨Ξ¦, begin 
      intros x x' xmaj hA,
      use tβ x,
      split, {
        have tβ_le_mβ := maj.majorizes_le (maj.majorizes_app x x' (cast h' tβ) mβ xmaj (by simp only [cast_eq]; apply maj.majorizer_majorizes)),
        -- have : (cast h' tβ) x = tβ x := by simp,
        -- rw this at tβ_le_mβ, clear this,
        have : mβ'' x' β€ Ξ¦ x' := by { dsimp only [Ξ¦], exact le_max_right _ _, },
        exact le_trans tβ_le_mβ this, 
      }, { 
        dsimp' at h,
        simp_rw [trivialA, trivialB] at h,
        specialize h (y x),
        dsimp at h,
        have : ((t x).snd (Ξ» (_x : β), π_inh')).fst = tβ x := by refl,
        rw this at h,
        apply h,
        apply hA,
        have : ((t x).fst (Ξ» (_x : β), π_inh') (Ξ» (_x : β) (_x_1 : (B _x x).mwc.fst), β_inh')).fst = tβ x, refl,
        rw this, clear this,
        have tβ_le_mβ := maj.majorizes_le (maj.majorizes_app x x' (cast h' tβ) mβ xmaj (by simp only [cast_eq]; apply maj.majorizer_majorizes)),
        -- have : (cast h' tβ) x = tβ x := by simp,
        -- rw this at tβ_le_mβ, clear this,
        have : mβ'' x' β€ Ξ¦ x' := by { dsimp only [Ξ¦], exact le_max_left _ _, },
        exact le_trans tβ_le_mβ this,
      }
    endβ©

end

#print axioms metatheorem
  -- open formula (π_inh' β_inh')
  -- set_option pp.proofs true
  -- def metatheorem (π : π β π) [maj_type π] (maj : majorizability π) (admissible : admissible_greq @greq) {Ο : π} (A B : β₯π // griβ₯ β β₯Οβ₯ β π½) (Ξ : premises') (premise_realizer : Ξ  {Ξ³ : π½}, Ξ³ β Ξ β dia.realizer Ξ³)
  -- -- (trivialA : β x u, (A x u).dia π_inh' β_inh' β β₯A x uβ₯) (trivialB : β x v, (B x v).dia π_inh' β_inh' β β₯B x vβ₯)
  -- (prf : proof @greq {with_markov := tt, with_ip := tt} Ξ (ββ x : β₯Οβ₯, ((ββ u : β₯πβ₯, A u x) βΉ (ββ v : β₯πβ₯, B v x)))) 
  -- : {Ο : β₯π Οβ₯ β β₯π // griβ₯ // β (x : β₯Οβ₯) (x' : β₯π Οβ₯) (_ : maj.majorizes x x'), (β u : β, u β€ Ο x' β β₯A u xβ₯) β (β v : β, v β€ Ο x' β§ β₯B v xβ₯)} :=
  -- let β¨t, hβ© := prf.dia_realize admissible @premise_realizer in 
  -- by {
  --   dsimp' at t,
  --   dsimp' at h,
  --   type_check t,
  --   have trivialA : β a b x y, (A a b).dia x y β β₯A a bβ₯ := sorry,
  --   have trivialB : β a b x y, (B a b).dia x y β β₯B a bβ₯ := sorry,
  --   simp_rw [trivialA, trivialB] at h,
  --   -- set t' := Ξ» y : (Ξ£ (x : β₯Οβ₯), (Ξ  (x_1 : β), (A x_1 x).mwc.fst) Γ Ξ  (x_1 : β), (B x_1 x).mwc.fst β (B x_1 x).mwc.snd), t y.fst with ht',
  --   set y' : β₯Οβ₯ β (Ξ£ (x : β₯Οβ₯), (Ξ  (x_1 : β), (A x_1 x).mwc.fst) Γ Ξ  (x_1 : β), (B x_1 x).mwc.fst β (B x_1 x).mwc.snd) 
  --     := Ξ» x, sigma.mk x β¨(Ξ» _, π_inh'), (Ξ» _ _, β_inh')β©,
  --   set tβ := Ξ» x, (t x).1,
  --   set tβ := Ξ» x, (t x).2,
  --   let tβ' : β₯Οβ₯ β β := Ξ» x, (tβ x (y' x).2.1 (y' x).2.2).1,
  --   let tβ' : β₯Οβ₯ β β := Ξ» x, (tβ x (y' x).2.1).1,
  --   let tβ'' : β₯Οβ₯ β β := Ξ» x, (tβ x (Ξ» _, π_inh') (Ξ» _ _, β_inh')).1,
  --   let tβ'' : β₯Οβ₯ β β := Ξ» x, (tβ x (Ξ» _, π_inh')).1,
  --   have : (β₯Οβ₯ β β) = β₯Ο β£ πβ₯ := sorry,
  --   let mβ := (maj.majorizer (cast this tβ'')),
  --   let mβ := (maj.majorizer (cast this tβ'')),
  --   set mβ' := type.cast (maj_type.π_app Ο π) mβ with eq_mβ',
  --   set mβ' := type.cast (maj_type.π_app Ο π) mβ with eq_mβ', 
  --   ss at mβ',
  --   ss at mβ',
  --   let Ξ¦ : β₯π Οβ₯ β β := Ξ» x', type.cast maj_type.π_π (max (mβ' x') (mβ' x')),
    
  --   refine subtype.mk Ξ¦ _,
  --   intros x x' xmaj h',
  --   use tβ'' x,
  --   split,
  --   have := maj.majorizes_app x x' (cast this tβ'') mβ xmaj sorry,
  --   have := maj.majorizes_le this,
  --   dsimp at this,
  --   rw βeq_mβ' at this_1,
  -- }