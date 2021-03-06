import formula 
import dialectica
import utils


section basics

  variables {Î¹ : Type} {gri : ground_interpretation Î¹} 
  local notation `ð½` := formula Î¹ gri
  local notation `ð` := type Î¹ gri
  variables (greq : Î  {i : Î¹}, â¥ð i // gri â¥ â â¥ð i // gri â¥ â ð½)
  local infixr `â` : 35 := formula.eqext @greq


  structure principles := 
  (with_lem : bool := ff)
  (with_markov : bool := ff)
  (with_ip : bool := ff)
  (with_ac : bool := ff)

  @[reducible]
  def plain : principles := {}

  -- structure premises (Î¹ : Type) (gri : ground_interpretation Î¹) := 
  -- (formulas : list $ formula Î¹ gri)
  -- (realizable : Î  {Î³ : formula Î¹ gri}, Î³ â formulas â dia.realizer Î³)

  @[reducible]
  def premises (Î¹ : Type) (gri : ground_interpretation Î¹) := list $ formula Î¹ gri

  @[reducible] 
  def premises' {Î¹ : Type} {gri : ground_interpretation Î¹} := premises Î¹ gri
  

  -- instance : has_mem (formula Î¹ gri) (premises Î¹ gri) := â¨Î» A Î, A â Î.formulasâ©

  open formula 

  inductive proof 
    (extra : principles)
    (Î : list $ formula Î¹ gri)
    : ð½ â Type
  -- `id` bug
  | qfer (Ï : ð) (x y : â¥Ïâ¥) (A : â¥Ïâ¥ â ð½) : 
    proof (x â y) â proof (A (id x) â¹ A (id y))
  | and_contr (A : ð½) : proof (A â¹ A â A)
  | or_contr (A : ð½) : proof (A â A â¹ A)
  | and_weak (A B : ð½) : proof (A â B â¹ A)
  | or_weak (A B : ð½) : proof (A â¹ A â B)
  | and_perm (A B : ð½) : proof (A â B â¹ B â A)
  | or_perm (A B : ð½) : proof (A â B â¹ B â A)
  | exfalso  (A : ð½) : proof (prime false â¹ A)
  | univ_ax {Ï : ð} (A : â¥Ïâ¥ â ð½) : Î  x, proof (universal' Ï A â¹ A x)
  | exist_ax {Ï : ð} (A : â¥Ïâ¥ â ð½) : Î  x, proof (A x â¹ existential' Ï A)
  | mp {A B : ð½} : proof A â proof (A â¹ B) â proof B 
  | syl {A B C : ð½} : proof (A â¹ B) â proof (B â¹ C) â proof (A â¹ C)
  | importation {A B C : ð½} : proof (A â¹ B â¹ C) â proof (A â B â¹ C)
  | exportation {A B C : ð½} : proof (A â B â¹ C) â proof (A â¹ B â¹ C)
  | expansion {A B C : ð½} : proof (A â¹ B) â proof (C â A â¹ C â B)
  | univ_rule {Ï : ð} {A : ð½} {B : â¥Ïâ¥ â ð½} : (Î  x : â¥Ïâ¥, proof (A â¹ B x)) â proof (A â¹ universal' Ï B)
  | exist_rule {Ï : ð} {A : ð½} {B : â¥Ïâ¥ â ð½} : (Î  x : â¥Ïâ¥, proof (B x â¹ A)) â proof (existential' Ï B â¹ A)
  | ir {A : â¥ð // griâ¥ â ð½} (m : â) : proof (A 0) â (Î  (n : â), proof (A n â¹ A n.succ)) â proof (A m)
  | lem (A : ð½) : extra.with_lem â proof (A â â¼A)
  | markov {Ï : ð} {A : â¥Ïâ¥ â ð½} [â x, subsingleton (A x).ð] [â x, subsingleton (A x).â] : extra.with_markov â 
    proof (â¼(ââ (x : â¥Ïâ¥) , â¼(A x)) â¹ (ââ (x : â¥Ïâ¥) , A x))
  | ip {Ï Ï : ð} {A : â¥Ïâ¥ â ð½} {B : â¥Ïâ¥ â ð½} 
    [â x : â¥Ïâ¥, subsingleton (A x).ð] [â y : â¥Ïâ¥, subsingleton (B y).â] : extra.with_ip â
    proof (((ââ (x : â¥Ïâ¥) , A x) â¹ (ââ (y : â¥Ïâ¥) , B y)) â¹ ââ (y : â¥Ïâ¥) , ((ââ (x : â¥Ïâ¥) , A x) â¹ B y))
  | ac {Ï Ï : ð} (A : â¥Ïâ¥ â â¥Ïâ¥ â ð½) : extra.with_ac â 
    proof ((ââ (x : â¥Ïâ¥) , (ââ (y : â¥Ïâ¥) , A x y)) â¹ ââ (Y : â¥Ï â£ Ïâ¥) , ââ (x : â¥Ïâ¥) , A x (Y x))
  | premise (A : ð½) : A â Î â proof A
  | of_prime_true {p : Prop} [decidable p] : p â proof (prime p)


end basics

section basics 

  variables {Î¹ : Type}  {gri : ground_interpretation Î¹} 
  local notation `ð½` := formula Î¹ gri
  local notation `ð` := type Î¹ gri
  variables {greq : Î  {i : Î¹}, â¥ð i // gri â¥ â â¥ð i // gri â¥ â ð½}
  local infixr `â` : 35 := formula.eqext @greq
  variables {extra : principles} {Î : premises Î¹ gri} {A B : ð½}

  namespace proof 

  @[reducible, simp] def and_contr' {A : ð½} := @and_contr Î¹ gri @greq extra Î A 
  @[reducible, simp] def or_contr' {A : ð½} := @or_contr Î¹ gri @greq extra Î A
  @[reducible, simp] def and_weak' {A B : ð½} := @and_weak Î¹ gri @greq extra Î A B
  @[reducible, simp] def or_weak' {A B : ð½} := @or_weak Î¹ gri @greq extra Î A B
  @[reducible, simp] def and_perm' {A B : ð½} := @and_perm Î¹ gri @greq extra Î A B 
  @[reducible, simp] def or_perm' {A B : ð½} := @or_perm Î¹ gri @greq extra Î A B
  @[reducible, simp] def exfalso' {A : ð½} := @exfalso Î¹ gri @greq extra Î A
  @[reducible, simp] def univ_ax' {Ï : ð} {A : â¥Ïâ¥ â ð½} {x : â¥Ïâ¥} := @univ_ax Î¹ gri @greq extra Î Ï A x
  @[reducible, simp] def exist_ax' {Ï : ð} {A : â¥Ïâ¥ â ð½} {x : â¥Ïâ¥} := @exist_ax Î¹ gri @greq extra Î Ï A x


  end proof

end basics 


section schemata 

  variables {Î¹ : Type} [decidable_eq Î¹] {gri : ground_interpretation Î¹} 
  local notation `ð½` := formula Î¹ gri
  local notation `ð` := type Î¹ gri
  variables {greq : Î  {i : Î¹}, â¥ð i // gri â¥ â â¥ð i // gri â¥ â ð½}
  local infixr `â` : 35 := formula.eqext @greq
  variables {Î : premises Î¹ gri}


  namespace proof 

  local infix `â¢` : 10 := proof @greq plain 

  section substitution_of_equivalents 

    -- variables {A B P : ð½}

    -- def subst_equiv (i : â) : (Î â¢ A â B) â (Î â¢ P.substitute i A â P.substitute i A) 

    variables {A B : ð½} {P : ð½ â ð½}

    def subst_equiv (i : â) : (Î â¢ A â B) â (Î â¢ P A â P B) := sorry


  end substitution_of_equivalents
  
  section propositional

    variables {A B : ð½}

    def A_imp_A : (Î â¢ A â¹ A) := 
      syl and_contr' and_weak'

    def A_imp_B_imp_A : (Î â¢ A â¹ (B â¹ A)) := 
      exportation and_weak' 


    section double_negation 

      def qf_lem (qfA : A.is_qf) : (Î â¢ A â â¼A) := 
      begin 
            
      end

      def A_imp_neg_neg_A : (Î â¢ A â¹ â¼â¼A) := sorry 

      def neg_neg_lem : (Î â¢ â¼â¼(A â â¼A)) := sorry 

      def neg_neg_conj : (Î â¢ â¼â¼(A â B) â â¼â¼A â â¼â¼B) := sorry 

      def neg_neg_imp : (Î â¢ â¼â¼(A â¹ B) â â¼â¼A â¹ â¼â¼B) := sorry 




    end double_negation


  end propositional


  section first_order 

    open formula 

    variables {Ï Ï : ð} {A : â¥Ïâ¥ â ð½} {B : â¥Ïâ¥ â ð½}

    def univ_imp_exist : (Î â¢ universal A â¹ existential A) := 
      syl univ_ax' (exist_ax _ Ï.inh)
    -- we need an inhabitant
    -- remark, when doing this proof on paper you actually assume an inhabitant to exist

    


  end first_order


  end proof

end schemata