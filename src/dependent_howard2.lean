import tactic 



namespace hiddenβ

  inductive simple_type 
  | natural : simple_type 
  | arrow : simple_type β simple_type β simple_type 

  local notation `π` := simple_type.natural
  local infixr `β£` : 50 := simple_type.arrow
  local notation `π` := simple_type

  @[simp]
  def simple_type.interpret : simple_type β Type 
  | simple_type.natural := β 
  | (simple_type.arrow Ο Ο) := Ο.interpret β Ο.interpret

  local notation `β₯` Ο `β₯` := Ο.interpret

  lemma simple_type.arrow_interpret_fun {Ο Ο : π} : β₯Ο β£ Οβ₯ = (β₯Οβ₯ β β₯Οβ₯) := by simp

  inductive term : π β Type 
  | zero : term π
  | K {Ο Ο : π} : term $ Ο β£ Ο β£ Ο 
  | S {Ο Ο Ο : π} : term $ (Ο β£ Ο β£ Ο) β£ (Ο β£ Ο) β£ Ο β£ Ο  
  | R {Ο : π} : term $ π β£ Ο β£ (π β£ Ο β£ Ο) β£ Ο
  | app {Ο Ο : π} : term (Ο β£ Ο) β term Ο β term Ο 

  def recursor {Ξ± : Type} : β β Ξ± β (β β Ξ± β Ξ±) β Ξ±
  | 0 y _ := y
  | (n + 1) y x := x n (recursor n y x)

  def term.interpret : Ξ  {Ο : π}, term Ο β β₯Οβ₯
  | _ term.zero := (0 : β)
  | _ (@term.K Ο Ο) := Ξ» (x) (y), x 
  | _ (@term.S Ο Ο Ο) := Ξ» x y z, x z (y z)
  | _ (@term.R Ο) := Ξ» n xβ x, nat.rec_on n xβ x 
  | Ο (@term.app Ο .(Ο) f x) := f.interpret x.interpret

  inductive type 
  | simple : π β type 
  | pi {Ο : π} : (β₯Οβ₯ β type) β type  
  
  def type.interpret : type β Type 
  | (type.simple Ο) := β₯Οβ₯
  | (@type.pi Ο Ο) := Ξ  x : β₯Οβ₯, β₯Ο xβ₯

  def howard_simple : Ξ  {Ο : π}, β₯Οβ₯ β β₯Οβ₯ β Prop
  | π x y := nat.le x y 
  | (Ο β£ Ο) x y := β zβ zβ : β₯Οβ₯, howard_simple zβ zβ β howard_simple (x zβ) (x zβ)  

  inductive howard_aux : Ξ  {Ο : type} {Ξ² : β₯Οβ₯ β type} {aβ aβ : β₯Οβ₯}, β₯Ξ² aββ₯ β β₯Ξ² aββ₯ β Prop
  | of_pi {Ο : π} {Ξ² : β₯Οβ₯ β type} (x y : β₯type.pi Ξ²β₯) : 
    (β zβ zβ : β₯Οβ₯, howard_simple zβ zβ β @howard_aux (type.simple Ο) Ξ² zβ zβ (x zβ) (y zβ)) β
    @howard_aux (@type.pi Ο Ξ²) _ x y x y
 
end hiddenβ



namespace hiddenβ 

  def typeof {Ξ± : Type} (x : Ξ±) := Ξ±

  def K {Ξ± Ξ² : Type} : Ξ± β Ξ² β Ξ± := 
    Ξ» x y, x

  def S  {Ξ± Ξ² Ξ³ : Type} : ((Ξ± β Ξ² β Ξ³) β (Ξ± β Ξ²) β Ξ± β Ξ³) := 
    (Ξ» x y z, x z (y z))

  def R {Ξ± : Type} : β β Ξ± β (Ξ± β β β Ξ±) β Ξ±
  | 0 y _ := y
  | (n + 1) y x := x (R n y x) n

  -- Godel primitive recursive functionals
  inductive gpr : Ξ  {Ξ± : Type}, Ξ± β Type 1
  | natural (n : β) : gpr n
  | K {Ξ± Ξ² : Type} : @gpr (Ξ± β Ξ² β Ξ±) K
  | S {Ξ± Ξ² Ξ³ : Type} : @gpr ((Ξ± β Ξ² β Ξ³) β (Ξ± β Ξ²) β Ξ± β Ξ³) S
  | R {Ξ± : Type} : @gpr (β β Ξ± β (Ξ± β β β Ξ±) β Ξ±) R
  -- the `id` bug
  | app {Ξ± Ξ² : Type 0} {f : Ξ± β Ξ²} {x : Ξ±} : @gpr (Ξ± β Ξ²) f β gpr x β gpr ((id f) x)

  -- which to chose?
  -- the Ξ£-version will cause universe issues, can we work around?
  def godel_primitive_recursiveβ (Ξ± : Type) := {f : Ξ± // nonempty $ gpr f}
  def godel_primitive_recursiveβ (Ξ± : Type) := Ξ£ f : Ξ±, gpr f  
  
  @[reducible, simp] def gpr.app' {Ξ± Ξ² : Type} {f : Ξ± β Ξ²} {x : Ξ±} : gpr f β gpr x β gpr (f x) := by {
    intros hβ hβ,
    apply gpr.app,
    { exact hβ},
    { exact hβ},
  }

  @[reducible, simp] def I {Ξ± : Type} : Ξ± β Ξ± := 
    S K (@K _ unit)

  example {Ξ± : Type} : @I Ξ± = @id Ξ± := by ext; simp [S, K]

  example : gpr (@I β) :=
  begin 
    simp [I],
    repeat  {apply gpr.app' };
    constructor,
  end 

  example : β {Ξ± : Type}, gpr (@id Ξ±) :=
  begin 
    intros Ξ±,
    have hβ : @I Ξ± = @id Ξ± := by ext; simp [S, K],
    have hβ : gpr (@I Ξ±) := by {
      simp only [I],
      repeat { apply gpr.app' };
      constructor,
    },
    rw hβ at hβ,
    exact hβ,
  end


  #check godel_primitive_recursiveβ
  inductive simple_type : Type β Type 1
  | natural : simple_type β 
  | function {Ξ± Ξ²} : simple_type Ξ± β simple_type Ξ² β simple_type (godel_primitive_recursiveβ $ Ξ± β Ξ²)

  inductive type : Type β Type 1
  | natural : type β 
  | function {Ξ± Ξ²} : type Ξ± β type Ξ² β type (godel_primitive_recursiveβ $ Ξ± β Ξ²)
  | pi {Ξ± : Type} {Ξ² : Ξ± β Type} : simple_type Ξ± β (Ξ  a : Ξ±, type (Ξ² a)) β type (Ξ  a : Ξ±, Ξ² a) 

  def howard_simple : Ξ  {Ξ± : Type}, simple_type Ξ± β Ξ± β Ξ± β Prop 
  | _ (simple_type.natural) x y := nat.le x y
  | _ (@simple_type.function Ξ± Ξ² hΞ± hΞ²) x y := 
    β zβ zβ : Ξ±, howard_simple hΞ± zβ zβ β howard_simple hΞ² (x.1 zβ) (y.1 zβ)

  inductive howard_aux : Ξ  {Ξ± : Type} {Ξ² : Ξ± β Type} {aβ aβ : Ξ±}, Ξ² aβ β Ξ² aβ β Prop
  | pi {Ξ± : Type} {Ξ² : Ξ± β Type} {hΞ± : simple_type Ξ±} (x y : Ξ  a : Ξ±, Ξ² a) : 
    (β zβ zβ : Ξ±, howard_simple hΞ± zβ zβ β howard_aux (x zβ) (y zβ)) β 
    @howard_aux (Ξ  a : Ξ±, Ξ² a) (Ξ» _, (Ξ  a : Ξ±, Ξ² a)) x y x y

  def howard : Ξ  {Ξ± : Type}, type Ξ± β Ξ± β Ξ± β Prop 
  | _ type.natural x y := nat.le x y
  | _ (@type.function Ξ± Ξ² hΞ± hΞ²) x y := β zβ zβ : Ξ±, howard hΞ± zβ zβ β howard hΞ² (x.1 zβ) (y.1 zβ) 
  | _ (@type.pi Ξ± Ξ² hΞ± hΞ²) x y := @howard_aux (Ξ  a : Ξ±, Ξ² a) (Ξ» _, (Ξ  a : Ξ±, Ξ² a)) x y x y

end hiddenβ


