
import Lean

section
universe u
variable (pre : Type u ) (const : Type u)  (var : Type u) [DecidableEq var] [DecidableEq pre] [DecidableEq const]
/-definition of Constructor, Predicate and their argument type-/

mutual
inductive γ  where
 | ι  : γ
 | arrow  : κ  ->  γ -> γ
deriving Repr, DecidableEq

inductive κ  where
| arrow : γ -> κ
deriving Repr, DecidableEq

inductive ρ  where
 | ο : ρ
 | arrow : σ  -> ρ  -> ρ
deriving Repr, DecidableEq

inductive σ where
 | c_arrow : γ -> σ
 | p_arrow : ρ  -> σ
deriving Repr, DecidableEq

inductive type where
 | Constructor      : γ  -> type
 | Constructor_Arg  : κ  -> type
 | Predicate        : ρ  -> type
 | Predicate_Arg    : σ  -> type
deriving Repr, DecidableEq
end
open type
def partial_function (a t) := a -> Option t
def total_function (a t) := a -> t

def TyEnv  := partial_function var type
def FunEnv := total_function const γ
def PreEnv := total_function pre ρ
def extend (pf : partial_function var type) (v : var) (t :type) (v' : var) : Option type :=  if v' = v then some t else pf v'
/-definition of Terms and type logic-/


inductive Term where
 | P    : pre     ->   Term
 | c    : const   ->   Term
 | Var  : var     ->   Term
 | app  : Term    ->   Term   ->  Term
deriving Repr

mutual
inductive Goal_formula where
  | Atomic : Term pre const var-> Goal_formula
  | true : Goal_formula
  | GandH : Goal_formula -> Goal_formula -> Goal_formula
  | exist : var -> Goal_formula -> Goal_formula
deriving Repr

inductive Definite_formula where
  | CandD : Definite_formula -> Definite_formula -> Definite_formula
  | true  : Definite_formula
  | nor_any : List (var) -> Goal_formula -> pre -> List (var) -> Definite_formula
  | cst_any : List (var) -> Goal_formula -> pre -> const -> List (var) -> Definite_formula
deriving Repr

end
open Term
open Goal_formula
open Definite_formula
deriving instance DecidableEq for Term
deriving instance DecidableEq for Goal_formula
deriving instance DecidableEq for Definite_formula
-- infixl:9 " :. " => Term.app
-- variable(a b : Term pre const var)

inductive term_has_type {fe : FunEnv const } {pi : PreEnv pre} : TyEnv var -> Term pre const var -> type -> Prop where
| Var {Δ : TyEnv var} {x : var} {τ : type} :
 Δ x = τ -> term_has_type Δ (Term.Var x) τ

| App_con {Δ : TyEnv var} {s t : Term pre const var} {left:κ} {right: γ}:
  term_has_type Δ (s) (Constructor (γ.arrow left right))
  -> term_has_type Δ t ( Constructor_Arg  left)
  -> term_has_type Δ (Term.app s t ) (Constructor right)


| App_pre {Δ : TyEnv var} {s t : Term pre const var} {left: σ} {right: ρ}:
  term_has_type Δ (s) (Predicate (ρ.arrow left right))
  -> term_has_type Δ t ( Predicate_Arg  left)
  -> term_has_type Δ (Term.app s t ) (Predicate right)

| Cst  {Δ : TyEnv var} {c : const} {y : γ} {fe : FunEnv const }:
  (fe c = y) -> term_has_type Δ (Term.c c) (type.constructor y)

| Cst_arg  {Δ : TyEnv var}   {c : const} {y : Constructor} {x : Con_arg}:
  term_has_type Δ (Term.c c) (type.constructor y)
 -> term_has_type Δ (Term.c c) (type.con_arg x)



-- end
def single_substitution (T : Term pre const var) (s : Term pre const var) (y : var)  : (Term pre const var) :=
    match T with
    | Var n => if n = y then s else T
    | app n_1 n_2 => Term.app (single_substitution n_1 s y) (single_substitution n_2 s y)
    | _ => T

def substitutions_Term : (T : Term pre const var) -> (s_bar : List (Term pre  const var)) -> (y_bar : List var) -> (Term pre const var)
| T , [] , [] => T
| T, a::as , b::bs => substitutions_Term (single_substitution pre const var T a b) as bs
| T , _ , _ => T





def helper : (T : Term pre const var) -> ( V: List var) -> Term pre const var
| T ,  []   => T
| T ,  a::as => helper (Term.app T (Term.Var a)) as

def pre_List_app : (Ps : pre) -> (V : List var) -> Term pre const var
| Ps , [] =>  Term.P Ps
| Ps , a::as => helper pre const var (Term.app (Term.P Ps) (Term.Var a)) as

def cst_List_app : (cst : const) -> (V : List var) -> Term pre const var
| Cst , [] =>  Term.c Cst
| Cst , a::as => helper pre const var (Term.app (Term.c Cst) (Term.Var a)) as

def single_goal (G : Goal_formula pre const var) (s : Term pre const var) (y : var)  : (Goal_formula pre const var) :=
    match G with
    | Goal_formula.Atomic t => Goal_formula.Atomic (single_substitution pre const var t s y)
    | Goal_formula.true => Goal_formula.true
    | Goal_formula.GandH G H => Goal_formula.GandH (single_goal G s y) (single_goal H s y)
    | Goal_formula.exist x G => Goal_formula.exist x (single_goal G s y)

def substitution : (G : Goal_formula pre const var) -> (s_bar : List (Term pre  const var)) -> (y_bar : List var) -> (Goal_formula pre const var)
| T , [] , [] => T
| G, a::as , b::bs => substitution (single_goal pre const var G a b) as bs
| G , _, _  => G

def break_ (D : Definite_formula pre const var) :  Prod (Goal_formula pre const var) (Goal_formula pre const var) :=
    match D with
    | Definite_formula.true => (Goal_formula.true , Goal_formula.true)
    | Definite_formula.nor_any _ G p v => (G , Goal_formula.Atomic (pre_List_app pre const var p v))
    | Definite_formula.cst_any _ G p cst v =>  (G , Goal_formula.Atomic (Term.app (Term.P p) (cst_List_app pre const var cst v)))
    | Definite_formula.CandD _ _=>  (Goal_formula.true , Goal_formula.true)



inductive Goal_formula_has_type : TyEnv var-> Goal_formula pre const var-> type -> Prop
  | True  {Δ : TyEnv var} {G : true } {o : Prop} :
  Goal_formula_has_type  Δ  (Goal_formula.true) (type.predicate Predicate.o)

  | And  {Δ : TyEnv var} {G H: Goal_formula pre const var} {o : Prop} :
  Goal_formula_has_type Δ G (type.predicate Predicate.o)
  -> Goal_formula_has_type Δ H (type.predicate Predicate.o)
  -> Goal_formula_has_type Δ (Goal_formula.GandH G H) (type.predicate Predicate.o)

  | Ex {Δ : TyEnv var} { new : TyEnv var} {empty : TyEnv var}{G : Goal_formula pre const var} {x : var} {sigma: Pre_arg}:
  term_has_type pre const var empty (Term.Var x) (type.pre_arg sigma)
  -> Goal_formula_has_type  Δ  G  (type.predicate Predicate.o)
  -> Goal_formula_has_type  new  (Goal_formula.exist x G) (type.predicate Predicate.o)

  -- | CI {Δ : TyEnv var} { new : TyEnv var} {Ly : List (Term pre const var)} {G : Goal_formula const pre var} {A : Term pre const var} :
  -- term_has_type const pre var Δ Ly

inductive Prove_Goal_formula: List (Definite_formula pre const var) -> Goal_formula pre const var-> Prop
| T {D :List (Definite_formula pre const var) } :
  Prove_Goal_formula D Goal_formula.true
|And {D :List (Definite_formula pre const var) } {G H :Goal_formula pre const var }:
  Prove_Goal_formula D G
  -> Prove_Goal_formula D H
  -> Prove_Goal_formula D (Goal_formula.GandH G H)
| Ex {D :List (Definite_formula pre const var) } (t : Term pre const var) {x : var} {G : Term pre const var}:
Prove_Goal_formula D (Goal_formula.Atomic (single_substitution pre const var G t x))
-> Prove_Goal_formula D (Goal_formula.exist x (Goal_formula.Atomic G))

| Res {D : List (Definite_formula pre const var)}{ y_bar: List (var)} {s_bar: List (Term pre const var)}{ G A: Goal_formula pre const var} {D_ : Definite_formula pre const var}:
substitution pre const var (break_ pre const var D_).fst  s_bar y_bar = G  ->
substitution pre const var (break_ pre const var D_).snd s_bar y_bar = A ->
Prove_Goal_formula D G->
Prove_Goal_formula D A

end
/- section end-/


namespace LazyIO

inductive pre_set where
 | V : pre_set
 | Ex : pre_set
 | Open : pre_set
 | Closed : pre_set
deriving Repr


inductive con_set where
 | o : con_set
 | c : con_set
 | bracket : con_set
 | colon : con_set
 | test_txt :con_set
 | ReadMode : con_set
 | hGetContent : con_set
 | withFile   : con_set
 | withFile_1 : con_set
 | withFile_2 : con_set
 | withFile_3 : con_set
 | act_2 : con_set
 | open : con_set
 | close : con_set
 | read: con_set
 | id : con_set
 | putStrLn : con_set
 | putCont : con_set
deriving Repr

inductive var_set where
| x : var_set
| f : var_set
| m : var_set
| h_0 : var_set
| h : var_set
| h_1 : var_set
| h_2 : var_set
| h_3: var_set
| k : var_set
| y : var_set
deriving Repr


deriving instance DecidableEq for pre_set
deriving instance DecidableEq for con_set
deriving instance DecidableEq for var_set
open var_set
open pre_set
open con_set

def D_5 : Definite_formula pre_set con_set var_set :=  Definite_formula.cst_any [h,k] (Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.Var k) (Term.c o)))) V con_set.open [h,k]
def D_6 : Definite_formula pre_set con_set var_set :=  Definite_formula.cst_any [h,k] (Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.Var k) (Term.c c)))) V con_set.close [h,k]
def D_7 : Definite_formula pre_set con_set var_set := Definite_formula.cst_any [h, k] (Goal_formula.Atomic (Term.app (Term.P Closed) (Term.Var h))) V con_set.read [h, k]
def D_10 : Definite_formula pre_set con_set var_set := Definite_formula.cst_any [x, h, k] (Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.Var x) (Term.Var h)) (Term.app (Term.c putCont) (Term.Var k))))) V con_set.putStrLn [x, h, k]
/- D_11 correspondingt the goal-/
def D_11 : Definite_formula pre_set con_set var_set := Definite_formula.cst_any [x , m , f , h , k] (Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.c con_set.open) (Term.Var h)) (Term.app (Term.app (Term.c con_set.withFile_1) (Term.Var f)) (Term.Var k))))) V con_set.withFile [x,m,f,h,k]
def D_12 : Definite_formula pre_set con_set var_set := Definite_formula.cst_any [f, k ,h_0] (Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.Var f) (Term.Var h_0)) (Term.app (Term.c con_set.withFile_2) (Term.Var k))))) V con_set.withFile_1 [f, k , h_0]
def D_13 : Definite_formula pre_set con_set var_set := Definite_formula.cst_any [k, h_1, y] (Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.c con_set.close) (Term.Var h_1)) (Term.app (Term.app (Term.c con_set.withFile_3) (Term.Var y)) (Term.Var k))))) V con_set.withFile_2 [k, h_1, y]
def D_14 : Definite_formula pre_set con_set var_set := Definite_formula.cst_any [y, k ,h_2] (Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.Var k) (Term.Var y)) (Term.Var h_2)))) V con_set.withFile_3 [y, k ,h_2]
def D_15 : Definite_formula pre_set con_set var_set := Definite_formula.cst_any  [h, k] (Goal_formula.GandH (Goal_formula.Atomic (Term.app (Term.P Open) (Term.Var h))) (Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.Var k) (Term.c o)) (Term.c con_set.read))))) V con_set.hGetContent [h,k]
def D_16 : Definite_formula pre_set con_set var_set := Definite_formula.cst_any [x, h_3]  (Goal_formula.Atomic (Term.app (Term.P V ) (Term.app  (Term.app (Term.app (Term.c con_set.putStrLn) (Term.Var var_set.x)) (Term.Var var_set.h_3)) (Term.c id)))) V con_set.act_2 [x, h_3]
def D_17 : Definite_formula pre_set con_set var_set := Definite_formula.cst_any [] Goal_formula.true pre_set.Open con_set.o []
def D_18 : Definite_formula pre_set con_set var_set := Definite_formula.cst_any [] Goal_formula.true pre_set.Closed con_set.c []


def D : List (Definite_formula pre_set con_set var_set) := [D_5, D_6, D_7, D_10, D_11,D_12, D_13, D_14,D_15, D_16,D_17, D_18]

theorem base_ : Prove_Goal_formula pre_set con_set var_set D Goal_formula.true :=  Prove_Goal_formula.T

theorem eighteen_ : Prove_Goal_formula pre_set con_set var_set D (Goal_formula.Atomic (Term.app (Term.P Closed) (Term.c c))) :=
have sub_1: substitution pre_set con_set var_set (break_ pre_set con_set var_set D[11]).fst [] [] = substitution pre_set con_set var_set Goal_formula.true [] []  := by rfl
have sub_2 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[11]).snd [] [] =  (Goal_formula.Atomic (Term.app (Term.P Closed) (Term.c c))) := by rfl
Prove_Goal_formula.Res sub_1 sub_2 base_

theorem seven_: Prove_Goal_formula pre_set con_set var_set D  (Goal_formula.Atomic (Term.app (Term.P V ) (Term.app (Term.app (Term.c con_set.read) (Term.c con_set.c)) (Term.app (Term.c con_set.putCont) (Term.c id))))) :=
 have sub_1 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[2]).fst [(Term.c con_set.c), (Term.app (Term.c con_set.putCont) (Term.c id))] [var_set.h, var_set.k] =
substitution pre_set con_set var_set (Goal_formula.Atomic (Term.app (Term.P Closed) (Term.c c))) [] []  := by rfl
have sub_2 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[2]).snd [(Term.c con_set.c), (Term.app (Term.c con_set.putCont) (Term.c id))] [var_set.h, var_set.k] = (Goal_formula.Atomic (Term.app (Term.P V ) (Term.app (Term.app (Term.c con_set.read) (Term.c con_set.c)) (Term.app (Term.c con_set.putCont) (Term.c id))))) := by rfl
Prove_Goal_formula.Res sub_1 sub_2 eighteen_

theorem ten_:Prove_Goal_formula pre_set con_set var_set D (Goal_formula.Atomic (Term.app (Term.P V ) (Term.app (Term.app (Term.app (Term.c con_set.putStrLn) (Term.c con_set.read)) ( Term.c c))  (Term.c id)))) :=
have sub_1: substitution pre_set con_set var_set (break_ pre_set con_set var_set D[3]).fst [Term.c con_set.read, Term.c c, Term.c id] [x, h, k]=
(substitution pre_set con_set var_set (Goal_formula.Atomic (Term.app (Term.P V ) (Term.app (Term.app (Term.c con_set.read) (Term.Var var_set.h)) (Term.Var var_set.k))))
[(Term.c con_set.c), (Term.app (Term.c con_set.putCont) (Term.c id))] [var_set.h, var_set.k]) := by rfl
have sub_2 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[3]).snd [Term.c con_set.read, Term.c c, Term.c id] [x, h, k] =
(Goal_formula.Atomic (Term.app (Term.P V ) (Term.app (Term.app (Term.app (Term.c con_set.putStrLn) (Term.c con_set.read)) ( Term.c c))  (Term.c id)))) := by rfl
Prove_Goal_formula.Res sub_1 sub_2 seven_

theorem sixteen_ : Prove_Goal_formula pre_set con_set var_set D (Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.c act_2) (Term.c con_set.read)) (Term.c c))))  :=
have sub_1 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[9]).fst [Term.c con_set.read, Term.c con_set.c] [x, h_3] =
(substitution pre_set con_set var_set (Goal_formula.Atomic (Term.app (Term.P V ) (Term.app (Term.app (Term.app (Term.c con_set.putStrLn) (Term.Var var_set.x)) (Term.Var var_set.h))  (Term.Var k)))) [Term.c con_set.read , Term.c c , Term.c id] [x, h, k])  := by rfl
have sub_2 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[9]).snd [Term.c con_set.read, Term.c con_set.c] [x, h_3] =
(Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.c act_2) (Term.c con_set.read)) (Term.c c)))) := by rfl
Prove_Goal_formula.Res sub_1 sub_2 ten_


theorem fourteen_ : Prove_Goal_formula pre_set con_set var_set D (Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.app (Term.c con_set.withFile_3) (Term.c con_set.read)) (Term.c act_2)) (Term.c c))))  :=
have sub_1:  substitution pre_set con_set var_set (break_ pre_set con_set var_set D[7]).fst [Term.c act_2, Term.c con_set.read, Term.c c] [k, y, h_2] =  (substitution pre_set con_set var_set (Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.c act_2) (Term.Var x)) (Term.Var h_3)))) [Term.c con_set.read, Term.c c] [x, h_3]) := by rfl
have sub_2 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[7]).snd [Term.c act_2, Term.c con_set.read, Term.c c] [k, y, h_2] =
(Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.app (Term.c con_set.withFile_3) (Term.c con_set.read)) (Term.c act_2)) (Term.c c)))) := by rfl
Prove_Goal_formula.Res sub_1 sub_2 sixteen_


theorem six_ : Prove_Goal_formula pre_set con_set var_set D  (Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.c con_set.close) (Term.c o)) ( Term.app (Term.app (Term.c con_set.withFile_3) (Term.c con_set.read)) (Term.c con_set.act_2))))) :=
 have sub_1 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[1]).fst [Term.c o, Term.app (Term.app (Term.c con_set.withFile_3) (Term.c con_set.read)) (Term.c con_set.act_2)] [h, k] =
 (substitution pre_set con_set var_set (Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.app (Term.c con_set.withFile_3) (Term.Var y)) (Term.Var k)) (Term.Var h_2)))) [Term.c act_2, Term.c con_set.read, Term.c c] [k, y, h_2] ) := by rfl
have sub_2 :  substitution pre_set con_set var_set (break_ pre_set con_set var_set D[1]).snd [Term.c o, Term.app (Term.app (Term.c con_set.withFile_3) (Term.c con_set.read)) (Term.c con_set.act_2)] [h, k] =
 (Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.c con_set.close) (Term.c o)) ( Term.app (Term.app (Term.c con_set.withFile_3) (Term.c con_set.read)) (Term.c con_set.act_2))))) := by rfl
 Prove_Goal_formula.Res sub_1 sub_2 fourteen_


theorem thirteen_ : Prove_Goal_formula pre_set con_set var_set D (Goal_formula.Atomic (Term.app (Term.P V) (Term.app ((Term.app ((Term.app (Term.c con_set.withFile_2) (Term.c act_2))) (Term.c o))) (Term.c con_set.read))))  :=
have sub_1 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[6]).fst [Term.c act_2, Term.c o, Term.c con_set.read] [k, h_1, y] = (substitution pre_set con_set var_set (Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.c con_set.close) (Term.Var h)) (Term.Var k))))
 [Term.c o, Term.app (Term.app (Term.c con_set.withFile_3) (Term.c con_set.read)) (Term.c con_set.act_2)] [h, k]) := by rfl
have sub_2 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[6]).snd  [Term.c act_2, Term.c o, Term.c con_set.read] [k, h_1 ,y] = (Goal_formula.Atomic (Term.app (Term.P V) (Term.app ((Term.app ((Term.app (Term.c con_set.withFile_2) (Term.c act_2))) (Term.c o))) (Term.c con_set.read)))) := by rfl
Prove_Goal_formula.Res sub_1 sub_2 six_

theorem seventeen_ : Prove_Goal_formula pre_set con_set var_set D (Goal_formula.Atomic (Term.app (Term.P Open) (Term.c o))) :=
have sub_1: substitution pre_set con_set var_set (break_ pre_set con_set var_set D[10]).fst [] [] = substitution pre_set con_set var_set Goal_formula.true [] []  := by rfl
have sub_2 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[10]).snd [] [] =  (Goal_formula.Atomic (Term.app (Term.P Open) (Term.c o))) := by rfl
Prove_Goal_formula.Res sub_1 sub_2 base_

theorem combine_ :Prove_Goal_formula pre_set con_set var_set D (Goal_formula.GandH (Goal_formula.Atomic (Term.app (Term.P Open) (Term.c o))) (Goal_formula.Atomic (Term.app (Term.P V) (Term.app ((Term.app ((Term.app (Term.c con_set.withFile_2) (Term.c act_2))) (Term.c o))) (Term.c con_set.read))))) :=
Prove_Goal_formula.And seventeen_ thirteen_

theorem fifteen_ : Prove_Goal_formula pre_set con_set var_set D (Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.c con_set.hGetContent) ( Term.c o)) (Term.app (Term.c con_set.withFile_2) (Term.c act_2))))) :=
have sub_1 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[8]).fst [Term.c o, Term.app (Term.c con_set.withFile_2) (Term.c act_2)] [h , k] =
(@Goal_formula.GandH pre_set con_set var_set (Goal_formula.Atomic (Term.app (Term.P Open) (Term.c o))) (Goal_formula.Atomic (Term.app (Term.P V) (Term.app ((Term.app ((Term.app (Term.c con_set.withFile_2) (Term.c act_2))) (Term.c o))) (Term.c con_set.read))))) := by rfl
have sub_2 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[8]).snd [Term.c o, Term.app (Term.c con_set.withFile_2) (Term.c act_2)] [h , k] =
 (Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.c con_set.hGetContent) ( Term.c o)) (Term.app (Term.c con_set.withFile_2) (Term.c act_2))))) := by rfl
 Prove_Goal_formula.Res sub_1 sub_2 combine_

theorem twelve_ : Prove_Goal_formula pre_set con_set var_set D (Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.app (Term.c con_set.withFile_1) ( Term.c con_set.hGetContent)) (Term.c act_2)) (Term.c o)))) :=
have sub_1 :  substitution pre_set con_set var_set (break_ pre_set con_set var_set D[5]).fst [Term.c con_set.hGetContent, Term.c act_2, Term.c o] [f, k, h_0] =
(Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.c con_set.hGetContent) ( Term.c o)) (Term.app (Term.c con_set.withFile_2) (Term.c act_2))))) := by rfl
have sub_2 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[5]).snd [Term.c con_set.hGetContent, Term.c act_2, Term.c o] [f, k, h_0] =
(Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.app (Term.c con_set.withFile_1) ( Term.c con_set.hGetContent)) (Term.c act_2)) (Term.c o)))) := by rfl
Prove_Goal_formula.Res sub_1 sub_2 fifteen_

theorem five_ : Prove_Goal_formula pre_set con_set var_set D (Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.c con_set.open) ( Term.c c )) (Term.app (Term.app (Term.c con_set.withFile_1) (Term.c con_set.hGetContent)) (Term.c act_2))))) :=
have sub_1 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[0]).fst [Term.c c, Term.app (Term.app (Term.c con_set.withFile_1) (Term.c con_set.hGetContent)) (Term.c act_2)] [h, k] =
(Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.app (Term.c con_set.withFile_1) ( Term.c con_set.hGetContent)) (Term.c act_2)) (Term.c o)))) := by rfl
have sub_2 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[0]).snd [Term.c c, Term.app (Term.app (Term.c con_set.withFile_1) (Term.c con_set.hGetContent)) (Term.c act_2)] [h, k] =
(Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.c con_set.open) ( Term.c c )) (Term.app (Term.app (Term.c con_set.withFile_1) (Term.c con_set.hGetContent)) (Term.c act_2))))) := by rfl
Prove_Goal_formula.Res sub_1 sub_2 twelve_

theorem eleven_ : Prove_Goal_formula pre_set con_set var_set D (Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.app (Term.app (Term.app (Term.c con_set.withFile) (Term.c con_set.test_txt)) (Term.c con_set.ReadMode)) (Term.c con_set.hGetContent)) (Term.c c)) (Term.c act_2)))) :=
have sub_1: substitution pre_set con_set var_set (break_ pre_set con_set var_set D[4]).fst [ Term.c con_set.test_txt, Term.c con_set.ReadMode, Term.c con_set.hGetContent, Term.c c, Term.c act_2] [x, m, f, h, k] =
(Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.c con_set.open) ( Term.c c )) (Term.app (Term.app (Term.c con_set.withFile_1) (Term.c con_set.hGetContent)) (Term.c act_2))))) := by rfl
have sub_2: substitution pre_set con_set var_set (break_ pre_set con_set var_set D[4]).snd [ Term.c con_set.test_txt, Term.c con_set.ReadMode, Term.c con_set.hGetContent, Term.c c, Term.c act_2] [x, m, f, h, k] =
(Goal_formula.Atomic (Term.app (Term.P V) (Term.app (Term.app (Term.app (Term.app (Term.app (Term.c con_set.withFile) (Term.c con_set.test_txt)) (Term.c con_set.ReadMode)) (Term.c con_set.hGetContent)) (Term.c c)) (Term.c act_2)))) := by rfl
Prove_Goal_formula.Res sub_1 sub_2 five_

end LazyIO


namespace simple
 /-con set and pre set-/  /-con set and pre set-/  /-con set and pre set-/  /-con set and pre set-/  /-con set and pre set-/
inductive con_set where
 | z : con_set
 | s : con_set


inductive pre_set where
 | a : pre_set

inductive var_set where
|  v : var_set
 /-con set and pre set-/  /-con set and pre set-/  /-con set and pre set-/  /-con set and pre set-/  /-con set and pre set-/

def map (x :con_set):=
  match x with
    | con_set.z => Constructor.individual
    | con_set.s => Constructor.C  (Con_arg.ctoc Constructor.individual ) Constructor.individual


def maps (x : pre_set):=
  match x with
   | pre_set.a => Predicate.o


def mapss (x : var_set)  :=
  match x with
    | var_set.v => some (type.constructor Constructor.individual)


variable (z s :const ) (v : var) (TE : TyEnv var_set) (provez : map con_set.z = Constructor.individual) (proves  : map con_set.s = Constructor.C  (Con_arg.ctoc Constructor.individual ) Constructor.individual)


example : @term_has_type pre_set con_set var_set  map  maps mapss (Term.app (Term.c con_set.s) (Term.c con_set.z)) (type.constructor Constructor.individual) :=
have pz : term_has_type pre_set con_set var_set mapss (Term.c con_set.z) (type.con_arg (Con_arg.ctoc Constructor.individual)) :=
have sub_pz : term_has_type pre_set con_set var_set mapss (Term.c con_set.z) (type.constructor Constructor.individual) :=
show term_has_type pre_set con_set var_set mapss (Term.c con_set.z) (type.constructor Constructor.individual) from term_has_type.Cst provez
show term_has_type pre_set con_set var_set mapss (Term.c con_set.z) (type.con_arg (Con_arg.ctoc Constructor.individual))
from term_has_type.Cst_arg sub_pz

have ps : term_has_type pre_set con_set var_set mapss (Term.c con_set.s) (type.constructor (Constructor.C  (Con_arg.ctoc Constructor.individual ) Constructor.individual)) :=
show term_has_type pre_set con_set var_set mapss (Term.c con_set.s) (type.constructor (Constructor.C  (Con_arg.ctoc Constructor.individual ) Constructor.individual))
from term_has_type.Cst proves
show @term_has_type pre_set con_set var_set map maps mapss (Term.app (Term.c con_set.s) (Term.c con_set.z)) (type.constructor Constructor.individual) from term_has_type.App_con ps pz
variable (s : mapss var_set.v = some (type.constructor Constructor.individual))

end simple
