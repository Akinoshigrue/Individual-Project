
import Lean

section
universe u
variable (pred_idents : Type u ) (const_idents : Type u)  (var_idents : Type u) [DecidableEq var_idents] [DecidableEq pred_idents] [DecidableEq const_idents]
/-definition of Constructor, Predicate and their argument type-/

mutual
inductive γ  where
 | ι  : γ
 | arrow : κ  ->  γ  ->  γ
deriving Repr, DecidableEq

inductive κ  where
| promote : γ -> κ
deriving Repr, DecidableEq

inductive ρ  where
 | o : ρ
 | arrow : σ  -> ρ  -> ρ
deriving Repr, DecidableEq

inductive σ where
 | c_promote : κ -> σ
 | p_promote : ρ  -> σ
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

def TyEnv  := partial_function var_idents type
def FunEnv := total_function const_idents γ
def PreEnv := total_function pred_idents ρ
def extend_ (pf : partial_function var_idents type) (v : var_idents) (t :type) (v' : var_idents) : Option type :=  if v' = v then some t else pf v'
def extend (pf : partial_function var_idents type) (v : var_idents) (t :type) : partial_function var_idents type
| v' => if v' = v then t else pf v'
/-definition of Terms and type logic-/
def list_extend   : (pf : partial_function var_idents type) -> ( y : List var_idents) -> ( t : List (σ)) -> partial_function var_idents type
| A , a::as , b :: bs => list_extend (extend var_idents A a (type.Predicate_Arg b)) as bs
| A , _ , _ => A

inductive Term where
 | pred   : pred_idents    ->       Term
 | const  : const_idents   ->       Term
 | var    : var_idents     ->       Term
 | app    : Term    ->   Term   ->  Term
deriving Repr

mutual
inductive Goal_formula where
  | Atomic : Term pred_idents const_idents var_idents -> Goal_formula
  | true : Goal_formula
  | GandH : Goal_formula -> Goal_formula -> Goal_formula
  | exist : var_idents -> Goal_formula -> Goal_formula
deriving Repr

inductive Definite_formula where
  | CandD : Definite_formula -> Definite_formula -> Definite_formula
  | true  : Definite_formula
  | nor_any : List (var_idents) -> Goal_formula -> pred_idents -> List (var_idents) -> Definite_formula
  | cst_any : List (var_idents) -> Goal_formula -> pred_idents -> const_idents -> List (var_idents) -> Definite_formula
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

inductive term_has_type {fe : FunEnv const_idents } {pi : PreEnv pred_idents} : TyEnv var_idents -> Term pred_idents const_idents var_idents -> type -> Prop where
| Var {Δ : TyEnv var_idents} {x : var_idents} {τ : type} :
 Δ x = τ -> term_has_type Δ (Term.var x) τ

| App_con {Δ : TyEnv var_idents} {s t : Term pred_idents const_idents var_idents} {left:κ} {right: γ}:
  term_has_type Δ (s) (Constructor (γ.arrow left right))
  -> term_has_type Δ t ( Constructor_Arg  left)
  -> term_has_type  Δ (Term.app s t ) (Constructor right)


| App_pre {Δ : TyEnv var_idents} {s t : Term pred_idents const_idents var_idents} {left: σ} {right: ρ}:
  term_has_type Δ (s) (Predicate (ρ.arrow left right))
  -> term_has_type  Δ t ( Predicate_Arg  left)
  -> term_has_type  Δ (Term.app s t ) (Predicate right)

| Cst  {Δ : TyEnv var_idents}  {c : const_idents} {y : γ} :
  (fe c = y) -> term_has_type  Δ (Term.const c) (type.Constructor y)

| Cst_arg  {Δ : TyEnv var_idents}   {c : Term pred_idents const_idents var_idents} {y : γ}:
  term_has_type  Δ (c) (type.Constructor y)
 -> term_has_type Δ (c) (type.Constructor_Arg (κ.promote y))

|Pred {Δ : TyEnv var_idents} {pred : pred_idents} {p : ρ} :
 (pi pred = p) -> term_has_type Δ (Term.pred pred) (type.Predicate p)

|Pred_arg_c  {Δ : TyEnv var_idents}   {c : Term pred_idents const_idents var_idents} {y : γ}:
  term_has_type Δ (c) (type.Constructor y)
 -> term_has_type Δ (c) (type.Predicate_Arg (σ.c_promote (κ.promote y)))

|Pred_arg_p  {Δ : TyEnv var_idents}   {c : Term pred_idents const_idents var_idents} {p : ρ}:
  term_has_type Δ (c) (type.Predicate p)
 -> term_has_type Δ (c) (type.Predicate_Arg (σ.p_promote p))



inductive wrong_term_has_type  : TyEnv var_idents -> Term pred_idents const_idents var_idents -> type -> Prop where
| App_con {Δ : TyEnv var_idents} {s t : Term pred_idents const_idents var_idents} {left:κ} {right: γ}:
  wrong_term_has_type Δ (s) (Constructor (γ.arrow left right))
  -> wrong_term_has_type Δ t ( Constructor_Arg  left)
  -> wrong_term_has_type Δ (Term.app s t ) (Constructor right)


| App_pre {Δ : TyEnv var_idents} {s t : Term pred_idents const_idents var_idents} {left: σ} {right: ρ}:
  wrong_term_has_type Δ (s) (Predicate (ρ.arrow left right))
  -> wrong_term_has_type Δ t ( Predicate_Arg  left)
  -> wrong_term_has_type Δ (Term.app s t ) (Predicate right)

| Cst  {Δ : TyEnv var_idents}{fe : FunEnv const_idents } {c : const_idents} {y : γ} :
  (fe c = y) -> wrong_term_has_type Δ (Term.const c) (type.Constructor y)

| Cst_arg  {Δ : TyEnv var_idents}   {c : Term pred_idents const_idents var_idents} {y : γ}:
  wrong_term_has_type Δ (c) (type.Constructor y)
 -> wrong_term_has_type Δ (c) (type.Constructor_Arg (κ.promote y))



















inductive Goal_formula_has_type : TyEnv var_idents-> Goal_formula pred_idents const_idents var_idents-> type -> Prop
  | True  {Δ : TyEnv var_idents} :
  Goal_formula_has_type  Δ  (Goal_formula.true) (type.Predicate ρ.o)

  | And  {Δ : TyEnv var_idents} {G H: Goal_formula pred_idents const_idents var_idents} :
  Goal_formula_has_type Δ G (type.Predicate ρ.o)
  -> Goal_formula_has_type Δ H (type.Predicate ρ.o)
  -> Goal_formula_has_type Δ (Goal_formula.GandH G H) (type.Predicate ρ.o)

  | Ex {Δ : TyEnv var_idents} {G : Goal_formula pred_idents const_idents var_idents} {x : var_idents} {sigma : σ}:
  Δ x = Option.none->
  Goal_formula_has_type (extend_ var_idents Δ x (type.Predicate_Arg sigma)) G (type.Predicate ρ.o) ->
  Goal_formula_has_type Δ (Goal_formula.exist x G) (type.Predicate ρ.o)


-- end
def term_single_substitution (T : Term pred_idents const_idents var_idents) (s : Term pred_idents const_idents var_idents) (y : var_idents)  : (Term pred_idents const_idents var_idents) :=
    match T with
    | var n => if n = y then s else T
    | app n_1 n_2 => Term.app (term_single_substitution n_1 s y) (term_single_substitution n_2 s y)
    | _ => T

def substitutions_Term : (T : Term pred_idents const_idents var_idents) -> (s_bar : List (Term pred_idents  const_idents var_idents)) -> (y_bar : List var_idents) -> (Term pred_idents const_idents var_idents)
| T , [] , [] => T
| T, a::as , b::bs => substitutions_Term (term_single_substitution pred_idents const_idents var_idents T a b) as bs
| T , _ , _ => T


def helper : (T : Term pred_idents const_idents var_idents) -> ( V: List var_idents) -> Term pred_idents const_idents var_idents
| T ,  []   => T
| T ,  a::as => helper (Term.app T (Term.var a)) as

def pre_List_app : (Ps : pred_idents) -> (V : List var_idents) -> Term pred_idents const_idents var_idents
| Ps , [] =>  Term.pred Ps
| Ps , a::as => helper pred_idents const_idents var_idents (Term.app (Term.pred Ps) (Term.var a)) as

def cst_List_app : (cst : const_idents) -> (V : List var_idents) -> Term pred_idents const_idents var_idents
| Cst , [] =>  Term.const Cst
| Cst , a::as => helper pred_idents const_idents var_idents (Term.app (Term.const Cst) (Term.var a)) as

def single_goal_sub (G : Goal_formula pred_idents const_idents var_idents) (s : Term pred_idents const_idents var_idents) (y : var_idents)  : (Goal_formula pred_idents const_idents var_idents) :=
    match G with
    | Goal_formula.Atomic t => Goal_formula.Atomic (term_single_substitution pred_idents const_idents var_idents t s y)
    | Goal_formula.true => Goal_formula.true
    | Goal_formula.GandH G H => Goal_formula.GandH (single_goal_sub G s y) (single_goal_sub H s y)
    | Goal_formula.exist x G => Goal_formula.exist x (single_goal_sub G s y)

def substitution : (G : Goal_formula pred_idents const_idents var_idents) -> (s_bar : List (Term pred_idents const_idents var_idents)) -> (y_bar : List var_idents) -> (Goal_formula pred_idents const_idents var_idents)
| G, a::as , b::bs => substitution (single_goal_sub  pred_idents const_idents var_idents G a b) as bs
| G , _ , _  => G

def break_ (D : Definite_formula pred_idents const_idents var_idents) :  Prod (Goal_formula pred_idents const_idents var_idents) (Goal_formula pred_idents const_idents var_idents) :=
    match D with
    | Definite_formula.true => (Goal_formula.true , Goal_formula.true)
    | Definite_formula.nor_any _ G p v => (G , Goal_formula.Atomic (pre_List_app pred_idents const_idents var_idents p v))
    | Definite_formula.cst_any _ G p cst v =>  (G , Goal_formula.Atomic (Term.app (Term.pred p) (cst_List_app pred_idents const_idents var_idents cst v)))
    | Definite_formula.CandD _ _=>  (Goal_formula.true , Goal_formula.true)

  -- | CI {Δ : TyEnv var} { new : TyEnv var} {Ly : List (Term pre const var)} {G : Goal_formula const pre var} {A : Term pre const var} :
  -- term_has_type const pre var Δ Ly
inductive Definite_formula_has_type : TyEnv var_idents-> Definite_formula pred_idents const_idents var_idents-> type -> Prop
|CI_nor  {Δ : TyEnv var_idents} {G : Goal_formula pred_idents const_idents var_idents} {y : List var_idents} {t : List σ} {P : pred_idents} :
Goal_formula_has_type pred_idents const_idents var_idents (list_extend var_idents Δ y t) G (type.Predicate ρ.o) ->
Goal_formula_has_type pred_idents const_idents var_idents (list_extend var_idents Δ y t) (Goal_formula.Atomic (pre_List_app pred_idents const_idents var_idents P y)) (type.Predicate ρ.o) ->
Definite_formula_has_type Δ (Definite_formula.nor_any y G P y) (type.Predicate ρ.o)

| CI_cst  {Δ : TyEnv var_idents} {G: Goal_formula pred_idents const_idents var_idents} {y : List var_idents} {t : List σ} {P : pred_idents} {con : const_idents} :
Goal_formula_has_type pred_idents const_idents var_idents (list_extend var_idents Δ y t) G (type.Predicate ρ.o) ->
Goal_formula_has_type pred_idents const_idents var_idents (list_extend var_idents Δ y t) (Goal_formula.Atomic (Term.app (Term.pred P ) (cst_List_app pred_idents const_idents var_idents con y))) (type.Predicate ρ.o) ->
Definite_formula_has_type Δ (Definite_formula.cst_any y G P con y) (type.Predicate ρ.o)

inductive Prove_Goal_formula: List (Definite_formula pre_idents const_idents var_idents) -> Goal_formula pred_idents const_idents var_idents-> Prop
| T {D :List (Definite_formula pred_idents const_idents var_idents) } :
  Prove_Goal_formula D Goal_formula.true
|And {D :List (Definite_formula pred_idents const_idents var_idents) } {G H :Goal_formula pred_idents const_idents var_idents }:
  Prove_Goal_formula D G
  -> Prove_Goal_formula D H
  -> Prove_Goal_formula D (Goal_formula.GandH G H)

| Ex {D :List (Definite_formula pred_idents const_idents var_idents) } (t : Term pred_idents const_idents var_idents) {x : var_idents} {G : Goal_formula pred_idents const_idents var_idents}:
Prove_Goal_formula D ((single_goal_sub pred_idents const_idents var_idents G t x))
-> Prove_Goal_formula D (Goal_formula.exist x (G))

| Res {D : List (Definite_formula pred_idents const_idents var_idents)}{ y_bar: List (var_idents)} {s_bar: List (Term pred_idents const_idents var_idents)}{ G_ A_: Goal_formula pred_idents const_idents var_idents} {D_ : Definite_formula pred_idents const_idents var_idents}:
substitution pred_idents const_idents var_idents (break_ pred_idents const_idents var_idents D_).fst  s_bar y_bar = G_  ->
substitution pred_idents const_idents var_idents (break_ pred_idents const_idents var_idents D_).snd s_bar y_bar = A_ ->
Prove_Goal_formula D G_->
Prove_Goal_formula D A_

end
/- section end-/


namespace LazyIO

inductive pre_set where
 | V : pre_set
 | Ex : pre_set
 | Open : pre_set
 | Closed : pre_set
 | Pred : pre_set
deriving Repr


inductive con_set where
 | o : con_set
 | c : con_set
 | sqr_bracket : con_set
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
| p : var_set
deriving Repr

deriving instance DecidableEq for pre_set
deriving instance DecidableEq for con_set
deriving instance DecidableEq for var_set
open var_set
open pre_set
open con_set
def D_1 : Definite_formula pre_set con_set var_set :=  Definite_formula.nor_any [p] (Goal_formula.Atomic (Term.app (Term.var p) (Term.const con_set.sqr_bracket))) pre_set.Ex [p]
def D_2 : Definite_formula pre_set con_set var_set :=  Definite_formula.nor_any [y,p] (Goal_formula.exist y (Goal_formula.Atomic (Term.app (Term.var p) (Term.app (Term.app (Term.var y) (Term.const con_set.colon)) (Term.const read))))) pre_set.Ex [y, p]
def D_3 : Definite_formula pre_set con_set var_set :=  Definite_formula.cst_any [x] (Goal_formula.Atomic (Term.app (Term.pred V) (Term.var x))) pre_set.V con_set.id [x]
def D_4 : Definite_formula pre_set con_set var_set :=  Definite_formula.nor_any [h, k, x] (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.var k) (Term.var x)) (Term.var h)))) pre_set.Pred [h, k ,x ]
def D_5 : Definite_formula pre_set con_set var_set :=  Definite_formula.cst_any [h,k] (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.var k) (Term.const o)))) V con_set.open [h,k]
def D_6 : Definite_formula pre_set con_set var_set :=  Definite_formula.cst_any [h,k] (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.var k) (Term.const c)))) V con_set.close [h,k]
def D_7 : Definite_formula pre_set con_set var_set :=  Definite_formula.cst_any [h, k] (Goal_formula.Atomic (Term.app (Term.pred Closed) (Term.var h))) V con_set.read [h, k]
def D_8 : Definite_formula pre_set con_set var_set :=  Definite_formula.cst_any [h, k] (Goal_formula.GandH (Goal_formula.Atomic (Term.app (Term.pred Open) (Term.var h))) (Goal_formula.Atomic (Term.app (Term.pred Ex) (Term.app (Term.app (Term.pred Pred) (Term.var h)) (Term.var k))))) pre_set.V con_set.read [h,k]
def D_9 : Definite_formula pre_set con_set var_set :=  Definite_formula.cst_any [k, y, h] (Goal_formula.Atomic (Term.app (Term.pred V) (Term.var k))) V putCont [k,y,h]
def D_10 : Definite_formula pre_set con_set var_set := Definite_formula.cst_any [x, h, k] (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.var x) (Term.var h)) (Term.app (Term.const putCont) (Term.var k))))) V con_set.putStrLn [x, h, k]
/- D_11 correspondingt the goal-/
def D_11 : Definite_formula pre_set con_set var_set := Definite_formula.cst_any [x , m , f , h , k] (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.const con_set.open) (Term.var h)) (Term.app (Term.app (Term.const con_set.withFile_1) (Term.var f)) (Term.var k))))) V con_set.withFile [x,m,f,h,k]
def D_12 : Definite_formula pre_set con_set var_set := Definite_formula.cst_any [f, k ,h_0] (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.var f) (Term.var h_0)) (Term.app (Term.const con_set.withFile_2) (Term.var k))))) V con_set.withFile_1 [f, k , h_0]
def D_13 : Definite_formula pre_set con_set var_set := Definite_formula.cst_any [k, h_1, y] (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.const con_set.close) (Term.var h_1)) (Term.app (Term.app (Term.const con_set.withFile_3) (Term.var y)) (Term.var k))))) V con_set.withFile_2 [k, h_1, y]
def D_14 : Definite_formula pre_set con_set var_set := Definite_formula.cst_any [y, k ,h_2] (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.var k) (Term.var y)) (Term.var h_2)))) V con_set.withFile_3 [y, k ,h_2]
def D_15 : Definite_formula pre_set con_set var_set := Definite_formula.cst_any  [h, k] (Goal_formula.GandH (Goal_formula.Atomic (Term.app (Term.pred Open) (Term.var h))) (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.var k) (Term.const o)) (Term.const con_set.read))))) V con_set.hGetContent [h,k]
def D_16 : Definite_formula pre_set con_set var_set := Definite_formula.cst_any [x, h_3]  (Goal_formula.Atomic (Term.app (Term.pred V ) (Term.app  (Term.app (Term.app (Term.const con_set.putStrLn) (Term.var var_set.x)) (Term.var var_set.h_3)) (Term.const id)))) V con_set.act_2 [x, h_3]
def D_17 : Definite_formula pre_set con_set var_set := Definite_formula.cst_any [] Goal_formula.true pre_set.Open con_set.o []
def D_18 : Definite_formula pre_set con_set var_set := Definite_formula.cst_any [] Goal_formula.true pre_set.Closed con_set.c []


def D : List (Definite_formula pre_set con_set var_set) := [D_1,D_2,D_3,D_4, D_5, D_6, D_7, D_8, D_9, D_10, D_11,D_12, D_13, D_14,D_15, D_16,D_17, D_18]

theorem base_ : Prove_Goal_formula pre_set con_set var_set D Goal_formula.true :=  Prove_Goal_formula.T

theorem eighteen_ : Prove_Goal_formula pre_set con_set var_set D (Goal_formula.Atomic (Term.app (Term.pred Closed) (Term.const c))) :=
have sub_1: substitution pre_set con_set var_set (break_ pre_set con_set var_set D[17]).fst [] [] = substitution pre_set con_set var_set Goal_formula.true [] []  := by rfl
have sub_2 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[17]).snd [] [] =  (Goal_formula.Atomic (Term.app (Term.pred Closed) (Term.const c))) := by rfl
Prove_Goal_formula.Res sub_1 sub_2 base_

theorem seven_: Prove_Goal_formula pre_set con_set var_set D  (Goal_formula.Atomic (Term.app (Term.pred V ) (Term.app (Term.app (Term.const con_set.read) (Term.const con_set.c)) (Term.app (Term.const con_set.putCont) (Term.const id))))) :=
 have sub_1 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[6]).fst [(Term.const con_set.c), (Term.app (Term.const con_set.putCont) (Term.const id))] [var_set.h, var_set.k] =
substitution pre_set con_set var_set (Goal_formula.Atomic (Term.app (Term.pred Closed) (Term.const c))) [] []  := by rfl
have sub_2 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[6]).snd [(Term.const con_set.c), (Term.app (Term.const con_set.putCont) (Term.const id))] [var_set.h, var_set.k] = (Goal_formula.Atomic (Term.app (Term.pred V ) (Term.app (Term.app (Term.const con_set.read) (Term.const con_set.c)) (Term.app (Term.const con_set.putCont) (Term.const id))))) := by rfl
Prove_Goal_formula.Res sub_1 sub_2 eighteen_

theorem ten_:Prove_Goal_formula pre_set con_set var_set D (Goal_formula.Atomic (Term.app (Term.pred V ) (Term.app (Term.app (Term.app (Term.const con_set.putStrLn) (Term.const con_set.read)) ( Term.const c))  (Term.const id)))) :=
have sub_1: substitution pre_set con_set var_set (break_ pre_set con_set var_set D[9]).fst [Term.const con_set.read, Term.const c, Term.const id] [x, h, k]=
(substitution pre_set con_set var_set (Goal_formula.Atomic (Term.app (Term.pred V ) (Term.app (Term.app (Term.const con_set.read) (Term.var var_set.h)) (Term.var var_set.k))))
[(Term.const con_set.c), (Term.app (Term.const con_set.putCont) (Term.const id))] [var_set.h, var_set.k]) := by rfl
have sub_2 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[9]).snd [Term.const con_set.read, Term.const c, Term.const id] [x, h, k] =
(Goal_formula.Atomic (Term.app (Term.pred V ) (Term.app (Term.app (Term.app (Term.const con_set.putStrLn) (Term.const con_set.read)) ( Term.const c))  (Term.const id)))) := by rfl
Prove_Goal_formula.Res sub_1 sub_2 seven_

theorem sixteen_ : Prove_Goal_formula pre_set con_set var_set D (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.const act_2) (Term.const con_set.read)) (Term.const c))))  :=
have sub_1 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[15]).fst [Term.const con_set.read, Term.const con_set.c] [x, h_3] =
(substitution pre_set con_set var_set (Goal_formula.Atomic (Term.app (Term.pred V ) (Term.app (Term.app (Term.app (Term.const con_set.putStrLn) (Term.var var_set.x)) (Term.var var_set.h))  (Term.var k)))) [Term.const con_set.read , Term.const c , Term.const id] [x, h, k])  := by rfl
have sub_2 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[15]).snd [Term.const con_set.read, Term.const con_set.c] [x, h_3] =
(Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.const act_2) (Term.const con_set.read)) (Term.const con_set.c)))) := by rfl
Prove_Goal_formula.Res sub_1 sub_2 ten_


theorem fourteen_ : Prove_Goal_formula pre_set con_set var_set D (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.app (Term.const con_set.withFile_3) (Term.const con_set.read)) (Term.const act_2)) (Term.const c))))  :=
have sub_1:  substitution pre_set con_set var_set (break_ pre_set con_set var_set D[13]).fst [Term.const act_2, Term.const con_set.read, Term.const c] [k, y, h_2] =  (substitution pre_set con_set var_set (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.const act_2) (Term.var x)) (Term.var h_3)))) [Term.const con_set.read, Term.const c] [x, h_3]) := by rfl
have sub_2 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[13]).snd [Term.const act_2, Term.const con_set.read, Term.const c] [k, y, h_2] =
(Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.app (Term.const con_set.withFile_3) (Term.const con_set.read)) (Term.const act_2)) (Term.const c)))) := by rfl
Prove_Goal_formula.Res sub_1 sub_2 sixteen_


theorem six_ : Prove_Goal_formula pre_set con_set var_set D  (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.const con_set.close) (Term.const o)) ( Term.app (Term.app (Term.const con_set.withFile_3) (Term.const con_set.read)) (Term.const con_set.act_2))))) :=
 have sub_1 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[5]).fst [Term.const o, Term.app (Term.app (Term.const con_set.withFile_3) (Term.const con_set.read)) (Term.const con_set.act_2)] [h, k] =
 (substitution pre_set con_set var_set (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.app (Term.const con_set.withFile_3) (Term.var y)) (Term.var k)) (Term.var h_2)))) [Term.const act_2, Term.const con_set.read, Term.const c] [k, y, h_2] ) := by rfl
have sub_2 :  substitution pre_set con_set var_set (break_ pre_set con_set var_set D[5]).snd [Term.const o, Term.app (Term.app (Term.const con_set.withFile_3) (Term.const con_set.read)) (Term.const con_set.act_2)] [h, k] =
 (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.const con_set.close) (Term.const o)) ( Term.app (Term.app (Term.const con_set.withFile_3) (Term.const con_set.read)) (Term.const con_set.act_2))))) := by rfl
 Prove_Goal_formula.Res sub_1 sub_2 fourteen_


theorem thirteen_ : Prove_Goal_formula pre_set con_set var_set D (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app ((Term.app ((Term.app (Term.const con_set.withFile_2) (Term.const act_2))) (Term.const o))) (Term.const con_set.read))))  :=
have sub_1 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[12]).fst [Term.const act_2, Term.const o, Term.const con_set.read] [k, h_1, y] = (substitution pre_set con_set var_set (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.const con_set.close) (Term.var h)) (Term.var k))))
 [Term.const o, Term.app (Term.app (Term.const con_set.withFile_3) (Term.const con_set.read)) (Term.const con_set.act_2)] [h, k]) := by rfl
have sub_2 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[12]).snd  [Term.const act_2, Term.const o, Term.const con_set.read] [k, h_1 ,y] = (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app ((Term.app ((Term.app (Term.const con_set.withFile_2) (Term.const act_2))) (Term.const o))) (Term.const con_set.read)))) := by rfl
Prove_Goal_formula.Res sub_1 sub_2 six_

theorem seventeen_ : Prove_Goal_formula pre_set con_set var_set D (Goal_formula.Atomic (Term.app (Term.pred Open) (Term.const o))) :=
have sub_1: substitution pre_set con_set var_set (break_ pre_set con_set var_set D[16]).fst [] [] = substitution pre_set con_set var_set Goal_formula.true [] []  := by rfl
have sub_2 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[16]).snd [] [] =  (Goal_formula.Atomic (Term.app (Term.pred Open) (Term.const o))) := by rfl
Prove_Goal_formula.Res sub_1 sub_2 base_

theorem combine_ :Prove_Goal_formula pre_set con_set var_set D (Goal_formula.GandH (Goal_formula.Atomic (Term.app (Term.pred Open) (Term.const o))) (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app ((Term.app ((Term.app (Term.const con_set.withFile_2) (Term.const act_2))) (Term.const o))) (Term.const con_set.read))))) :=
Prove_Goal_formula.And seventeen_ thirteen_

theorem fifteen_ : Prove_Goal_formula pre_set con_set var_set D (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.const con_set.hGetContent) ( Term.const o)) (Term.app (Term.const con_set.withFile_2) (Term.const act_2))))) :=
have sub_1 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[14]).fst [Term.const o, Term.app (Term.const con_set.withFile_2) (Term.const act_2)] [h , k] =
(@Goal_formula.GandH pre_set con_set var_set (Goal_formula.Atomic (Term.app (Term.pred Open) (Term.const o))) (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app ((Term.app ((Term.app (Term.const con_set.withFile_2) (Term.const act_2))) (Term.const o))) (Term.const con_set.read))))) := by rfl
have sub_2 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[14]).snd [Term.const o, Term.app (Term.const con_set.withFile_2) (Term.const act_2)] [h , k] =
 (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.const con_set.hGetContent) ( Term.const o)) (Term.app (Term.const con_set.withFile_2) (Term.const act_2))))) := by rfl
 Prove_Goal_formula.Res sub_1 sub_2 combine_

theorem twelve_ : Prove_Goal_formula pre_set con_set var_set D (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.app (Term.const con_set.withFile_1) ( Term.const con_set.hGetContent)) (Term.const act_2)) (Term.const o)))) :=
have sub_1 :  substitution pre_set con_set var_set (break_ pre_set con_set var_set D[11]).fst [Term.const con_set.hGetContent, Term.const act_2, Term.const o] [f, k, h_0] =
(Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.const con_set.hGetContent) ( Term.const o)) (Term.app (Term.const con_set.withFile_2) (Term.const act_2))))) := by rfl
have sub_2 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[11]).snd [Term.const con_set.hGetContent, Term.const act_2, Term.const o] [f, k, h_0] =
(Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.app (Term.const con_set.withFile_1) ( Term.const con_set.hGetContent)) (Term.const act_2)) (Term.const o)))) := by rfl
Prove_Goal_formula.Res sub_1 sub_2 fifteen_

theorem five_ : Prove_Goal_formula pre_set con_set var_set D (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.const con_set.open) ( Term.const c )) (Term.app (Term.app (Term.const con_set.withFile_1) (Term.const con_set.hGetContent)) (Term.const act_2))))) :=
have sub_1 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[4]).fst [Term.const c, Term.app (Term.app (Term.const con_set.withFile_1) (Term.const con_set.hGetContent)) (Term.const act_2)] [h, k] =
(Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.app (Term.const con_set.withFile_1) ( Term.const con_set.hGetContent)) (Term.const act_2)) (Term.const o)))) := by rfl
have sub_2 : substitution pre_set con_set var_set (break_ pre_set con_set var_set D[4]).snd [Term.const c, Term.app (Term.app (Term.const con_set.withFile_1) (Term.const con_set.hGetContent)) (Term.const act_2)] [h, k] =
(Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.const con_set.open) ( Term.const c )) (Term.app (Term.app (Term.const con_set.withFile_1) (Term.const con_set.hGetContent)) (Term.const act_2))))) := by rfl
Prove_Goal_formula.Res sub_1 sub_2 twelve_

theorem eleven_ : Prove_Goal_formula pre_set con_set var_set D (Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.app (Term.app (Term.app (Term.const con_set.withFile) (Term.const con_set.test_txt)) (Term.const con_set.ReadMode)) (Term.const con_set.hGetContent)) (Term.const c)) (Term.const act_2)))) :=
have sub_1: substitution pre_set con_set var_set (break_ pre_set con_set var_set D[10]).fst [ Term.const con_set.test_txt, Term.const con_set.ReadMode, Term.const con_set.hGetContent, Term.const c, Term.const act_2] [x, m, f, h, k] =
(Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.const con_set.open) ( Term.const c )) (Term.app (Term.app (Term.const con_set.withFile_1) (Term.const con_set.hGetContent)) (Term.const act_2))))) := by rfl
have sub_2: substitution pre_set con_set var_set (break_ pre_set con_set var_set D[10]).snd [ Term.const con_set.test_txt, Term.const con_set.ReadMode, Term.const con_set.hGetContent, Term.const c, Term.const act_2] [x, m, f, h, k] =
(Goal_formula.Atomic (Term.app (Term.pred V) (Term.app (Term.app (Term.app (Term.app (Term.app (Term.const con_set.withFile) (Term.const con_set.test_txt)) (Term.const con_set.ReadMode)) (Term.const con_set.hGetContent)) (Term.const c)) (Term.const act_2)))) := by rfl
Prove_Goal_formula.Res sub_1 sub_2 five_

end LazyIO


namespace simple
 /-con set and pre set-/  /-con set and pre set-/  /-con set and pre set-/  /-con set and pre set-/  /-con set and pre set-/
inductive con_set where
 | Z : con_set
 | S : con_set

inductive pre_set where
 | Leq : pre_set

inductive var_set where
|  v : var_set

 /-con set and pre set-/  /-con set and pre set-/  /-con set and pre set-/  /-con set and pre set-/  /-con set and pre set-/

def Sigma (x :con_set):=
  match x with
    | con_set.Z => γ.ι
    | con_set.S => γ.arrow  (κ.promote γ.ι ) γ.ι

-- def incorrect_Sigma (x :con_set):=
--   match x with
--     | con_set.Z => γ.ι
--     | con_set.S => γ.ι

def Pi (x : pre_set):=
  match x with
   | pre_set.Leq => ρ.arrow (σ.c_promote (κ.promote γ.ι)) (ρ.arrow (σ.c_promote (κ.promote γ.ι)) ρ.o)

def Δ (x : var_set)  :=
  match x with
    | var_set.v => some (type.Constructor γ.ι)

deriving instance DecidableEq for pre_set
deriving instance DecidableEq for con_set
deriving instance DecidableEq for var_set
open var_set
open pre_set
open con_set


#check @term_has_type pre_set con_set var_set Sigma Pi Δ
(Term.app (Term.app (Term.pred pre_set.Leq) (Term.app (Term.const con_set.S) (Term.const con_set.Z))) (Term.const con_set.Z)) (type.Predicate ρ.o)


theorem Z_ : @term_has_type pre_set con_set var_set Sigma Pi Δ (Term.const Z) (type.Constructor γ.ι) :=
have sub : Sigma Z = γ.ι := by rfl
@term_has_type.Cst pre_set con_set var_set Sigma Pi Δ Z γ.ι sub

theorem Z_con_arg : @term_has_type pre_set con_set var_set Sigma Pi Δ (Term.const Z) (type.Constructor_Arg (κ.promote γ.ι)) := term_has_type.Cst_arg Z_
theorem Z__pred : @term_has_type pre_set con_set var_set Sigma Pi Δ (Term.const Z) (type.Predicate_Arg (σ.c_promote (κ.promote γ.ι))) := term_has_type.Pred_arg_c Z_
theorem S_ : @term_has_type pre_set con_set var_set Sigma Pi Δ (Term.const S) (type.Constructor  (γ.arrow  (κ.promote γ.ι ) γ.ι)) :=
have sub : Sigma S = γ.arrow  (κ.promote γ.ι ) γ.ι := by rfl
term_has_type.Cst sub

theorem SZ_ : @term_has_type pre_set con_set var_set Sigma Pi Δ (Term.app (Term.const S) (Term.const Z)) (type.Constructor γ.ι) :=
term_has_type.App_con S_ Z_con_arg

theorem SZ__pred : @term_has_type pre_set con_set var_set Sigma Pi Δ (Term.app (Term.const S) (Term.const Z)) (type.Predicate_Arg (σ.c_promote (κ.promote γ.ι)))
:= term_has_type.Pred_arg_c SZ_

theorem leq :@term_has_type pre_set con_set var_set Sigma Pi Δ  (Term.pred Leq) (type.Predicate (ρ.arrow (σ.c_promote (κ.promote γ.ι)) (ρ.arrow (σ.c_promote (κ.promote γ.ι)) ρ.o))) :=
have sub : Pi Leq = ρ.arrow (σ.c_promote (κ.promote  γ.ι)) (ρ.arrow (σ.c_promote (κ.promote γ.ι)) ρ.o) := by rfl
term_has_type.Pred sub

theorem Leq_SZ : @term_has_type pre_set con_set var_set Sigma Pi Δ  (Term.app (Term.pred Leq) (Term.app (Term.const S) (Term.const Z)))
 (type.Predicate (ρ.arrow (σ.c_promote (κ.promote γ.ι)) (ρ.o))) := term_has_type.App_pre leq SZ__pred
theorem Leq_SZ_Z : @term_has_type pre_set con_set var_set Sigma Pi Δ (Term.app (Term.app (Term.pred Leq) (Term.app (Term.const S) (Term.const Z))) (Term.const Z))
(type.Predicate ρ.o) := term_has_type.App_pre Leq_SZ Z__pred


def Leq_SZ_Z_ : Goal_formula pre_set con_set var_set := Goal_formula.Atomic
(Term.app (Term.app (Term.pred pre_set.Leq) (Term.app (Term.const con_set.S) (Term.const con_set.Z))) (Term.const con_set.Z))

-- theorem Z__ : @term_has_type pre_set con_set var_set incorrect_Sigma Pi Δ (Term.const con_set.Z) (type.Constructor γ.ι) :=
-- have sub : Sigma con_set.Z = γ.ι := by rfl
-- term_has_type.Cst  sub

-- -- theorem Z_con_arg : @term_has_type pre_set con_set var_set incorrect_Sigma Pi Δ (Term.const Z) (type.Constructor_Arg (κ.promote γ.ι)) :=
-- -- term_has_type.Cst_arg Z_

-- theorem S___ : @term_has_type pre_set con_set var_set incorrect_Sigma Pi Δ (Term.const S) (type.Constructor  (γ.arrow  (κ.promote γ.ι ) γ.ι)) :=
-- have sub : Sigma S = γ.arrow  (κ.promote γ.ι ) γ.ι := by rfl
-- term_has_type.Cst sub

-- theorem incorrect_SZ : @term_has_type pre_set con_set var_set incorrect_Sigma Pi Δ (Term.app (Term.const S) (Term.const Z)) (type.Constructor γ.ι) :=
-- term_has_type.App_con S_ Z_con_arg



-- theorem incorrect_Z : wrong_term_has_type pre_set con_set var_set Δ (Term.const Z) (type.Constructor γ.ι) :=
-- have sub : incorrect_Sigma Z = γ.ι := by rfl
-- wrong_term_has_type.Cst  sub

-- theorem incorrect_Z_con_arg : wrong_term_has_type pre_set con_set var_set Δ (Term.const Z) (type.Constructor_Arg (κ.promote γ.ι)) :=
-- wrong_term_has_type.Cst_arg incorrect_Z

-- theorem incorrect_S : wrong_term_has_type pre_set con_set var_set Δ (Term.const S) (type.Constructor  (γ.arrow  (κ.promote γ.ι ) γ.ι)) :=
-- have sub : Sigma S = γ.arrow  (κ.promote γ.ι ) γ.ι := by rfl
-- wrong_term_has_type.Cst sub

-- theorem incorrect_SZ : wrong_term_has_type pre_set con_set var_set Δ (Term.app (Term.const S) (Term.const Z)) (type.Constructor γ.ι) :=
-- wrong_term_has_type.App_con incorrect_S incorrect_Z_con_arg


end simple


-- theorem incorrect_SZ_ : wrong_term_has_type  Sigma Pi Δ (Term.app (Term.const S) (Term.const Z)) (type.Constructor γ.ι) :=
-- have Z_ : wrong_term_has_type
