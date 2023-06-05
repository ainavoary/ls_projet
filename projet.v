Require Export Nat.

(*Question 1*)
(*
Exemple d'expression : 

infixe : 1 + 2 * 3    (A)
postfixe : 1 2 + 3 *  (B)

Afin de prouver la correction de la traduction il 
faut que l'évaluation de l'expression (A) soit identique 
à l'évaluation de l'expression (B)


*)

(*Question 2*)

(*2.1*)

Inductive expr : Type :=
  | Cst : nat -> expr
  | Mult : expr -> expr -> expr
  | Plus : expr -> expr -> expr.

(*2.2*)

(*Exemple donné à la question 1*)
Example expr1 : expr := Plus (Cst 1) (Mult (Cst 2) (Cst 3)).

(*exemple : 1 * (2 + 3) * 4 *)
Example expr2 : expr := Mult (Cst 1) (Mult (Plus (Cst 2) (Cst 3)) (Cst 4)).


(*Question 3*)

Fixpoint eval_expr (exp : expr) : nat :=
  match exp with
  |Cst n => n
  |Mult e1 e2 => (eval_expr e1) * (eval_expr e2)
  |Plus e1 e2 => (eval_expr e1) + (eval_expr e2)
  end.

(*Utilisation de eval_expr*)

Eval compute in eval_expr expr1. (*7*)
Eval compute in eval_expr expr2. (*20*)

(*Question 4*)

(*4.1*)

Inductive liste (T : Type) : Type := 
  | lvide : liste T
  | ajt : T -> liste T -> liste T.

Inductive postfix_expr : Type := 
  |post_Cst : nat -> postfix_expr
  |post_Mult : postfix_expr
  |post_Plus : postfix_expr.

(*4.2*)

Definition postfix_expr_liste := liste postfix_expr.  

(*4.3*)

Example postfix_expr1 : postfix_expr_liste := ajt (post_Cst 1) (ajt (post_Cst 2) (ajt post_Plus (ajt (post_Cst 3) (ajt post_Mult lvide)))).
Example postfix_expr2 : postfix_expr_liste := .




