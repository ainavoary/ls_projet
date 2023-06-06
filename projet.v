Require Export Nat.
Require Export Ltac.

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

Inductive postfix_expr : Type := 
  |post_Cst : nat -> postfix_expr
  |post_Mult : postfix_expr
  |post_Plus : postfix_expr.


Inductive liste : Type := 
  | lvide : liste
  | ajt : postfix_expr -> liste -> liste.


(*4.2*)

(*?????????????????????*)

(*4.3*)

(* 
1 2 + 3 * 
*)
Example postfix_expr1 := ajt (post_Cst 1) 
                                (ajt (post_Cst 2) 
                                     (ajt post_Plus 
                                          (ajt (post_Cst 3) 
                                               (ajt post_Mult lvide)
                                          )
                                     )
                                ).

(* 
1 2 3 + * 4 *
*)
Example postfix_expr2 := ajt (post_Cst 1) 
                                (ajt (post_Cst 2)
                                     (ajt (post_Cst 3) 
                                          (ajt post_Plus 
                                               (ajt post_Mult 
                                                    (ajt (post_Cst 4)
                                                         (ajt post_Mult lvide)
                                                    )
                                                )
                                          )
                                     )
                                ).

(*Question 5*)

(*5.1*)

Fixpoint append (l1 l2 : liste) : liste :=
  match l1 with
  |lvide => l2
  |ajt elt l => ajt elt (append l l2)
  end.

Notation "l1 @ l2" := (append l1 l2) (right associativity, at level 60).

Example associativity : lvide @ ( postfix_expr1 @ postfix_expr2) = (lvide @ postfix_expr1) @ postfix_expr2.
Abort.
Theorem associativity : forall l:liste,
lvide @ ( postfix_expr1 @ postfix_expr2) = (lvide @ postfix_expr1) @ postfix_expr2.

About intro.

Proof
  intro.

