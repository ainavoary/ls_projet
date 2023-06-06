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

(*
exemple : 1 * (2 + 3) * 4 
*)
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

Notation "pexpr :l: l" := (ajt pexpr l) (right associativity, at level 60).




(*4.2*)

(*?????????????????????*)

(*4.3*)

(* 
1 2 3 * +
*)

Example postfix_expr1 := (post_Cst 1) :l: (post_Cst 2) :l: (post_Cst 3) :l: post_Mult :l: post_Plus :l: lvide.

(* 
1 2 3 + * 4 *
*)

Example postfix_expr2 := (post_Cst 1) :l: (post_Cst 2) :l: (post_Cst 3) :l: post_Plus :l: 
                         post_Mult :l: (post_Cst 4) :l: post_Mult :l: lvide.

(*Question 5*)

(*5.1*)

Fixpoint append (l1 l2 : liste) : liste :=
  match l1 with
  |lvide => l2
  |ajt elt_2 l_2 => ajt elt_2 (append l_2 l2)
  end.

Notation "l1 @ l2" := (append l1 l2) (right associativity, at level 60).

Compute postfix_expr1 @ postfix_expr2.

(*5.2*)

Lemma associativity : lvide @ (postfix_expr1 @ postfix_expr2) = (lvide @ postfix_expr1) @ postfix_expr2.

Proof.
  simpl.
  reflexivity.
Qed.

(*Question 6*)

Fixpoint translate (e : expr) : liste :=
  match e with
  |Cst n => (post_Cst n) :l: lvide
  |Mult e1 e2 => (translate e1) @ (translate e2) @ post_Mult :l: lvide
  |Plus e1 e2 => (translate e1) @ (translate e2) @ post_Plus :l: lvide
  end.

Example test : translate expr1 = postfix_expr1.
Proof.
  simpl.
  reflexivity.
Qed.

(*Question 7*)

(*7.1*)
Inductive well_formed : liste -> Prop :=
| w_cst : forall n, well_formed(n :l: lvide)
| w_plus : forall l1 l2, well_formed l1 -> well_formed l2 -> well_formed ( l1 @ l2 @ post_Mult :l: lvide)
| w_fois : forall l1 l2, well_formed l1 -> well_formed l2 -> well_formed ( l1 @ l2 @ post_Plus :l: lvide). 

Compute well_formed postfix_expr1.

(*7.2*)

Lemma wf_ok : forall e : expr, well_formed (translate e).
Proof.
  intros e.
  induction e.
  - simpl. constructor.
  - simpl. constructor; assumption.
  - simpl. constructor; assumption.
Qed.

(*Question 8*)

(*8.1*)

Inductive pile : Type := 
  | pvide : pile
  | empiler : pile -> nat -> pile.

(*8.2*)

Definition sommet (p : pile) : nat := 
  match p with
  |pvide => (0-1)
  |empiler _ n => n
  end.

Definition depiler (p : pile) : pile := 
  match p with
  |pvide => pvide
  |empiler p n => p
  end.

Definition show (p : pile) : pile := 
  p.

Notation "p :p: elt" := (empiler p elt) (left associativity, at level 40).


Example test_pile := pvide :p: 1 :p: 2 :p: 3.

Compute show test_pile.
Compute sommet test_pile.
Compute depiler test_pile.
Compute depiler (depiler test_pile).
Compute depiler (depiler (depiler test_pile)).

(*Question 9*)

(*9.1*)

Fixpoint eval_postfixe (pf_liste : liste) (p : pile) : pile := 
  match pf_liste with
  |lvide => p
  |ajt exp l => match exp with
                 |post_Cst n => eval_postfixe l (p :p: n)
                 |post_Mult => eval_postfixe l (depiler (depiler p) :p: ((sommet p) * (sommet (depiler p))))
                 |post_Plus => eval_postfixe l (depiler (depiler p) :p: ((sommet p) + (sommet (depiler p))))
                end
  end.

(*9.2*)

Compute sommet (eval_postfixe postfix_expr1 pvide). (*7*)
Compute sommet (eval_postfixe postfix_expr2 pvide). (*20*)

Compute sommet (eval_postfixe (postfix_expr2 @ postfix_expr1 @ post_Plus :l: lvide)  pvide). (*27*)
Compute sommet (eval_postfixe (postfix_expr2 @ postfix_expr1 @ post_Mult :l: lvide)  pvide). (*140*)

(*Question 10*)

(*10.1*)

Lemma append_eval : forall ( e f: liste), forall ( p: pile),
eval_postfixe (append e f) p = eval_postfixe f (eval_postfixe e p).



