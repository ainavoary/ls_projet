

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

Compute eval_expr expr1. (*7*)
Compute eval_expr expr2. (*20*)

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

Theorem append_l_lvide_equals_l: forall(e:liste),append e lvide = e.
Proof.
  intro e.
  induction e as [| e' e'' IHe'].
  +simpl. reflexivity.
  +simpl. rewrite IHe'. reflexivity.
Qed.


(*5.2*)

Lemma associativity : lvide @ (postfix_expr1 @ postfix_expr2) = (lvide @ postfix_expr1) @ postfix_expr2.

Proof.
  simpl.
  reflexivity.
Qed.

(*Question 6*)
  
Fixpoint translate (e : expr) : liste :=
  match e with
  |Mult e1 e2 => (translate e1) @ (translate e2) @ post_Mult :l: lvide
  |Plus e1 e2 => (translate e1) @ (translate e2) @ post_Plus :l: lvide
  |Cst n => (post_Cst n) :l: lvide
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

(*7.2*)

Lemma wf_ok : forall e : expr, well_formed (translate e).
Proof.
  intros e.
  induction e.
  - simpl. constructor.
  - simpl. constructor. assumption. assumption.
  - simpl. constructor. assumption. assumption.
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

Proof.
Admitted.
(*

Trace

Proof.
  intros e f p.
  induction e as [|e_elt e_li IHe'].
  +simpl. reflexivity.
  +destruct e_elt as [n| |].
    -assert(H: forall(n : nat), forall(li : well_formed e_li), eval_postfixe e_li p = p :p: n).
      *intros n0 wf. destruct wf.
        ++simpl. destruct n1.
          --reflexivity.


    - assert(H: forall(n : nat), w_cst n -> eval_postfixe e_li p = p :p: n)
      *intro n. intro wf. destruct wf as [n0| |].
        ++rewrite (n0 :l: lvide) .
    -induction f as [|f_elt f_li IHf']. 
      *simpl. rewrite append_l_lvide_equals_l. reflexivity.
      *intro IHf'.



    -simpl.
     destruct (p :p: n).
        *destruct l as [m|].
            ++rewrite append_l_lvide_equals_l.
    -simpl. 
    -simpl. induction f as [| f' f'' IHf'].
      *simpl. rewrite append_l_lvide_equals_l. reflexivity.
      *destruct f' as [m | |].
          ++apply IHe'.


  intros e f p.
  induction e.
  +simpl. reflexivity.
  +assert (H: eval_postfixe e p = (p :p: p0)).
  +induction p as [|p' p'' IHp'].
    -simpl; reflexivity.
    -rewrite <- IHe'.
     simpl.
  induction e as [|e' e'' IHe'].
  +simpl. reflexivity.
  +assert (H: eval_postfixe (e' :l: e'') p = p).
    -rewrite <- IHe'.
  +simpl. reflexivity.
  +simpl. reflexivity.
  induction e.
  +simpl. reflexivity.
  +simpl. 
  +simpl.


    -reflexivity.
  assert (H: eval_postfixe lvide p = p).
  +simpl. reflexivity.
  +rewrite -> H. simpl. reflexivity.
  +assert (H0: eval_postfixe (e @ f) p = eval_postfixe ((p0 :l: e) @ f) p).
    -rewrite -> IHe. rewrite <- IHe. destruct e.
      *rewrite -> IHe. rewrite <- IHe. simpl.

 intros e f p.
  induction e as [| exp l IHl].
  - (* Cas de base : e = lvide *)
    simpl.
    (* Utilise la réflexivité de l'égalité pour conclure *)
    reflexivity.
  - (* Cas de l'induction : e = ajt exp l *)
    simpl.
    destruct exp as [n | | ].
    +
      simpl. (*rewrite Ihl.*)
*)

(*10.2*)

Lemma depiler_eval : forall (f: liste),
    well_formed f -> forall (p : pile), p = depiler(eval_postfixe f p).
Proof.
Admitted.

(*
Trace
(* 10.2 *)

  intros f p.
  induction p as [| exp | IHl].
  -
    intro p. simpl.
    destruct p as [n0 | ].
    simpl.
    +
      destruct n as [ | |].
      simpl. reflexivity.
      simpl. reflexivity.
      simpl. reflexivity.
    +
      destruct n as [n | |].
      simpl. reflexivity.
      simpl.
*)


