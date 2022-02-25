(** * Lógica Computacional 1 *)

(**
  Neste documento vamos apresentar o desenvolvimento dos estudos de lógica computacional. Completar ...
 *)

(** ** Lógica Proposicional Minimal *)

(** A regra de introdução da conjunção - landi *)

Parameter phi1 phi2: Prop.

Section regra1.
Hypothesis H1: phi1.
Hypothesis H2: phi2.

Lemma landi: phi1 /\ phi2.
Proof.
  split.
  - assumption.
  - assumption.
Qed.
End regra1.

Section regra2.

Hypothesis H: phi1 /\ phi2.

Lemma lande: phi1.
Proof.
  destruct H.
  assumption.
Qed.
End regra2.

Section regra2'.

Hypothesis H: phi1 /\ phi2.

Lemma
  lande': phi2.
Proof.
  destruct H.
  assumption.
Qed.
End regra2'.

Section exercicio1.

Hypothesis H: phi1 /\ phi2.

Lemma and_comm: phi2 /\ phi1.
Proof.
 split.
 - destruct H.
   assumption.
 - destruct H.
   assumption.
Qed.
End exercicio1.

Section regra3.

Hypothesis H: phi1.

Lemma ori: phi1 \/ phi2.
Proof.
  left.
  assumption.
Qed.
  
End regra3.

Section regra3'.

Hypothesis H: phi2.

Lemma or_i: phi1 \/ phi2.
Proof.
  right.
  assumption.
Qed.
End regra3'.

Section regra4.
 Variable gamma: Prop.
  
  Hypothesis H: phi1 \/ phi2.
  Hypothesis H1: phi1 -> gamma.
  Hypothesis H2: phi2 -> gamma.
  
Lemma or_e: gamma.
Proof.
  destruct H.
  - apply H1.
     assumption.
  - cut (phi2).
    + assumption.
    + assumption.
Qed.    
End regra4.

Section regra5.

  Hypothesis H: phi1 -> phi2.

  Lemma imp_i: phi1 -> phi2.
  Proof.
    assumption.
  Qed.
End regra5.

Section regra6.

  Hypothesis H1: phi1 -> phi2.
  Hypothesis H2: phi1.

  Lemma imp_e: phi2.
  Proof.
    apply H1.
    assumption.
  Qed.
End regra6.

Section regra7.

  Hypothesis H1: phi1 -> False.

  Lemma neg_i: ~ phi1.
  Proof.
    intro H.
    apply H1.
    assumption.
  Qed.
End regra7.

Section regra8.

  Hypothesis H1: ~phi1.
  Hypothesis H2: phi1.

  Lemma neg_e: False.
  Proof.
    contradiction.
  Qed.
End regra8.

Section ex23.

  Hypothesis H: (~~ phi1) -> (~~phi2).
  Lemma dup_imp: ~~(phi1 -> phi2).
  Proof.
    intro H'.
    cut (~phi2).
    - apply H.
      intro H''.
      cut (phi1 -> phi2).
      + assumption.
      + intro H'''.
        apply False_ind.
        contradiction.
    - intro H''.
      cut (phi1->phi2).
      + assumption.
      + intro H'''.
        assumption.
  Qed.
End ex23.

Section aula06.

  Variable a: Prop.
  Axiom LP: (((a \/ ~a) -> ~a) -> (a \/ ~a)) -> (a \/ ~a).

  Lemma LEM: a \/ ~a.
  Proof.
    cut (((a \/ ~a) -> ~a) -> (a \/ ~a)).
    - apply LP.
    - intro H.
      right.
      intro H'.
      cut a.
      + cut (a \/ ~a).
        * assumption.
        * left.
          assumption.
      + assumption.
  Qed.

(** Aula 11 *)       

       Print list.
Print list_ind.

Require Import List.

Fixpoint size (l: list nat) :=
  match l with
  | nil => 0
  | h::tl => 1 + (size tl)
  end.

Fixpoint app (l1 l2: list nat) :=
  match l1 with
  | nil => l2
  | h::l1' => h::(app l1' l2)
  end.

Lemma ex51: forall l1 l2, size(app l1 l2) = size l1 + size l2.
Proof.
  induction l1.
  - intros l2.
    reflexivity.
  - intro l2.
    simpl.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma ex52: forall l, app l nil = l.
Proof.
  induction l.
  - reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed. 

Lemma ex53: forall l1 l2 l3, app (app l1 l2) l3 = app l1 (app l2 l3).
Proof.
  induction l1.
  - intros l2 l3.
    reflexivity.
  - intros l2 l3.
    simpl.
    rewrite IHl1.
    reflexivity.
Qed.

(** Aula 12 *)

Fixpoint rev (l : list nat) :=
  match l with
  | nil => l
  | h::tl => (rev tl) ++ (h::nil)
  end.

Print "_ ++ _". (* app em notação infixa. *)
Require Import Lia.

Lemma ex54: forall l, size(rev l) = size l.
Proof.
  induction l.
  - reflexivity.
  - simpl.
    rewrite ex51.
    rewrite IHl.
    simpl.
    lia.
Qed.
