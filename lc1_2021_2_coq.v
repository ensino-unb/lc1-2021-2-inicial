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

  
