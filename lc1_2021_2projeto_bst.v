(** * Formalização da estrutura de árvores binárias de busca%\footnote{Este documento foi adaptado de \url{https://softwarefoundations.cis.upenn.edu/}}% *)

From Coq Require Import String.
From Coq Require Export Arith.
From Coq Require Export Lia.

(*
Notation  "a >=? b" := (Nat.leb b a) (at level 70) : nat_scope.
Notation  "a >? b"  := (Nat.ltb b a) (at level 70) : nat_scope.
*)

(** Utilizaremos números naturais para representar as chaves em cada nó de nossas árvores binárias de busca porque os naturais possuem uma ordem total [<=?] com diversos teoremas já provados. *)

Definition key := nat.

(** Adicionalmente, os nós armazenarão pares chave/valor, onde o valor associado a uma chave terá um tipo [V] qualquer. Definiremos indutivamente a estrutura [tree] para representar árvores binárias cujos nós contêm uma chave [k] e um valor [v]. As árvores possuem dois construtores, [E] que representa a árvore vazia, e [T] que recebe os seguintes argumentos: 

- [l]: a subárvore à esquerda do nó atual;
- [k]: a chave ligada ao nó atual;
- [v]: o valor associado à chave [k], e;
- [r]: a subárvore à direita do nó atual.

Nesta construção, cada chave se liga a apenas um valor. *)

Inductive tree (V : Type) : Type :=
| E
| T (l : tree V) (k : key) (v : V) (r : tree V).

Arguments E {V}.
Arguments T {V}.

(** Exemplo: a árvore binária contendo valores do tipo [string]
<<
      4 -> "four"
      /        \
     /          \
  2 -> "two"   5 -> "five"
>>

é representada a seguir: *)

Definition ex_tree : tree string :=
  (T (T E 2 "two" E) 4 "four" (T E 5 "five" E))%string.

(** A árvore vazia [empty_tree] não contém chaves: *)

Definition empty_tree {V : Type} : tree V := E. 

(** Uma árvore binária de busca  é caracterizada pela seguinte invariante: dado qualquer nó não-vazio com chave [k], todas as chaves da subárvore à esquerda são menores do que [k], e todas as chaves da subárvore à direita são maiores do que [k]. *)

(** A primeira operação importante relacionada às árvores binárias de busca é  certamente a busca que pode ser implementada de forma muito eficiente. Por exemplo, a função [bound k t] retorna [true] quando [k] é uma chave de [t], e [false] caso contrário. *)

Fixpoint bound {V : Type} (x : key) (t : tree V) :=
  match t with
  | E => false
  | T l y v r => if x <? y then bound x l
                else if x >? y then bound x r
                     else true
  end.

(** Analogamente, a função [lookup d k t] retorna o valor ligado à chave [k] em [t], ou retorna o valor _default_ [d] quando [k] não é uma chave de [t]. *)

Fixpoint lookup {V : Type} (d : V) (x : key) (t : tree V) : V :=
  match t with
  | E => d
  | T l y v r => if x <? y then lookup d x l
                else if x >? y then lookup d x r
                     else v
  end.

(** Observe que se [t] não é uma árvore binária de busca então as funções [bound] e [lookup] podem retornar respostas erradas: *)

Module NotBst.
  Open Scope string_scope.

  (** De fato, considere a seguinte árvore que não é uma árvore binária de busca: *)
  
  Definition t : tree string :=
    T (T E 5 "five" E) 4 "four" (T E 2 "two" E).

  (** Ela possui uma ocorrência da chave 2, mas em uma posição não esperada pelas funções [bound] e [lookup]: *)
  
  Example not_bst_bound_wrong :
    bound 2 t = false.
  Proof.
    reflexivity.
  Qed.

  Example not_bst_lookup_wrong :
    lookup "" 2 t <> "two".
  Proof.
    simpl. unfold not. intros contra. discriminate.
  Qed.
End NotBst.

(** A segunda operação fundamental de árvores binárias de busca que estudaremos neste trabalho é a inserção. A função [insert k v t] insere a chave [k] e o valor [v] na árvore binária de busca [t], de forma a preservar a invariante de uma árvore binária de busca. *)

Fixpoint insert {V : Type} (x : key) (v : V) (t : tree V) : tree V :=
  match t with
  | E => T E x v E
  | T l y v' r => if x <? y then T (insert x v l) y v' r
                 else if x >? y then T l y v' (insert x v r)
                      else T l x v r
  end.

(** Nossa primeira tarefa será mostrar que a função [insert] de fato preserva esta invariante. Vamos então formalizar a invariante de uma árvore binária de busca. Faremos isto com a ajuda da função [ForallT]: *)

Fixpoint ForallT {V : Type} (P: key -> V -> Prop) (t: tree V) : Prop :=
  match t with
  | E => True
  | T l k v r => P k v /\ ForallT P l /\ ForallT P r
  end.

(** Esta função expressa as condições para que uma árvore satisfaça uma dada propriedade [P]: Se a árvore for vazia então a propriedade é satisfeita por vacuidade, e portanto retorna [True]. Quando a árvore não é vazia, e portanto tem a forma [T l k v r], então precisamos que o nó que tem chave [k] e valor [v] satisfaça a propriedade [P], assim como as subárvores à esquerda e à direita.

Agora vamos definir a invariante [BST], que é composta de dois construtores:

    - O primeiro construtor, denotado por [BST_E], consiste em um axioma que estabelece que uma árvore vazia é uma árvore binária de busca.

    - O segundo construtor, denotado por [BST_T], consiste na regra que diz que para que uma árvore não vazia [T l x v r] seja uma árvore binária de busca é necessário que todas as chaves da subárvore à esquerda sejam menores do que [x], todas a chaves da subárvore à direita sejam maiores do que [x], e que as subárvores à esquerda e à direita sejam também árvores binárias de busca: *)

Inductive BST {V : Type} : tree V -> Prop :=
| BST_E : BST E
| BST_T : forall l x v r,
    ForallT (fun y _ => y < x) l ->
    ForallT (fun y _ => y > x) r ->
    BST l ->
    BST r ->
    BST (T l x v r).

Hint Constructors BST.
Ltac inv H := inversion H; clear H; subst.

Inductive reflect (P : Prop) : bool -> Set :=
  | ReflectT :   P -> reflect P true
  | ReflectF : ~ P -> reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H; split.
  - intro H'.
    inv H.
    + reflexivity.
    + contradiction.
  - intro H'; subst.
    inv H; assumption.
Qed.

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

(** Vejamos que o predicado [BST] classifica correta alguns exemplos: *)

Example is_BST_ex :
  BST ex_tree.
Proof.
  unfold ex_tree.
  repeat (constructor; try lia).
Qed.

Example not_BST_ex :
  ~ BST NotBst.t.
Proof.
  unfold NotBst.t. intros contra.
  inv contra. inv H3. lia.
Qed.

(** Prove que uma árvore vazia (de qualquer tipo) é uma árvore binária de busca. *)

Theorem empty_tree_BST : forall (V : Type),
    BST (@empty_tree V).
Proof.
(** Substitua esta linha pela sua prova. *)Admitted.
  
(** Prove que a função [insert] preserva qualquer propriedade dos nós: *)

Lemma ForallT_insert : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
    ForallT P t -> forall (k : key) (v : V),
      P k v -> ForallT P (insert k v t).
Proof.
(** Substitua esta linha pela sua prova. *)Admitted.

(** Prove que ao receber uma árvore binária de busca como argumento, a função [insert] gera outra árvore binária de busca. *)

Theorem insert_BST : forall (V : Type) (k : key) (v : V) (t : tree V),
    BST t -> BST (insert k v t).
Proof.
(** Substitua esta linha pela sua prova. *)Admitted.

(** * A correção das funções de busca [lookup] e [bound] *)

(** Qual o comportamento esperado para as funções [lookup] e [bound]? Ao procurarmos uma chave na árvore binária de busca vazia com a função [lookup], devemos obter o valor default [d]: *)

Theorem lookup_empty : forall (V : Type) (d : V) (k : key),
    lookup d k empty_tree = d.
Proof.
  auto.
Qed.

(** Se inserirmos a chave [k] e valor [v] na árvore binária de busca [t], então a busca em [insert k v t] com a função [lookup] retorna [v]: *)

Theorem lookup_insert_eq : forall (V : Type) (t : tree V) (d : V) (k : key) (v : V), lookup d k (insert k v t) = v.
Proof.
  induction t; intros; simpl.
  - bdestruct (k <? k); try lia;auto.
  - bdestruct (k <? k0); bdestruct (k0 <? k); simpl; try lia; auto.
    + bdestruct (k <? k0); bdestruct (k0 <? k); try lia; auto.
    + bdestruct (k <? k0); bdestruct (k0 <? k); try lia; auto.
    + bdestruct (k0 <? k0); try lia; auto.
Qed.

(** A tática [bdall] a seguir, simplifica esta prova evitando os passos repetitivos *)
Ltac bdestruct_guard :=
  match goal with
  | |- context [ if ?X =? ?Y then _ else _ ] => bdestruct (X =? Y)
  | |- context [ if ?X <=? ?Y then _ else _ ] => bdestruct (X <=? Y)
  | |- context [ if ?X <? ?Y then _ else _ ] => bdestruct (X <? Y)
  end.

Ltac bdall :=
  repeat (simpl; bdestruct_guard; try lia; auto).

Theorem lookup_insert_eq' :
  forall (V : Type) (t : tree V) (d : V) (k : key) (v : V),
    lookup d k (insert k v t) = v.
Proof.
  induction t; intros; bdall.
Qed.

(** Prove que a busca de uma chave [k'], via a função [lookup], na árvore binária de busca [insert k v t], com [k] e [k'] distintos, retorna o resultado de buscar [k'] em [t]:  *)

Theorem lookup_insert_neq :
  forall (V : Type) (t : tree V) (d : V) (k k' : key) (v : V),
   k <> k' -> lookup d k' (insert k v t) = lookup d k' t.
Proof.
(** Substitua esta linha pela sua prova. *)Admitted.

(** Enuncie e prove os três teoremas análogos para a função [bound]. *)
    
(** A relação esperada entre as funções [bound] e [lookup] é que, se [bound k t] retorna [false] então [lookup d k t] retorna o valor default [d]. Prove este fato dado pelo seguinte teorema: *)

Theorem bound_default :
  forall (V : Type) (k : key) (d : V) (t : tree V),
    bound k t = false ->
    lookup d k t = d.
Proof.
(** Substitua esta linha pela sua prova. *)Admitted.
    
(** * Convertendo árvores binárias de busca em listas *)

From Coq Require Export Lists.List.
Export ListNotations.

(** Uma representação alternativa para as árvores binárias de busca é via listas ligadas. Neste caso, os elementos são pares [(k,v)] contendo a chave [k] e o valor [v]. Se a lista estiver ordenada pelas chaves, então duas árvores representando a mesma árvore binária de busca são convertidas na mesma lista pela função [elements]: *)

Fixpoint elements {V : Type} (t : tree V) : list (key * V) :=
  match t with
  | E => []
  | T l k v r => elements l ++ [(k, v)] ++ elements r
  end.

Example elements_ex :
    elements ex_tree = [(2, "two"); (4, "four"); (5, "five")]%string.
Proof. reflexivity. Qed.

Definition ex_tree' : tree string :=
  (T E 2 "two" (T E 4 "four" (T E 5 "five" E)))%string.

Example elements_ex' :
    elements ex_tree' = [(2, "two"); (4, "four"); (5, "five")]%string.
Proof. reflexivity. Qed.

(** Agora vamos provar que esta transformação possui algumas propriedades interessantes. Por exemplo, dada uma árvore binária de busca [t], uma chave [k] associada a um valor [v] ocorre em [t] se, e somente se o par [(k,v)] é um elemento de [elements t]. Dividiremos esta prova em duas partes: *)

(** Prove que a transformação via [elements] é completa, i.e. se uma chave [k] associada a um valor [v] ocorre em [t] então o par [(k,v)] é um elemento de [elements t]: *)

Theorem elements_complete : forall (V : Type) (k : key) (v d : V) (t : tree V),
    BST t ->
    bound k t = true ->
    lookup d k t = v ->
    In (k, v) (elements t).
Proof.
(** Substitua esta linha pela sua prova. *)Admitted.

(** Agora vamos provar que a transformação via [elements] é correta, i.e. se o par [(k,v)] é um elemento de [elements t] então a chave [k] ocorre associada ao valor [v] em [t]. 

A prova da correção exige um pouco mais de trabalho porque enquanto o predicado [BST] utiliza o predicado [ForallT] para garantir que todos os nós da árvore satisfazem uma determinada propriedade, listas utilizam o predicado [Forall] para isto. Assim, precisamos estabelecer uma relação entre estes predicados. *)

Lemma Forall_app : forall (A: Type) (P : A -> Prop) (l1 l2 : list A),
    Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  induction l1; intros; simpl; auto; inv H; constructor; auto.
Qed.

Definition uncurry {X Y Z : Type} (f : X -> Y -> Z) '(a, b) :=
  f a b.

Hint Transparent uncurry.

Lemma elements_preserves_forall : forall (V : Type) (P : key -> V -> Prop) (t : tree V), ForallT P t -> Forall (uncurry P) (elements t).
Proof.
(** Substitua esta linha pela sua prova. *)Admitted.

Theorem elements_correct : forall (V : Type) (k : key) (v d : V) (t : tree V),
    BST t ->
    In (k, v) (elements t) ->
    bound k t = true /\ lookup d k t = v.
Proof.
(** Substitua esta linha pela sua prova. *)Admitted.

(** * Uma implementação mais eficiente de [elements] *)
                                                                         
(** Uma outra forma de transformar uma árvore binária de busca em uma lista é dada pela função [elements_tr]: *)

Fixpoint elements_aux {V : Type} (t : tree V)
         (acc : list (key * V)) : list (key * V) :=
  match t with
  | E => acc
  | T l k v r => elements_aux l ((k, v) :: elements_aux r acc)
  end.

Definition elements_tr {V : Type} (t : tree V) : list (key * V) :=
  elements_aux t [].

(** Prove que [elements_tr] e [elements] fazem a mesma transformação. *)

Lemma elements_tr_elements : forall (V : Type) (t : tree V),
    elements_tr t = elements t.
Proof.
(** Substitua esta linha pela sua prova. *)Admitted.

(** Prove que a transformação [elements_tr] é correta utilizando a correção de [elements]. *)

Corollary elements_tr_correct :
  forall (V : Type) (k : key) (v d : V) (t : tree V),
    BST t ->
    In (k, v) (elements_tr t) ->
    bound k t = true /\ lookup d k t = v.
Proof.
(** Substitua esta linha pela sua prova. *)Admitted.


