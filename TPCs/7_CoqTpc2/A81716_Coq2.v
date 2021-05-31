

(* ================================================================== *)
(* ===================== Reasoning about lists  ===================== *)
(* ================================================================== *)

Set Implicit Arguments.

Require Import List.
Require Import Omega.
Import ListNotations.

Inductive In (A:Type) (y:A) : list A -> Prop :=
| InHead : forall (xs:list A), In y (cons y xs)
| InTail : forall (x:A) (xs:list A), In y xs -> In y (cons x xs).


Inductive Prefix (A:Type) : list A -> list A -> Prop :=
| PreNil : forall (l:list A), Prefix nil l
| PreCons : forall (x:A) (l1 l2:list A), Prefix l1 l2 -> Prefix (x::l1) (x::l2).


Inductive SubList (A:Type) : list A -> list A -> Prop :=
| SLnil : forall (l:list A), SubList nil l
| SLcons1 : forall (x:A) (l1 l2:list A), SubList l1 l2 -> SubList (x::l1) (x::l2)
| SLcons2 : forall (x:A) (l1 l2:list A), SubList l1 l2 -> SubList l1 (x::l2).


Lemma ex1_a : SubList (5::3::nil) (5::7::3::4::nil).
Proof.
  constructor.
  constructor.
  constructor.  
  constructor.
Qed.


Lemma ex1_b : forall (A:Type) (l:list A), SubList l l.
Proof.
  intros.
  induction l.
  constructor.
  constructor.
  assumption.
Qed.

Lemma ex1_c : forall (A B:Type) (f:A->B) (l1 l2:list A), SubList l1 l2 -> SubList (map f l1) (map f l2).
Proof.
  intros.
  induction H.
  constructor.
  simpl.
  constructor.
  assumption.
  simpl.
  constructor.
  assumption.
Qed.

Lemma ex1_d : forall (A:Type) (x:A) (l : list A), In x l -> exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros.
  induction H.
  exists nil. exists xs. simpl. reflexivity.
  destruct IHIn as [I1 H1]. destruct H1 as [I2 H1]. exists (x0::I1). exists I2.  rewrite <-app_comm_cons.
  rewrite H1. reflexivity.
Qed.

Fixpoint drop (A:Type) (n:nat) (l : list A)  : list A :=  
  match n with               (* Dar match com n, pois a guarda para quando l é nil está definida na função tl do lists.*)
  | 0 => l                   (* Quando n igual a 0, retorna a lista. *)
  | S n' => drop n' (tl l)   (* Quando n maior que 0, remove-se o primeiro elemento com a função tl de lists. *)
  end.

Eval compute in drop 2 (5::7::3::4::nil). (* Provar q funciona *)

Lemma ex2_a : drop 2 (5::7::3::4::nil) = (3::4::nil).
Proof.
  constructor.
Qed.

Lemma ex2_b : forall (A:Type) (n:nat) (l:list A), SubList (drop n l) l.
Proof.
  intros H n.
  induction n.
  - unfold drop. apply ex1_b.
  - induction l.
    + simpl. apply IHn.
    + simpl. constructor. apply IHn.
Qed.

Inductive Sorted : list nat -> Prop :=
| sort0 : Sorted nil
| sort1 : forall a:nat, Sorted (a::nil)
| sort2 : forall z1 z2:nat, forall l:list nat, z1 <= z2 -> Sorted (z2 :: l) -> Sorted (z1 :: z2 :: l).

Lemma ex3_a : forall (x y:nat) (l:list nat), x<=y -> (Sorted (y::l)) -> Sorted (x::l).
Proof.
  intros.
  induction l.
  - constructor.
  - constructor.
    + rewrite H. inversion H0. exact H3.
    + inversion H0. exact H5.
Qed.

(*---------- LEMAS AUXILIARES PARA RESOLVER O EX3_B ----------*)
Lemma sorted_min : forall (x y:nat) (l:list nat), Sorted(x::y::l) -> x <= y.
Proof.
  intros.
  inversion H.
  exact H2.
Qed.

Lemma aux: forall (y a :nat) (l:list nat),In y (a::l)  ->  y = a \/ In y l.
Proof.
intros.
inversion H. 
- left. trivial. 
- right. assumption.
Qed.

Lemma auxObvious: forall (x y :nat) (l:list nat), x<=y -> Sorted(x::y::l) -> Sorted(x::l).
Proof.
  intros.
  inversion H0.
  generalize H5.
  generalize H3.
  apply ex3_a.
Qed.
(*---------- ----- ---------- ---- -------- - ----- ----------*)

Lemma ex3_b : forall (x y:nat) (l:list nat), (In y l) /\ (Sorted (x::l)) -> x <= y.
Proof.
  intros.
  inversion H.
  induction l.
  - inversion H0.
  - apply sorted_min in H1. apply aux in H0. destruct H0.
    + rewrite H0. exact H1.
    + apply IHl.
      * split.
        { - exact H0. }
        { - destruct H. generalize H2. generalize H1. apply auxObvious. }
      * exact H0.
      * destruct H. generalize H2. generalize H1. apply auxObvious.
Qed.

Lemma ex4_a : forall (A:Type) (l:list A), Prefix l l.
Proof.
  intros.
  induction l.
  constructor.
  constructor.
  assumption.
Qed.

(*---------- LEMAS AUXILIARES PARA RESOLVER O EX4_B ----------*)
Lemma pref_conc_def : forall (A:Type) (l1 l2:list A), Prefix l1 l2 -> exists l3, l2 = l1 ++ l3. 
Proof.
  intros.
  induction H.
    - exists l. simpl. trivial.
    - destruct IHPrefix. exists x0. rewrite H0. apply app_comm_cons.
Qed.

Lemma pref_conc_prefix : forall (A:Type) (l1 l2:list A), Prefix l1 (l1++l2).
Proof.
  intros.
  induction l1.
  - simpl. constructor.
  - simpl. constructor. exact IHl1.
Qed.
(*---------- ----- ---------- ---- -------- - ----- ----------*)

Lemma ex4_b : forall (A:Type) (l1 l2 l3:list A), Prefix l1 l2 /\ Prefix l2 l3 -> Prefix l1 l3.
Proof.
  intros.
  destruct H as [H1 H2].
  apply pref_conc_def in H1.
  destruct H1.
  apply pref_conc_def in H2.
  destruct H2.
  rewrite  H0.
  rewrite  H.
  assert(((l1++x)++x0)=(l1++(x++x0))). 
    - apply app_assoc_reverse. 
    - rewrite H1. apply pref_conc_prefix.
Qed.

Lemma auxEqual : forall (A:Type) (x:A) (l1 l2:list A), l1 = l2 -> x::l1 = x::l2.
Proof.
  intros.
  induction H.
  trivial.
Qed.

Lemma ex4_c : forall (A:Type) (l1 l2:list A), Prefix l1 l2 /\ Prefix l2 l1 -> l1 = l2.
Proof.
  intros. 
  destruct H.
  induction H.
  - inversion H0. trivial.
  - apply auxEqual. apply IHPrefix. inversion H0. exact H2. 
Qed.
