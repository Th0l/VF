Require Import ZArith.

Require Import List.

Require Extraction. 

Set Implicit Arguments.

Extraction Language Haskell.

(************************
**** Exercício 1.
************************)

(**** (a) ****)

Inductive mkList (A:Type) : nat -> A -> (list A) -> Prop :=
  | mkNil : forall (a:A), mkList 0 a nil
  | mkSec : forall (n:nat) (a:A) (l:list A), mkList n a l -> mkList (S n) a (a::l).

Theorem mkList_correct : forall (A:Type) (n:nat) (x:A), { l:list A | mkList n x l }.
Proof.
  intros.
  induction n.
  - exists nil. constructor.
  - destruct IHn. exists (x::x0). constructor. assumption.
Qed.

(* Extração do código *)
Recursive Extraction mkList_correct.

(**** (b) ****)

Inductive pairSum : list (nat*nat) -> list nat -> Prop :=
  | sumNil : pairSum nil nil
  | sumSec : forall (p: (nat*nat)) (inp: list (nat*nat)) (res: list nat), pairSum inp res -> pairSum (p::inp) (((fst p)+(snd p))::res).

Theorem pairSum_correct : forall (inp: list(nat*nat)), {res: list nat | pairSum inp res}.
Proof.
  intros.
  induction inp.
  - exists nil. constructor.
  - elim IHinp.
    + intros. exists ( ((fst a) + (snd a))::x ). constructor. assumption.
Qed.

(* Extração do código *)
Recursive Extraction pairSum_correct.


(************************
**** Exercício 2.
************************)
Open Scope Z_scope. 

Fixpoint count (z:Z) (l:list Z) {struct l} : nat :=
  match l with
  | nil => 0%nat
  | (z' :: l') => if (Z.eq_dec z z')
                  then S (count z l')
                  else count z l'
  end.

(**** (a) ****)
Lemma count_corr : forall (x:Z) (a:Z) (l:list Z), x <> a ->  count x (a :: l) = count x l.
Proof.
  intros.
  simpl.
  elim (Z.eq_dec x a).
  - intros. contradiction.
  - intros. trivial.
Qed.

(**** (b) ****)
Inductive countRel : Z -> list Z -> nat -> Prop :=
  | countNil : forall e:Z, countRel e nil 0
  | countIf : forall (e:Z) (l: list Z) (n: nat), countRel e l n -> countRel e (e::l) (S n)
  | countElse : forall (e e':Z) (l: list Z) (n: nat), e <> e' -> countRel e l n -> countRel e (e'::l) n.

(**** (c) ****)
Lemma count_correct : forall (x:Z) (l:list Z), countRel x l (count x l).
Proof.
  intros.
  induction l.
  - simpl. constructor.
  - simpl. elim (Z.eq_dec x a).
    + intros. rewrite <- a0. constructor. assumption.
    + intros. destruct IHl. 
      * constructor.
        -- assumption.
        -- constructor.
      * constructor.
        -- assumption.
        -- constructor. assumption.
      * constructor.
        -- assumption.
        -- constructor.
          ++ assumption.
          ++ assumption.
Qed.

Close Scope Z_scope.
(************************************************************* END *************************************************************)