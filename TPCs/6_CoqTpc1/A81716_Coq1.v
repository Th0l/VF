(* ================================================================== *)
Section EX_1.

Variable A:Prop. 
Variable B:Prop. 
Variable C:Prop. 
Variable D:Prop.


Lemma ex_1_1 : (A -> C) /\ (B -> C) -> (A /\ B) -> C.
Proof.
  intros.
  apply H.
  apply H0.
Qed.

Lemma ex_1_2 : (~A \/ ~B) -> ~(A /\ B).
Proof.
  intros.
  intro.
  destruct H.
  destruct H0.
  apply H.
  apply H0.
  destruct H0.
  apply H.
  apply H1.
Qed.

Lemma ex_1_3 : (A -> (B \/ C)) /\ (B -> D) /\ (C -> D) -> (A -> D).
Proof.
  intros.
  destruct H.
  destruct H1.
  destruct H.
  assumption.
  apply H1.
  assumption.
  apply H2.
  assumption.
Qed.

Lemma ex_1_4 : (A /\ B) -> ~(~A \/ ~B).
Proof.
  intros.
  intro.
  destruct H.
  destruct H0.
  contradiction.
  contradiction.
Qed.
  
End EX_1.

Section EX_2.

Variable X : Set.
Variables P Q R : X -> Prop.

Lemma ex_2_1 : (forall x : X, P x -> Q x) -> (forall y : X, ~(Q y)) -> (forall x : X, ~(P x)).
Proof.
  intros.
  intro.
  destruct (H0 x).
  apply H.
  assumption.
Qed.

Lemma ex_2_2 : (forall x:X, P x \/ Q x) -> (exists y:X, ~Q y) -> (forall x:X, R x -> ~P x) -> (exists x:X, ~R x).
Proof.
  intros.
  destruct H0.
  exists x.
  intro.
  destruct (H1 x).
  assumption.
  destruct (H x).
  assumption.
  contradiction. 
Qed.

End EX_2.

Section EX_3.

Variable A B : Prop.
Variable X : Set.
Variable P : X -> Prop.

Hypothesis Excluded_middle : forall P : Prop, P \/ ~P.

Lemma ex_3_1 : (~A -> B) -> (~B -> A).
Proof.
  intros.
  destruct Excluded_middle with A.
  assumption.
  destruct H0.
  apply H.
  assumption.
Qed.

Lemma ex_3_2 : ~(exists x:X, ~P x) -> (forall x:X, P x).
Proof.
  intros.
  destruct Excluded_middle with (P x).
  exact H0.
  destruct H.
  exists x.
  assumption.
Qed.

Lemma ex_3_3 : ~(forall x:X, ~P x) -> (exists x:X, P x).
Proof.
  intros.
  destruct Excluded_middle with (exists x, P x).
  exact H0.
  destruct H.
  intro x0.
  destruct Excluded_middle with (~P x0).
  assumption.
  unfold not.
  intro.
  destruct H0.
  exists x0.
  assumption.
Qed.

End EX_3.