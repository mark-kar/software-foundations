Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p: rgb).

Definition monochrome (c : color) : bool := 
  match c with
  | black => true
  | white => true
  | primary _ => false
  end.

Definition isred (c : color) : bool := 
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Module TuplePlayground.
  Inductive bit : Type :=
  | B1
  | B0.

  Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

  Definition all_zero (nb: nybble) : bool := 
  match nb with
  | (bits B0 B0 B0 B0) => true
  | _ => false
  end.

  Compute (all_zero (bits B0 B0 B0 B0)).
  Compute (all_zero (bits B0 B0 B1 B0)).
End TuplePlayground.


Module NatPlayground.
  Inductive nat : Type :=
    | O
    | S (n : nat).

  Definition pred (n : nat) := 
    match n with
    | O => O
    | S n' => n'
    end.
End NatPlayground.


Check (S (S (S (S O)))).

Definition minus_two (n : nat) := 
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minus_two 4).

Check S.

Fixpoint even (n : nat) : bool := 
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n : nat) : bool := 
  negb (even n).

Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2: odd 4 = false.
Proof. simpl. reflexivity. Qed.

Fixpoint plus (n : nat) (m : nat) : nat := 
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute (plus 100 3).

Fixpoint mult (n m : nat): nat := 
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Example test_rigth_zero: (mult 4 0) = 0.
Proof. reflexivity. Qed.


Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | O, _ => O
  | S _, O => n
  | S n', S m' => minus n' m'
  end. 

Fixpoint factorial (n : nat) : nat := 
  match n with
  | O => 1
  | S n' => mult n (factorial n')
  end.

Compute (factorial 5).

Notation "x + y" := (plus x y) (at level 50, left associativity).
Notation "x * y" := (mult x y) (at level 40, left associativity).
Notation "x - y" := (minus x y) (at level 50, left associativity).

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | _ => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => leb n' m'
            end
  end.

Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

Definition ltb (n m : nat) : bool :=
  (negb (n =? m)) && (n <=? m).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
intros n. simpl. reflexivity. Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
intros n. reflexivity. Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m : nat, n = m -> n + n = m + m. 
Proof.
intros n m.
intros H.
rewrite -> H.
reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat, 
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1 H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
Qed.

Check mult_0_l.

Check mult_n_O.

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.

Check mult_n_Sm.

Theorem mult_n_1 : forall n : nat, n * 1 = n.
Proof.
  intros n.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity. Qed.

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

















