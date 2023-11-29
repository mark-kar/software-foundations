Check true.
Check andb.
Check negb.
Check orb.
Check plus.
Check mult.
Check eq.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
intros [] [].
- reflexivity.
- intros H.
  rewrite <- H.
  reflexivity.
- reflexivity.
- intros H.
  rewrite <- H.
  reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  (0 =? (n + 1)) = false.
Proof.
intros [|n].
- reflexivity.
- reflexivity.
Qed.

Theorem identity_fn_applied_twice : forall (f : bool -> bool),
  (forall x : bool, f x = x) -> forall b : bool, f (f b) = b.
Proof.
intros f.
intros H.
intros b.
rewrite <- H.
rewrite <- H.
reflexivity.
Qed.

Theorem negation_fn_applied_twice : forall (f : bool -> bool),
  (forall x : bool, f x = negb x) -> forall b : bool, f (f b) = b.
Proof.
intros f.
intros H.
intros b.
rewrite -> H.
rewrite -> H.
destruct b eqn:B.
- reflexivity.
- reflexivity.
Qed.

Lemma neutral_false : forall b : bool,
  orb false b = b.
Proof.
intros [].
- reflexivity.
- reflexivity.
Qed.

Lemma orb_always_true : forall b : bool,
  orb true b = true.
Proof.
intros [].
- reflexivity.
- reflexivity.
Qed.

Theorem andb_eq_orb : forall b c : bool,
  (andb b c = orb b c) -> b = c.
Proof.
intros b c. destruct b eqn:Eb.
- rewrite -> orb_always_true.
  intros H.
  rewrite <- H.
  reflexivity.
- rewrite -> neutral_false.
  intros H.
  rewrite <- H.
  reflexivity.
Qed.











