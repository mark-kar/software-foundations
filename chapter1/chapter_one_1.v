Inductive bool : Type :=
  | true
  | false.


Definition negb (b: bool) := 
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1: bool) (b2: bool) := 
  match b1 with
  | true => b2
  | false => false  
  end.

Definition orb (b1: bool) (b2: bool) := 
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || true || false = true.
Proof. simpl. reflexivity. Qed.

Definition negb' (b: bool) := 
  if b then false
  else true.

Definition andb' (b1: bool) (b2: bool) := 
  if b1 then b2
  else false.

Definition orb' (b1: bool) (b2: bool) := 
  if b1 then true
  else b2.

Definition nandb (b1: bool) (b2: bool) : bool := 
  negb (andb b1 b2).

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1: bool) (b2: bool) (b3: bool) : bool := 
  andb (andb b1 b2) b3.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.
Check (negb true).

Check negb.







