From mathcomp Require Import ssreflect ssrbool eqtype ssrfun ssrnat seq.
Require Import monadification.monadification.

Set Monadification Verbose. (* show the original definition and the monadified definition *)

Definition ret {A} (x : A) := Some x.
Definition bind {A} {B} (x' : option A) (f : A -> option B) :=
  match x' with
  | None => None
  | Some x => f x
  end.

Monadify Type option.
Monadify Return @ret.
Monadify Bind @bind.

Notation "'return' t" := (ret t) (at level 100).
Notation "x >>= y" := (bind x y)
  (at level 65, left associativity).

Definition check x :=
  if Nat.log2 x < 32 then Some x else None.
Definition SM a := check a.+1.
Definition addM a b := check (a + b).
Definition mulM a b := check (a * b).

(* addn, muln and S may overflow *)
Monadify Action addn => addM.
Monadify Action muln => mulM.
Monadify Action S => SM.

Definition test (a b c : nat) : nat := if eqn (a + b + c) 0 then a else b.

Monadification test.
Print testM.

Require PeanoNat.

Lemma testM_is_test a b c : Nat.log2 (a + b + c) < 32 ->
  (testM a b c) = Some (test a b c).
Proof.
intro H.
have H1 : Nat.log2 (a + b) < 32. 
  apply: leq_ltn_trans H.
  by apply/leP/PeanoNat.Nat.log2_le_mono/leP/leq_addr.
rewrite /testM /testM /test /bind /addM /check H1 H /=.
by case: ifP.
Qed.

Fixpoint pow a k :=
  match k with
  | O => 1
  | S k' => a * pow a k'
  end.

Monadification pow.
Print powM.

Lemma pow_expn a b : pow a b = a ^ b.
Proof. 
induction b => /=.
  by rewrite expn0.
by rewrite IHb expnS.
Qed.

Theorem powM_ok :
  forall a b, Nat.log2 (pow a b) < 32 ->
  (powM a b) = Some (pow a b).
Proof.
induction b => //= H.
rewrite IHb /= /mulM /check.
  by rewrite H.
destruct a.
  destruct b.
    by rewrite /= PeanoNat.Nat.log2_1.
  by rewrite pow_expn exp0n.
apply: leq_ltn_trans H.
apply/leP/PeanoNat.Nat.log2_le_mono/leP.
by rewrite mulSn leq_addr.
Qed.
