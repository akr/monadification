From mathcomp Require Import ssreflect ssrbool eqtype ssrfun ssrnat.
Require Import Monadification.monadification.
Require Import List.

Set Monadification Verbose. (* show the original definition and the monadified definition *)

Definition counter_with A : Type := nat * A.

Definition ret {A} (x : A) := (0, x).
Definition bind {A} {B} (x' : counter_with A) (f : A -> counter_with B) :=
  let (m, x) := x' in
  let (n, y) := f x in
  (m+n, y).

Monadify Type counter_with.
Monadify Return @ret.
Monadify Bind @bind.

Definition consM {T} (hd : T) tl := (1, cons hd tl).
Monadify Action cons => @consM.

Notation "'return' t" := (ret t) (at level 100).
Notation "x >>= y" := (bind x y) (at level 65, left associativity).

Definition test3 := true :: false :: true :: nil.

Monadification test3.
Print test3M.
Compute test3M.

Monadification app rev rev'.

Compute appM nat (1::2::3::nil) (4::5::6::7::8::nil).

Lemma NumConsInApp T s1 s2 : appM T s1 s2 = (length s1, app s1 s2).
Proof.
  elim: s1; first by [].
  move=> a s1 IH /=.
  by rewrite IH /= addnS addn0.
Qed.

(* naive reverse using app. *)
Compute revM nat nil. (* 0 *)
Compute revM nat (1::nil). (* 1 *)
Compute revM nat (1::2::nil). (* 3 *)
Compute revM nat (1::2::3::nil). (* 6 *)
Compute revM nat (1::2::3::4::nil). (* 10 *)
Compute revM nat (1::2::3::4::5::nil). (* 15 *)
Compute revM nat (1::2::3::4::5::6::nil). (* 21 *)

(* number of cons invocation is quadratic *)
Lemma NumConsInRev T s : revM T s = (((length s) * (length s).+1)./2, rev s).
Proof.
  elim: s; first by [].
  move=> a s IH /=.
  rewrite -/addn_rec -/addn -/muln /= IH /= NumConsInApp /=.
  f_equal.
  rewrite rev_length add1n addnS [length s + _]addnC [_ * _.+2]mulnSr.
  by rewrite -addnA addnn halfD odd_double andbF /= add0n doubleK.
Qed.

(* efficient reverse *)
Compute rev'M nat nil. (* 0 *)
Compute rev'M nat (1::nil). (* 1 *)
Compute rev'M nat (1::2::nil). (* 2 *)
Compute rev'M nat (1::2::3::nil). (* 3 *)

Print rev_appendM.
Lemma NumConsInRevAppend T s1 s2 :
  rev_appendM T s1 s2 = (length s1, rev_append s1 s2).
Proof.
  elim: s1 s2; first by [].
  move=> a s1 IH s2 /=.
  by rewrite IH add1n.
Qed.

Lemma NumConsInRev' T s : rev'M T s = (length s, rev' s).
Proof.
  by rewrite /rev'M NumConsInRevAppend.
Qed.
