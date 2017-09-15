From mathcomp Require Import ssreflect ssrbool eqtype ssrfun ssrnat seq.
Require Import monadification.monadification.

Set Monadification Verbose. (* show the original definition and the monadified definition *)

Definition counter_with A : Type := nat * A.

Definition ret {A} (x : A) := (0, x).
Definition bind {A} {B} (x' : counter_with A) (f : A -> counter_with B) :=
  let (n, x) := x' in
  let (m, y) := f x in
  (n+m, y).

Definition consM {A} (hd : A) tl := (1, cons hd tl).

Monadify Type counter_with.
Monadify Return @ret.
Monadify Bind @bind.
Monadify Action cons => @consM.

Notation "'return' t" := (ret t) (at level 100).
Notation "x >>= y" := (bind x y) (at level 65, left associativity).

Definition test3 := true :: false :: true :: nil.

Monadification test3.
Print test3M.
Compute test3M.

Monadification cat.
Compute catM nat (1::2::3::nil) (4::5::6::7::8::nil).

Lemma NumConsInCat : forall A s1 s2, catM A s1 s2 = (size s1, cat s1 s2).
Proof.
  move=> A.
  elim; first by [].
  move=> a s1 IH s2 /=.
  by rewrite IH /= addnS addn0.
Qed.

(* naive reverse using ++ (cat).  Same as List.rev except using cat of ssreflect. *)
Fixpoint nrev {A} (l:seq A) : seq A :=
  match l with
    | nil => nil
    | x :: l' => nrev l' ++ x :: nil
  end.

Monadification nrev.
Compute nrevM nat nil. (* 0 *)
Compute nrevM nat (1::nil). (* 1 *)
Compute nrevM nat (1::2::nil). (* 3 *)
Compute nrevM nat (1::2::3::nil). (* 6 *)
Compute nrevM nat (1::2::3::4::nil). (* 10 *)
Compute nrevM nat (1::2::3::4::5::nil). (* 15 *)
Compute nrevM nat (1::2::3::4::5::6::nil). (* 21 *)

(* Same as rev_length *)
Lemma size_nrev : forall A (s:seq A), size (nrev s) = size s.
Proof.
  move=> A.
  elim; first by [].
  move=> a s IH /=.
  by rewrite size_cat IH /= addn1.
Qed.

(* number of cons invocation is quadratic *)
Lemma NumConsInNRev : forall A s, nrevM A s = (((size s) * (size s).+1)./2, nrev s).
Proof.
  move=> A.
  elim; first by [].
  move=> a s IH.
  rewrite [size _]/= mulnC mulSnr mulSnr -addnA addnn.
  rewrite halfD odd_double andbF add0n doubleK.
  rewrite [nrevM _ _]/= IH [_ >>= _]/= NumConsInCat.
  by rewrite size_nrev add1n.
Qed.

(* efficient reverse *)
Monadification rev.

Compute revM nat nil. (* 0 *)
Compute revM nat (1::nil). (* 1 *)
Compute revM nat (1::2::nil). (* 2 *)
Compute revM nat (1::2::3::nil). (* 3 *)

Print catrevM.
Lemma NumConsInCatrev : forall (A : Type) (s1 s2 : seq A),
  catrevM A s1 s2 = (size s1, catrev s1 s2).
Proof.
  move=> A.
  elim; first by [].
  move=> a s1 IH s2 /=.
  by rewrite IH add1n.
Qed.

Lemma NumConsInRev : forall (A : Type) (s : seq A), revM A s = (size s, rev s).
Proof.
  move=> A s.
  by rewrite /revM NumConsInCatrev.
Qed.
