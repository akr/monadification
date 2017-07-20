(* complexity of rank *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq ssrfun.
From mathcomp Require Import div prime.
Require Import Monadification.monadification.

Require Import Monadification.sample.listutils.
Require Import Monadification.sample.natutils.
Require Import Monadification.sample.bits.

Require Import Monadification.sample.rank.

Definition counter_with A : Type := nat * A.

Definition ret {A} (x : A) := (0, x).
Definition bind {A} {B} (x' : counter_with A) (f : A -> counter_with B) :=
  let (n, x) := x' in
  let (m, y) := f x in
  (n+m, y).

Monadify Type counter_with.
Monadify Return @ret.
Monadify Bind @bind.

Definition bcountM (b : bool) n m (s : bits) := (m, bcount b n m s).
Monadify Action bcount => bcountM.

Notation "'return' t" := (ret t) (at level 100).
Notation "x >>= y" := (bind x y) (at level 65, left associativity).

Set Monadification Verbose. (* show the original definition and the monadified definition *)

Monadify Pure bitlen divn modn.

Monadification rank_init.
Monadification rank_lookup.

Print rank_init.
Print rank_initM.
Print buildDirM.
Print buildDir1M.
Print buildDir2M.
Print rank_lookupM.

Definition sample_bits := bseq (true::false::true::true::nil).
Compute rank_init true sample_bits.
Compute rank_lookup (rank_init true sample_bits) 3.
Compute rank_initM true sample_bits.
Compute rank_initM true sample_bits >>= fun aux => rank_lookupM aux 3.

Lemma BuildDir2NumBcount b s sz2 c i D2 m2 :
  buildDir2M b s sz2 c i D2 m2 = (c * sz2, buildDir2 b s sz2 c i D2 m2).
Proof.
  elim: c i D2 m2; first by [].
  move=> c IH i D2 m2 /=.
  by rewrite IH.
Qed.

Lemma BuildDir1NumBcount b s k sz1 sz2 c i D1 D2 m1 :
  buildDir1M b s k sz1 sz2 c i D1 D2 m1 =
  (c * k * sz2, buildDir1 b s k sz1 sz2 c i D1 D2 m1).
Proof.
  elim: c i D1 D2 m1; first by [].
  move=> c IH i D1 D2 m1 /=.
  by rewrite /bind BuildDir2NumBcount BuildDir2Val IH -mulnA -mulnA.
Qed.

Lemma BuildDirNumBcount b s k sz2 w1 w2 :
  0 < k ->
  let n := bsize s in
  buildDirM b s k sz2 w1 w2 = (n %/ sz2 * sz2, buildDir b s k sz2 w1 w2).
Proof.
  move=> Hk n.
  rewrite /buildDirM /bind /ret -/n.
  rewrite BuildDir1NumBcount BuildDir1Val; last by [].
  rewrite BuildDir2NumBcount BuildDir2Val.
  f_equal.
    by rewrite addn0 -mulnDl -divn_eq.
  rewrite /buildDir BuildDir1Val; last by [].
  by rewrite BuildDir2Val.
Qed.

Lemma RankInitNumBitsExamined b s :
  let n := bsize s in
  rank_initM b s = (n %/ (bitlen n).+1 * (bitlen n).+1, rank_init b s).
Proof.
  move=> n.
  rewrite /rank_initM.
  rewrite -/n BuildDirNumBcount; last by [].
  rewrite /bind /ret.
  f_equal.
  by rewrite addn0.
Qed.

Lemma RankLookupNumBitsExamined b s i :
  let n := bsize s in
  let aux := rank_init b s in
  rank_lookupM aux i = (i %% (bitlen n).+1, rank_lookup aux i).
Proof.
  rewrite /rank_init BuildDirVal; last first.
      by [].
    by [].
  rewrite /rank_lookupM /bind /ret.
  rewrite /rank_lookup.
  rewrite /query_bit /blksz2 /input_bits /dir1 /dir2 /ratio.
  rewrite /bcountM.
  f_equal.
  by rewrite addn0.
Qed.
