(* rank definition and correctness *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq ssrfun.
From mathcomp Require Import div prime.
Require Import Monadification.monadification.

Require Import Monadification.sample.listutils.
Require Import Monadification.sample.natutils.
Require Import Monadification.sample.bits.

(* specification of rank *)
Definition rank (b : bool) i s := count_mem b (take i s).

Definition neq0 n := n.-1.+1.

Inductive DArr : Type := darr : nat -> seq nat -> DArr.
Definition bwidth D := let: darr w d := D in w.
Definition seq_of_D D := let: darr w d := D in d.
Definition emptyD w := darr w nil.
Definition pushD D v := let: darr w d := D in darr w (v :: d).
Definition lookupD D i :=
  let: darr w d := D in nth 0 d (size d - i.+1).
Definition sizeD D := let: darr w d := D in size d.

Record Aux : Set := mkAux {
  query_bit: bool;
  input_bits: bits;
  ratio: nat; (* number of small blocks in a large block *)
  blksz2: nat; (* number of bits in a small block *)
  dir1: DArr;
  dir2: DArr;
}.

Fixpoint buildDir2 (b : bool) (s : bits) sz2 c i D2 m2 :=
  if c is cp.+1 then
    let m := bcount b i sz2 s in
    buildDir2 b s sz2 cp (i + sz2) (pushD D2 m2) (m2 + m)
  else
    (D2, m2).

Fixpoint buildDir1 (b : bool) (s : bits) k sz1 sz2 c i D1 D2 m1 :=
  if c is cp.+1 then
    let D1' := pushD D1 m1 in
    let (D2', m2) := buildDir2 b s sz2 k i D2 0 in
    buildDir1 b s k sz1 sz2 cp (i + sz1) D1' D2' (m1 + m2)
  else
    (D1, D2, m1).

Definition buildDir (b : bool) (s : bits) k sz2 w1 w2 :=
  let sz1 := k * sz2 in
  let n := bsize s in
  let n2 := n %/ sz2 in (* number of small blocks *)
  let n1 := n2 %/ k in (* number of large blocks *)
  let: (D1, D2, m1) := buildDir1 b s k sz1 sz2 n1 0 (emptyD w1) (emptyD w2) 0 in
  let (D2, m2) := buildDir2 b s sz2 (n2 %% k) (n1 * sz1) D2 0 in
  (pushD D1 m1, pushD D2 m2).

(*
  large block size: (lg n) ^ 2
  small block size :sz2: (lg n)
  large block size / small block size :k: lg n
  large block table size : n / (lg n)^2 * (lg n) = n / (lg n)
  small block table size :
    n / (lg n) * (lg (lg^2 n)) = n / (lg n) * (2 * lg (lg n))
    = 2n * (lg lg n) / (lg n)
*)
Definition rank_init b s :=
  let n := bsize s in
  let kp := bitlen n in (* k - 1 *)
  let k := kp.+1 in  (* sz1 / sz2 *)
  let sz2p := bitlen n in (* sz2 - 1 *)
  let sz2 := sz2p.+1 in
  let sz1 := k * sz2 in
  let nn := n %/ sz2 in (* number of small blocks *)
  let w1 := neq0 (bitlen (n %/ sz1 * sz1)) in
  let w2 := neq0 (bitlen (kp * sz2)) in
  let (D1, D2) := buildDir b s k sz2 w1 w2 in
  mkAux b s k sz2 D1 D2.

Definition rank_lookup aux i :=
  let b := query_bit aux in
  let s := input_bits aux in
  let k := ratio aux in
  let sz2 := blksz2 aux in
  let D1 := dir1 aux in
  let D2 := dir2 aux in
  let j2 := i %/ sz2 in (* index in the second-level directory *)
  let j3 := i %% sz2 in (* index in a small block *)
  let j1 := j2 %/ k in (* index in the first-level directory *)
  lookupD D1 j1 + lookupD D2 j2 +
  bcount b (j2 * sz2) j3 s.

Lemma sizeD_pushD D v : sizeD (pushD D v) = (sizeD D).+1.
Proof.
  case: D => w d.
  by rewrite /sizeD /pushD.
Qed.

Lemma lookupD_pushD_sizeD D v : lookupD (pushD D v) (sizeD D) = v.
Proof.
  case: D => w d.
  by rewrite /lookupD /pushD /sizeD /= subnn /=.
Qed.

Lemma lookupD_pushD D v i : i < sizeD D -> lookupD (pushD D v) i = lookupD D i.
Proof.
  case: D => w d.
  rewrite /lookupD /pushD /sizeD /= subSS => H.
  by rewrite subnS -{1}[size d - i]prednK; last rewrite subn_gt0.
Qed.

Definition catDs (D : DArr) (s : seq nat) :=
  let: darr w d := D in darr w (catrev s d).

Lemma BuildDir2Val b s sz2 c i D2 m2 :
  buildDir2 b s sz2 c i D2 m2 =
  (catDs D2 (map (fun j => m2 + bcount b i (j * sz2) s) (iota 0 c)),
   m2 + bcount b i (c * sz2) s).
Proof.
  case: D2 => w2 d2.
  elim: c => [|cp IH] /= in i d2 m2 *.
    by rewrite mul0n bcount_empty addn0.
  rewrite IH /=.
  congr (_, _); last first.
    by rewrite -addnA bcount_adjacent -mulSn.
  congr (darr _ (catrev _ _)); last first.
    by rewrite mul0n bcount_empty addn0.
  rewrite -[1]add1n iota_addl -map_comp.
  apply eq_map => j /=.
  by rewrite -addnA bcount_adjacent mulSn.
Qed.

Lemma BuildDir1Val b s k sz2 c i D1 D2 m1 :
  0 < k ->
  let sz1 := k * sz2 in
  buildDir1 b s k sz1 sz2 c i D1 D2 m1 =
  (catDs D1 (map (fun j => m1 + bcount b i (j * sz1) s) (iota 0 c)),
   catDs D2 (map (fun j => bcount b (i + (j %/ k * sz1)) (j %% k * sz2) s) (iota 0 (c * k))),
   m1 + bcount b i (c * sz1) s).
Proof.
  move=> Hk sz1.
  case: D1 => w1 d1.
  case: D2 => w2 d2.
  elim: c i d1 d2 m1.
    move=> i d1 d2 m1 /=.
    by rewrite mul0n bcount_empty addn0.
  move=> cp IH i d1 d2 m1 /=.
  rewrite BuildDir2Val IH /=.
  congr (_, _); last by rewrite add0n -/sz1 -addnA bcount_adjacent.
  congr ((darr w1 (catrev _ _)), (darr w2 _)).
      rewrite -[1]add1n iota_addl -map_comp.
      apply eq_map => j /=.
      by rewrite add0n -/sz1 -addnA bcount_adjacent.
    by rewrite mul0n bcount_empty addn0.
  rewrite mulSn iota_add add0n map_cat catrev_catl.
  congr (catrev _ _).
    rewrite -{6}[k]addn0 iota_addl -map_comp.
    apply eq_map => j /=.
    rewrite divnDl; last by [].
    rewrite modnDl.
    congr bcount.
    by rewrite divnn Hk /= add1n -addnA -mulSn.
  congr (catrev _ d2).
  apply eq_in_map => j.
  rewrite mem_iota add0n => /andP [_ Hj].
  rewrite add0n.
  rewrite divn_small; last by [].
  rewrite modn_small; last by [].
  by rewrite mul0n addn0.
Qed.

Definition buildD1 (b : bool) (s : bits) sz1 w1 n1 :=
  darr w1 (map (fun j => bcount b 0 (j * sz1) s) (rev (iota 0 n1.+1))).

Definition buildD2 (b : bool) (s : bits) k sz2 w2 n2 :=
  let sz1 := k * sz2 in
  darr w2 (map (fun j => bcount b (j %/ k * sz1) (j %% k * sz2) s) (rev (iota 0 n2.+1))).

Lemma BuildDirVal b s k sz2 w1 w2 :
  0 < k ->
  0 < sz2 ->
  let sz1 := k * sz2 in
  let n := bsize s in
  let n2 := n %/ sz2 in
  let n1 := n2 %/ k in
  buildDir b s k sz2 w1 w2 =
  (buildD1 b s sz1 w1 n1, buildD2 b s k sz2 w2 n2).
Proof.
  move=> Hk Hsz2 sz1 n n2 n1.
  rewrite /buildDir BuildDir1Val; last by [].
  rewrite BuildDir2Val -/n add0n add0n.
  rewrite /catDs /emptyD /pushD -/n2 -/n1 -/sz1.
  congr (_, _).
    by rewrite /buildD1 map_rev -addn1 iota_add add0n map_cat rev_cat.
  rewrite /buildD2.
  congr (darr w2 _).
  rewrite map_rev -addn1 iota_add add0n map_cat rev_cat /= -/n1.
  congr (_ :: _).
  rewrite -catrev_catl /rev.
  congr (catrev _ _).
  rewrite {2}(divn_eq n2 k) -/n1 iota_add map_cat.
  congr (_ ++ _).
  rewrite add0n -[n1 * k]addn0 iota_addl -map_comp.
  apply eq_in_map => j.
  rewrite mem_iota add0n => /andP [_ Hj].
  rewrite add0n /=.
  have Hj' : j < k.
    by apply (@ltn_trans (n2 %% k)); last apply ltn_pmod.
  rewrite divnMDl; last by [].
  rewrite divn_small; last by [].
  rewrite addn0.
  congr bcount.
  by rewrite modnMDl modn_small.
Qed.

Lemma sizeD_buildD1 b s sz1 w1 m : sizeD (buildD1 b s sz1 w1 m) = m.+1.
Proof. by rewrite /sizeD /buildD1 size_map size_rev size_iota. Qed.

Lemma sizeD_buildD2 b s k sz2 w2 m : sizeD (buildD2 b s k sz2 w2 m) = m.+1.
Proof. by rewrite /sizeD /buildD2 size_map size_rev size_iota. Qed.

Lemma lookupD_buildD1 b s sz1 w1 n1 i : i <= n1 ->
  lookupD (buildD1 b s sz1 w1 n1) i = (bcount b 0 (i * sz1) s).
Proof.
  move=> Hi.
  rewrite /lookupD /buildD1 map_rev nth_rev; last first.
    by rewrite size_rev size_map size_iota subSS -subSn; first apply leq_subr.
  rewrite size_map size_rev size_iota size_map size_iota.
  rewrite subnS subKn; last by rewrite ltnS.
  rewrite (nth_map 0); last by rewrite size_iota.
  by rewrite nth_iota; first rewrite add0n succnK.
Qed.

Lemma lookupD_buildD2 b s k sz2 w2 n2 i : i <= n2 ->
  lookupD (buildD2 b s k sz2 w2 n2) i = (bcount b (i %/ k * k * sz2) (i %% k * sz2) s).
Proof.
  move=> Hi.
  rewrite /lookupD /buildD2 map_rev nth_rev; last first.
    by rewrite size_rev size_map size_iota subSS -subSn; first apply leq_subr.
  rewrite size_map size_iota size_rev size_map size_iota.
  rewrite subnS subKn; last by rewrite ltnS.
  rewrite (nth_map 0); last by rewrite size_iota.
  by rewrite nth_iota; first rewrite succnK add0n mulnA.
Qed.

Lemma RankCorrect b s i : i <= bsize s -> rank_lookup (rank_init b s) i = rank b i s.
Proof.
  move=> Hi.
  rewrite /rank_lookup /rank_init BuildDirVal; last first.
      by [].
    by [].
  rewrite /dir1 /dir2 /blksz2 /ratio /query_bit /input_bits.
  rewrite lookupD_buildD1; last by do 2 apply leq_div2r.
  rewrite lookupD_buildD2; last by apply leq_div2r.
  rewrite bcount_adjacent2; last by rewrite mulnA.
  rewrite bcount_adjacent2; last by rewrite mulnA -mulnDl -divn_eq.
  by rewrite mulnA -mulnDl -divn_eq -divn_eq /bcount /rank drop0.
Qed.
