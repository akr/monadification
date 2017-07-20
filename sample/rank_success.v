(* rank never fail *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq ssrfun.
From mathcomp Require Import div prime.
Require Import Monadification.monadification.

Require Import Monadification.sample.listutils.
Require Import Monadification.sample.natutils.
Require Import Monadification.sample.bits.

Require Import Monadification.sample.rank.

Definition ret {A} (x : A) := Some x.
Definition bind {A} {B} (x' : option A) (f : A -> option B) :=
  match x' with
  | None => None
  | Some x => f x
  end.

Set Monadification Verbose. (* show the original definition and the monadified definition *)

Monadify Type option.
Monadify Return @ret.
Monadify Bind @bind.

Notation "'return' t" := (ret t) (at level 100).
Notation "x >>= y" := (bind x y) (at level 65, left associativity).

Definition W := 64.
Definition check x := if log2 x < W then Some x else None.

(* integer overflow *)
Definition SM a := check a.+1.
Definition addM a b := check (a + b).
Definition mulM a b := check (a * b).
Monadify Action addn => addM.
Monadify Action muln => mulM.
Monadify Action S => SM.

(* negative integer overflow *)
Definition subM a b := if a < b then None
  else Some (a - b).
Monadify Action subn => subM.

(* division by zero *)
Definition divM a b := if b is 0 then None
  else Some (a %/ b).
Definition modM a b := if b is 0 then None
  else Some (a %% b).
Monadify Action divn => divM.
Monadify Action modn => modM.

(* buffer overrun, integer overflow *)
Definition bcountM (b : bool) n m (s : bits) :=
  if n + m <= bsize s then check (bcount b n m s)
  else None.
Monadify Action bcount => bcountM.

(* implementation limitation *)
Definition emptyDM w := if w is 0 then None
  else Some (emptyD w).
Monadify Action emptyD => emptyDM.

(* directory element integer overflow *)
Definition pushDM D v := let: darr w d := D in
  if v < 2 ^ w then Some (pushD D v) else None.
Monadify Action pushD => pushDM.

(* buffer overrun *)
Definition lookupDM D i :=
  if i < sizeD D then check (lookupD D i) else None.
Monadify Action lookupD => lookupDM.

Monadify Pure bitlen.

Monadification rank_init.
Monadification rank_lookup.

Print rank_initM.
Print buildDirM.
Print buildDir1M.
Print buildDir2M.
Print rank_lookupM.

Definition sample_bits := bseq (true::false::true::true::nil).
Compute rank_init true sample_bits.
Compute rank_lookup (rank_init true sample_bits) 3.
Compute rank_initM true sample_bits >>= fun aux => rank_lookupM aux 3.

Lemma check_trans n : log2 n < W -> forall x, x <= n -> check x = Some x.
Proof.
  move=> HW x Hxn.
  rewrite /check.
  rewrite (_ : log2 x < W); first by [].
  apply (@leq_ltn_trans (log2 n)); last by [].
  by apply log2_le_mono.
Qed.

Lemma bound_bitlen_n w n : n < 2 ^ w -> bitlen n < 2 ^ w.
Proof.
  move=> H.
  apply leq_trans with (n:=w.+1).
    by rewrite -addn1 -[w.+1]addn1 leq_add2r leq_bitlen_l.
  by apply ltn_expl.
Qed.

Lemma bound_S_bitlen_n w n : 1 < w -> n < 2 ^ w -> (bitlen n).+1 < 2 ^ w.
Proof.
  move=> Hw Hn.
  apply leq_trans with (n:=w.+2).
    by rewrite 2!ltnS leq_bitlen_l.
  rewrite -[w.+1]addn1.
  by apply ltnDexp with (q:=2).
Qed.

Lemma bound_bitlen_n_S_bitlen_n w n : 4 < w -> n < 2 ^ w -> bitlen n * (bitlen n).+1 < 2 ^ w.
  move=> Hw Hn.
  apply leq_ltn_trans with (n:=w * w.+1).
    apply leq_mul.
      by rewrite leq_bitlen_l.
    by rewrite ltnS leq_bitlen_l.
  rewrite (_:w=(5+(w-5))); last by rewrite subnKC // Hw.
  case: (w - 5) => // i; rewrite -addSnnS.
  case: i => // i; rewrite -addSnnS.
  case: i => // i; rewrite -addSnnS.
  apply leq_trans with (n:=(8+i).+1 * (8+i).+1).
    by rewrite ltn_mul2r ltn0Sn leqnn.
  apply leq_trans with (n:=2 ^ (4+i./2) * 2 ^ (4+i./2)); last first.
    rewrite -expnD leq_exp2l; last by [].
    rewrite {1}addnC addnA -[_ + 4 + 4]addnA /= [_ + 8]addnC -addnA.
    apply leq_add; first by [].
    rewrite addnn.
    apply leq_trans with (odd i + i./2.*2).
      by rewrite addnC leq_addr.
    by rewrite odd_double_half.
  rewrite 2!mulnn leq_sqr.
  apply leq_ltn_trans with (n:=9 + i./2.*2).
    rewrite [9 + _]addSnnS leq_add2l -add1n.
    rewrite -{1}(odd_double_half i) leq_add2r.
    by case: (odd i).
  rewrite -addSn.
  rewrite (_:(10 + (i./2).*2)=((4 + i./2).*2+2)); last first.
    by rewrite 2!addnS addn0.
  rewrite -mul2n.
  by apply leq_MDexp with (n0:=4).
Qed.

Lemma bound_square_S_bitlen_n w n : 5 < w -> n < 2 ^ w -> (bitlen n).+1 * (bitlen n).+1 < 2 ^ w.
Proof.
  move=> Hw Hn.
  apply leq_ltn_trans with (n:=w.+1 * w.+1).
    apply leq_mul; by rewrite ltnS leq_bitlen_l.
  rewrite (_:w=(6+(w-6))); last by rewrite subnKC.
  remember (w - 6) as i.
  clear Heqi Hw Hn n.
  rewrite -addSn.
  apply leq_trans with (n := (8 + i) * (8 + i)).
    by rewrite [8 + i]addSn mulSnr [(7 + i) * (7 + i).+1]mulnSr addnS ltnS -addnA leq_addr.
  case: i => // i; rewrite -2!addSnnS.
  case: i => // i; rewrite -2!addSnnS.
  apply leq_trans with (n:=2 ^ (4+i./2) * 2 ^ (4+i./2)); last first.
    rewrite -expnD leq_exp2l; last by [].
    rewrite {1}addnC addnA -[_ + 4 + 4]addnA /= [_ + 8]addnC -addnA.
    apply leq_add; first by [].
    rewrite addnn.
    apply leq_trans with (odd i + i./2.*2).
      by rewrite addnC leq_addr.
    by rewrite odd_double_half.
  rewrite 2!mulnn leq_sqr.
  apply leq_trans with (n:=11 + i./2.*2).
    rewrite [11 + _]addSnnS leq_add2l -add1n.
    rewrite -{1}(odd_double_half i) leq_add2r.
    by case: (odd i).
  rewrite (_:(11 + (i./2).*2)=((4 + i./2).*2+3)); last first.
    by rewrite 3!addnS addn0.
  rewrite -mul2n.
  by apply leq_MDexp with (n0:=4).
Qed.

Lemma ltn_neq0 m n : 1 < n -> m < n -> neq0 m < n.
Proof.
  rewrite /neq0.
  case: m.
    by rewrite /=.
  move=> m.
  by rewrite succnK.
Qed.

Lemma leq_neq0 m n : 0 < n -> m <= n -> neq0 m <= n.
Proof.
  rewrite /neq0.
  case: m.
    by rewrite /=.
  move=> m.
  by rewrite succnK.
Qed.

Lemma BuildDir2Success (b : bool) (s : bits) kp sz2 c ii D2 m2 :
  let k := kp.+1 in
  log2 k < W ->
  log2 sz2 < W ->
  0 < sz2 ->
  let sz1 := k * sz2 in
  neq0 (bitlen (kp * sz2)) <= bwidth D2 <= W ->
  let n := bsize s in
  log2 n < W ->
  c <= k ->
  let i := ii * sz2 in
  i + c * sz2 <= n ->
  m2 <= i ->
  m2 + c * sz2 <= sz1 ->
  buildDir2M b s sz2 c i D2 m2 = Some (buildDir2 b s sz2 c i D2 m2).
Proof.
  move=> k Hk Hsz2 Hsz2nz sz1 Hw2 n Hn Hck i.
  rewrite {}/i => Hic Hm2i Hm2z.
  case: D2 Hw2 => w2 d2.
  rewrite [bwidth _]/bwidth => Hw2'.
  have Hw2 : kp * sz2 < 2 ^ w2.
    rewrite -leq_bitlen_l.
    move: Hw2' => /andP [] Hw2 _.
    apply (@leq_trans (neq0 (bitlen (kp * sz2)))).
      rewrite /neq0.
      by apply leqSpred.
    by apply Hw2.
  elim: c ii m2 d2 Hck Hic Hm2i Hm2z.
    by [].
  move=> cp IH ii m2 d2 Hck Hic Hm2i Hm2z.
  rewrite /= /bind.
  rewrite {1}/bcountM -/n.
  rewrite (_ : ii * sz2 + sz2 <= n); last first.
    apply (@leq_trans (ii * sz2 + cp.+1 * sz2)); last by [].
    by rewrite mulSn addnA leq_addr.
  rewrite (check_trans sz2 Hsz2); last first.
    by apply bcount_max.
  rewrite {1}/addM (check_trans n Hn); last first.
    apply (@leq_trans ((ii * sz2) + cp.+1 * sz2)); last by [].
    by rewrite mulSn addnA leq_addr.
  rewrite (_ : m2 < 2 ^ w2); last first.
    apply (@leq_ltn_trans (kp * sz2)); last by [].
    rewrite /sz1 mulSnr addnA /k mulSnr leq_add2r in Hm2z.
    apply (@leq_trans (m2 + cp * sz2)); last by [].
    by apply leq_addr.
  rewrite {1}/addM (check_trans n Hn); last first.
    apply (@leq_trans ((ii * sz2) + sz2)).
      by apply leq_add; last apply bcount_max.
    apply (@leq_trans ((ii * sz2) + cp.+1 * sz2)); last by [].
    by rewrite mulSn addnA leq_addr.
  rewrite -mulSnr {}IH.
          by [].
        by apply ltnW.
      by rewrite -mulnDl addSnnS mulnDl.
    rewrite mulSnr.
    by apply leq_add; last apply bcount_max.
  apply (@leq_trans (m2 + cp.+1 * sz2)); last by [].
  by rewrite mulSn addnA leq_add2r leq_add2l bcount_max.
Qed.

Lemma BuildDir1Success (b : bool) (s : bits) k sz2 c ii D1 D2 m1 :
  log2 k < W ->
  0 < k ->
  let kp := k.-1 in
  log2 sz2 < W ->
  0 < sz2 ->
  let sz1 := k * sz2 in
  let n := bsize s in
  let n2 := n %/ sz2 in (* number of small blocks *)
  let n1 := n2 %/ k in (* number of large blocks *)
  neq0 (bitlen (n %/ sz1 * sz1)) <= bwidth D1 <= W ->
  neq0 (bitlen (kp * sz2)) <= bwidth D2 <= W ->
  log2 n < W ->
  c <= n1 ->
  let i := ii * sz1 in
  i + c * sz1 <= n ->
  m1 <= i ->
  m1 + c * sz1 <= n ->
  buildDir1M b s k sz1 sz2 c i D1 D2 m1 = Some (buildDir1 b s k sz1 sz2 c i D1 D2 m1).
Proof.
  move=> Hk Hknz kp Hsz2 Hsz2nz sz1 n n2 n1 Hw1 Hw2 Hn Hc i.
  rewrite {}/i => Hic Hm1i Hm1z.
  case: D1 Hw1 => w1 d1.
  rewrite [bwidth _]/bwidth => Hw1'.
  have Hw1 : n %/ sz1 * sz1 < 2 ^ w1.
    rewrite -leq_bitlen_l.
    move: Hw1' => /andP [] Hw1 _.
    apply (@leq_trans (neq0 (bitlen (n %/ sz1 * sz1)))).
      rewrite /neq0.
      by apply leqSpred.
    by apply Hw1.
  case: D2 Hw2 => w2 d2 Hw2.
  have Hsz1nz: 0 < sz1.
    rewrite /sz1.
    clear Hk sz1 Hic Hm1i Hm1z Hw1 Hw1' Hw2 n1 Hc Hsz2 n2 kp.
    case: k Hknz; first by [].
    case: sz2 Hsz2nz; first by [].
    move=> x Hx y Hy.
    by rewrite mulSn addn_gt0 Hx orTb.
  elim: c ii m1 d1 d2 Hc Hic Hm1i Hm1z Hw2.
    by [].
  move=> cp IH ii m1 d1 d2 Hc Hic Hm1i Hm1z Hw2.
  rewrite /= /bind.
  rewrite (_ : m1 < 2 ^ w1); last first.
    apply (@leq_ltn_trans (ii * sz1)); first by [].
    apply (@leq_ltn_trans (n %/ sz1 * sz1)); last by [].
    rewrite -(leq_add2r sz1).
    apply (@leq_trans n).
      apply (@leq_trans (ii * sz1 + cp.+1 * sz1)); last by [].
      by rewrite mulSn addnA leq_addr.
    rewrite {1}(divn_eq n sz1) leq_add2l.
    apply ltnW.
    apply ltn_pmod.
    by apply Hsz1nz.
  rewrite {1}/sz1 mulnA.
  rewrite (BuildDir2Success _ _ k.-1); last first.
                    by rewrite add0n prednK.
                  by [].
                rewrite -/n -mulnA -/sz1.
                apply (@leq_trans (ii * sz1 + cp.+1 * sz1)); last by []. (* ii * sz1 + sz1 <= n *)
                by rewrite leq_add2l mulSn leq_addr.
              by rewrite prednK.
            by rewrite -/n.
          by apply Hw2.
        by [].
      by [].
    by rewrite prednK.
  rewrite BuildDir2Val.
  rewrite {1}/addM (check_trans n Hn); last first.
    rewrite -mulnA -/sz1.
    apply (@leq_trans (ii * sz1 + cp.+1 * sz1)); last by []. (* ii * sz1 + sz1 <= n *)
    by rewrite leq_add2l mulSn leq_addr.
  rewrite add0n {1}/addM (check_trans n Hn); last first.
    rewrite -/sz1.
    apply (@leq_trans (m1 + cp.+1 * sz1)); last by [].
    apply leq_add; first by [].
    apply (@leq_trans sz1); first by apply bcount_max.
    by rewrite mulSn leq_addr.
  rewrite -mulnA -/sz1 -mulSnr {}IH.
            by [].
          by apply ltnW.
        by rewrite -mulnDl addSnnS mulnDl.
      rewrite mulSnr.
      apply leq_add; first by [].
      by apply bcount_max.
    apply (@leq_trans (m1 + cp.+1 * sz1)); last by [].
    by rewrite [cp.+1 * sz1]mulSn addnA leq_add2r leq_add2l bcount_max.
  by [].
Qed.

Lemma sizeSuccess (T : Type) (s : seq T) : log2 (size s) < W -> sizeM T s = Some (size s).
Proof.
  elim: s.
    by [].
  move=> a s IH /= Hsz.
  rewrite IH.
    rewrite /SM /bind.
    by rewrite (check_trans (size s).+1 Hsz).
  apply (@leq_ltn_trans (log2 (size s).+1)); last by [].
  by apply log2_le_mono.
Qed.

Lemma bsizeSuccess : forall (s : bits), log2 (bsize s) < W -> bsizeM s = Some (bsize s).
Proof.
  case=> s.
  move=> Hn.
  rewrite /bsizeM /bsize.
  rewrite seq_of_bits_of_seq.
  by apply sizeSuccess.
Qed.

Lemma BuildDirSuccess b s k sz2 w1 w2 :
  0 < k ->
  0 < sz2 ->
  let sz1 := k * sz2 in
  log2 sz1 < W ->
  let kp := k.-1 in
  let n := bsize s in
  log2 n < W ->
  neq0 (bitlen (n %/ sz1 * sz1)) <= w1 <= W ->
  neq0 (bitlen (kp * sz2)) <= w2 <= W ->
  buildDirM b s k sz2 w1 w2 = Some (buildDir b s k sz2 w1 w2).
Proof.
  move=> Hknz Hsz2nz sz1 Hsz1 kp n Hn Hw1 Hw2.
  have Hkpos : k = k.-1.+1.
    by rewrite prednK.
  have Hsz2pos : sz2 = sz2.-1.+1.
    by rewrite prednK.
  have Hk : log2 k < W.
    apply (@leq_ltn_trans (log2 sz1)); last by [].
    apply log2_le_mono.
    rewrite /sz1 Hkpos Hsz2pos.
    by rewrite mulnS leq_addr.
  have Hsz2 : log2 sz2 < W.
    apply (@leq_ltn_trans (log2 sz1)); last by [].
    apply log2_le_mono.
    rewrite /sz1 Hkpos Hsz2pos.
    by rewrite mulSn leq_addr.
  rewrite /buildDirM /bind.
  rewrite {1}/mulM (check_trans sz1 Hsz1); last by [].
  rewrite bsizeSuccess; last by [].
  rewrite -/n /divM {1}Hsz2pos {1}Hkpos.
  rewrite {1}/emptyDM.
  rewrite -{1}[w1]prednK; last first.
    apply (@leq_trans (neq0 (bitlen (n %/ sz1 * sz1)))).
      by rewrite /neq0 ltn0Sn.
    by move: Hw1 => /andP [] ->.
  rewrite {1}/emptyDM.
  rewrite -{1}[w2]prednK; last first.
    apply (@leq_trans (neq0 (bitlen (kp * sz2)))).
      by rewrite /neq0 ltn0Sn.
    by move: Hw2 => /andP [] ->.
  rewrite -{1}[0](mul0n sz1).
  rewrite BuildDir1Success; last first.
                        by rewrite -/n add0n -divnMA [sz2 * k]mulnC -/sz1 leq_trunc_div.
                      by [].
                    by rewrite -/n mul0n add0n -divnMA [sz2 * k]mulnC -/sz1 leq_trunc_div.
                  by [].
                by [].
              by [].
            by [].
          by [].
        by [].
      by [].
    by [].
  rewrite BuildDir1Val; last by [].
  rewrite {1}/modM {1}Hkpos.
  rewrite {1}/mulM (check_trans n Hn); last first.
    rewrite -divnMA [sz2 * k]mulnC -/sz1.
    by apply leq_trunc_div.
  rewrite mulnA (BuildDir2Success _ _ k.-1); last first.
                    rewrite add0n leq_mul2r -Hkpos.
                    apply/orP; right.
                    apply ltnW.
                    by apply ltn_pmod.
                  by [].
                by rewrite -/n -mulnDl -divn_eq leq_trunc_div.
              rewrite -Hkpos.
              apply ltnW.
              by apply ltn_pmod.
            by rewrite -/n.
          by [].
        by [].
      by [].
    by rewrite -Hkpos.
  rewrite BuildDir2Val.
  rewrite add0n mul0n -divnMA [sz2 * k]mulnC -[_ * k * sz2]mulnA -/sz1.
  rewrite {1}/pushDM {1}/catDs {1}/emptyD.
  rewrite (_ : bcount b 0 (n %/ sz1 * sz1) s < 2 ^ w1); last first.
    apply (@leq_ltn_trans (n %/ sz1 * sz1)); first by apply bcount_max.
    rewrite -leq_bitlen_l.
    move: Hw1 => /andP [] Hw1 _.
    apply (@leq_trans (neq0 (bitlen (n %/ sz1 * sz1)))).
      rewrite /neq0.
      by apply leqSpred.
    by apply Hw1.
  rewrite add0n.
  rewrite {1}/pushDM {1}/emptyD {1 2}/catDs.
  rewrite (_ : bcount b (n %/ sz1 * sz1) ((n %/ sz2) %% k * sz2) s < 2 ^ w2); last first.
    apply (@leq_ltn_trans ((n %/ sz2) %% k * sz2)); first by apply bcount_max.
    apply (@leq_ltn_trans (kp * sz2)).
      rewrite leq_mul2r -ltnS /kp -Hkpos ltn_pmod; last by [].
      by rewrite orbT.
    rewrite -leq_bitlen_l.
    move: Hw2 => /andP [] Hw2 _.
    apply (@leq_trans (neq0 (bitlen (kp * sz2)))).
      rewrite /neq0.
      by apply leqSpred.
    by apply Hw2.
  rewrite /ret.
  rewrite /catDs /emptyD /=.
  f_equal.
  rewrite BuildDirVal; last first.
      by [].
    by [].
  f_equal.
    rewrite /buildD1.
    f_equal.
    rewrite -/n -addn1 iota_add map_rev map_cat rev_cat /=.
    by rewrite add0n -divnMA [sz2 * k]mulnC -/sz1.
  rewrite /buildD2.
  f_equal.
  rewrite -/n -addn1 iota_add map_rev map_cat rev_cat /=.
  rewrite add0n -divnMA [sz2 * k]mulnC -/sz1.
  f_equal.
  rewrite /rev.
  rewrite -catrev_catl.
  f_equal.
  rewrite {2}[n %/ sz2](divn_eq (n %/ sz2) k).
  rewrite iota_add map_cat.
  rewrite -divnMA [sz2 * k]mulnC -/sz1.
  rewrite add0n.
  f_equal.
  rewrite -[n %/ sz1 * k]addn0 iota_addl -map_comp.
  apply eq_in_map => j.
  rewrite mem_iota add0n => /andP [_ Hj].
  rewrite add0n /=.
  rewrite divnMDl; last by [].
  rewrite modnMDl.
  have Hj' : j < k.
    apply (@leq_trans ((n %/ sz2) %% k)); first by [].
    apply ltnW.
    by apply ltn_pmod.
  rewrite [j %/ k]divn_small; last by [].
  rewrite [j %% k]modn_small; last by [].
  by rewrite addn0.
Qed.

Lemma RankInitSuccess b s :
  log2 (bsize s) < W -> rank_initM b s = Some (rank_init b s).
Proof.
  have @n := bsize s.
  rewrite -/n.
  move=> Hn.
  have Hn' : n < 2 ^ W.
    by apply ltn_log2_pow2.
  rewrite /rank_initM /bind.
  rewrite bsizeSuccess; last by [].
  have Hok1 : SM (bitlen (bsize s)) = Some (S (bitlen (bsize s))).
    rewrite /SM /check.
    rewrite (_ : log2 ((bitlen (bsize s)).+1) < W); first by [].
    apply ltn_pow2_log2'; first by [].
    move: Hn.
    rewrite -/n.
    move=> H.
    by apply bound_S_bitlen_n.
  rewrite Hok1.
  rewrite /divM.
  rewrite -/n.
  rewrite {1}/mulM /check.
  have Hok2 : log2 ((bitlen n).+1 * (bitlen n).+1) < W.
    apply ltn_pow2_log2'; first by [].
    by apply bound_square_S_bitlen_n.
  rewrite Hok2.
  rewrite mulSn addSn -addSn -mulSn.
  rewrite {1}/mulM /check.
  have Hok3 : log2 (n %/ ((bitlen n).+1 * (bitlen n).+1)
                       * ((bitlen n).+1 * (bitlen n).+1)) < W.
    apply ltn_pow2_log2'; first by [].
    apply (@leq_ltn_trans n); last by [].
    by apply leq_trunc_div.
  rewrite Hok3.
  rewrite {1}/neq0M {1}/SM /check.
  rewrite (_ : log2
      (bitlen
         (n %/ ((bitlen n).+1 * (bitlen n).+1) *
          ((bitlen n).+1 * (bitlen n).+1))).-1.+1 < W); last first.
    apply ltn_pow2_log2'; first by [].
    apply ltn_neq0; first by [].
    apply (@leq_ltn_trans (n %/ ((bitlen n).+1 * (bitlen n).+1) * ((bitlen n).+1 * (bitlen n).+1))).
      by apply bitlen_small.
    by apply ltn_log2_pow2.
  rewrite /mulM /check.
  have Hok4 : log2 (bitlen n * (bitlen n).+1) < W.
    apply ltn_pow2_log2'; first by [].
    by apply bound_bitlen_n_S_bitlen_n.
  rewrite Hok4.
  rewrite {1}/neq0M {1}/SM /check.
  rewrite (_ : log2 (bitlen (bitlen n * (bitlen n).+1)).-1.+1 < W); last first.
    apply ltn_pow2_log2'; first by [].
    apply ltn_neq0; first by [].
    apply (@leq_ltn_trans (bitlen n * (bitlen n).+1)).
      by apply bitlen_small.
    by apply ltn_log2_pow2.
  rewrite BuildDirSuccess.
              by [].
            by [].
          by [].
        apply ltn_pow2_log2'; first by [].
        by apply bound_square_S_bitlen_n.
      by [].
    rewrite -/n.
    rewrite leqnn andTb.
    apply leq_neq0; first by [].
    rewrite leq_bitlen_l.
    apply (@leq_ltn_trans n); last by [].
    by apply leq_trunc_div.
  rewrite succnK leqnn andTb.
  apply leq_neq0; first by [].
  rewrite leq_bitlen_l.
  by apply bound_bitlen_n_S_bitlen_n.
Qed.

Lemma RankSuccess b s i :
  let n := bsize s in
  log2 n < W -> i <= n ->
  (rank_initM b s >>= fun aux => rank_lookupM aux i) =
  Some (rank_lookup (rank_init b s) i).
Proof.
  move=> n Hn Hi.
  rewrite RankInitSuccess; last by [].
  rewrite /rank_lookupM /bind /rank_init BuildDirVal; last first.
      by [].
    by [].
  rewrite -/n.
  rewrite /query_bit /input_bits /ratio /blksz2 /dir1 /dir2.
  rewrite {1}/divM {1}/modM {1}/divM {1}/lookupDM.
  rewrite sizeD_buildD1.
  rewrite (_ : (i %/ (bitlen n).+1) %/ (bitlen n).+1 <
              ((n %/ (bitlen n).+1) %/ (bitlen n).+1).+1); last first.
    by rewrite ltnS -divnMA -divnMA leq_div2r.
  rewrite (check_trans n Hn); last first.
    rewrite lookupD_buildD1; last first.
      by rewrite -divnMA -divnMA leq_div2r.
    rewrite -divnMA.
    apply (@leq_trans (i %/ ((bitlen n).+1 * (bitlen n).+1)
                          * ((bitlen n).+1 * (bitlen n).+1))).
      by apply bcount_max.
    apply (@leq_trans i); last by [].
    by apply leq_trunc_div.
  rewrite {1}/lookupDM sizeD_buildD2.
  rewrite (_ : i %/ (bitlen n).+1 < (n %/ (bitlen n).+1).+1); last first.
    by rewrite ltnS leq_div2r.
  rewrite (check_trans n Hn) lookupD_buildD2; last first.
        by apply leq_div2r.
      apply (@leq_trans ((i %/ (bitlen n).+1) %% (bitlen n).+1 * (bitlen n).+1)).
        by apply bcount_max.
      apply (@leq_trans i); last by [].
      apply (@leq_trans ((i %/ (bitlen n).+1) * (bitlen n).+1)).
        rewrite leq_pmul2r; last by [].
        by apply leq_mod.
      by apply leq_trunc_div.
    by apply leq_div2r.
  rewrite lookupD_buildD1; last first.
    by do 2 apply leq_div2r.
  rewrite {1}/addM mulnA bcount_adjacent (check_trans n Hn); last first.
    apply (@leq_trans
        (((i %/ (bitlen n).+1) %/ (bitlen n).+1 * (bitlen n).+1 * (bitlen n).+1 +
          (i %/ (bitlen n).+1) %% (bitlen n).+1 * (bitlen n).+1))).
      by apply bcount_max.
    rewrite -mulnDl -divn_eq.
    apply (@leq_trans i); last by [].
    by apply leq_trunc_div.
  rewrite {1}/mulM (check_trans n Hn); last first.
    apply (@leq_trans i); last by [].
    by apply leq_trunc_div.
  rewrite {1}/bcountM -/n -divn_eq Hi (check_trans n Hn); last first.
    apply (@leq_trans (i %% (bitlen n).+1)).
      by apply bcount_max.
    apply (@leq_trans i); last by [].
    by apply leq_mod.
  rewrite -mulnDl -divn_eq /addM (check_trans n Hn); last first.
    rewrite bcount_adjacent -divn_eq.
    apply (@leq_trans i); last by [].
    by apply bcount_max.
    rewrite bcount_adjacent -divn_eq.
  f_equal.
  rewrite /rank_lookup.
  rewrite /query_bit /input_bits /ratio /blksz2 /dir1 /dir2.
  rewrite lookupD_buildD1; last first.
    by do 2 apply leq_div2r.
  rewrite lookupD_buildD2; last first.
    by apply leq_div2r.
  rewrite -divnMA mulnA bcount_adjacent divnMA -mulnDl -divn_eq.
  by rewrite bcount_adjacent -divn_eq.
Qed.

