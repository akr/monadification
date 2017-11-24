From mathcomp Require Import ssreflect ssrbool eqtype ssrfun ssrnat.
Require Import monadification.sample.natutils.

Require Import monadification.monadification.

Fixpoint pow a k :=
  match k with
  | 0 => 1
  | k'.+1 => a * pow a k'
  end.

Lemma pow_expn a k : pow a k = expn a k.
Proof.
  elim: k; first by [].
  move=> k IH /=.
  by rewrite expnS IH.
Qed.

Definition uphalf' n := n - n./2.

Lemma uphalf'_uphalf n : uphalf' n = uphalf n.
Proof.
  rewrite /uphalf' -{1}[n]odd_double_half.
  by rewrite -addnn addnA addnK uphalf_half.
Qed.

(* (uphalf' k') is used instead of (k./2) for decreasing argument detection *)
Fixpoint fastpow_iter a k x :=
  if k is k'.+1 then
    if odd k then
      fastpow_iter a k' (a * x)
    else
      fastpow_iter (a * a) (uphalf' k') x
  else
    x.

Definition fastpow a k := fastpow_iter a k 1.

Require FunInd.

Functional Scheme fastpowiter_ind := Induction for fastpow_iter Sort Prop.

Lemma fastpowiter_expn a k x : fastpow_iter a k x = expn a k * x.
Proof.
  elim/fastpowiter_ind: a k x / _.
      move=> a k x _.
      by rewrite expn0 mul1n.
    move=> a k' x k -> /= /negbTE Hodd ->.
    by rewrite mulnA -expnSr.
  move=> a k' x k -> /= /negbFE Hodd ->.
  rewrite uphalf'_uphalf uphalf_half -{3}[k]odd_double_half.
  by rewrite Hodd 2!addSn 2!add0n -doubleS -mul2n expnM mulnn.
Qed.

Lemma fastpow_expn a k : fastpow a k = expn a k.
Proof. by rewrite /fastpow fastpowiter_expn muln1. Qed.

Lemma fastpow_pow a k : fastpow a k = pow a k.
Proof. by rewrite fastpow_expn pow_expn. Qed.

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

Definition W := 64.
Definition check x :=
  if log2 x < W then Some x else None.
Definition SM a := check a.+1.
Definition addM a b := check (a + b).
Definition mulM a b := check (a * b).

(* addn, muln and S may overflow *)
Monadify Action addn => addM.
Monadify Action muln => mulM.
Monadify Action S => SM.

(* Declare uphalf' pure to prserve decreasing argument.
  Since uphalf' n = n - n./2 which n./2 uses S,
  it is monadified without this declaration.
  Note that (uphalf' n) is expected to implemented as (((n)+1)>>1) in C.
  (n)+1 doesn't cause integer overflow because it is applied to k' which is k - 1.
  Actually, we can not check it with monad because defining the monadic action
  uphalfM causes the monadification failure.
  Coq cannot detect decreasing argument using uphalfM. *)
Monadify Pure uphalf'.

Monadification pow.
Print powM.

Monadification fastpow.
Print fastpowM.
Print fastpow_iterM.

Lemma fastpowiterSuccess a k x :
  log2 (a ^ k * x) < W -> ((a == 0) || (0 < x)) ->
  fastpow_iterM a k x =
  Some (fastpow_iter a k x).
Proof.
  elim/fastpowiter_ind: a k x / _.
      by [].
    move=> a k' x k -> /= /negbTE Hodd IH H Hax.
    rewrite Hodd /bind [mulM a a]/mulM /check /=.
    rewrite [mulM a x]/mulM /check.
    have -> : is_true (log2 (a * x) < W).
      clear IH.
      case: a Hax H => [|a /= Hx]; first by [].
      apply leq_trans; rewrite ltnS expnS; apply log2_le_mono.
      apply leq_mul; last by [].
      apply leq_pmulr.
      by rewrite expn_gt0 ltn0Sn.
    rewrite {}IH.
        by [].
      case: a Hax H => [_ _|a]; first by rewrite mul0n muln0.
      rewrite orFb => Hx.
      apply leq_trans; rewrite ltnS expnSr -mulnA.
      by apply log2_le_mono; apply leq_mul.
    case: a Hax H => [|a /= Hx]; first by [].
    by case: x Hx.
  move=> a k' x k -> /= /negbFE Hodd IH H Hax.
  rewrite Hodd /bind [mulM a a]/mulM /check /=.
  have -> : is_true (log2 (a * a) < W).
    clear IH.
    case: a Hax H => [|a /= Hax]; first by [].
    apply leq_trans; rewrite ltnS; apply log2_le_mono.
    rewrite -[a.+1 * a.+1]muln1; apply leq_mul; last by [].
    rewrite mulnn; apply leq_pexp2l; first by [].
    by rewrite ltnS; apply odd_gt0.
  rewrite {}IH.
      by [].
    move: H.
    apply leq_trans; rewrite ltnS uphalf'_uphalf; apply log2_le_mono.
    case: a Hax => [_|a].
      rewrite exp0n; last by [].
      rewrite mul0n exp0n; first by [].
      by rewrite uphalf_half /= Hodd.
    rewrite orFb => Hx.
    rewrite leq_pmul2r; last by [].
    rewrite mulnn -expnM.
    apply leq_pexp2l.
      by [].
    rewrite uphalf_half -{3}[k]odd_double_half.
    rewrite mulnDr 2!mul2n.
    by case: (odd k).
  by case: a Hax H.
Qed.

Lemma fastpowSuccess a k : log2 (a ^ k) < W -> fastpowM a k = Some (fastpow a k).
Proof.
  move=> H.
  rewrite /fastpowM /= fastpowiterSuccess.
      by [].
    by rewrite muln1.
  by apply orbT.
Qed.
