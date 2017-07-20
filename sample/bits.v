From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From mathcomp Require Import div prime.

Require Import Monadification.sample.listutils.
Require Import Monadification.sample.natutils.

Section Bits.

Inductive bits : Type := bseq of seq bool.

Definition seq_of_bits s := match s with bseq l => l end.
Coercion seq_of_bits : bits >-> list.

Definition bnil := bseq nil.
Definition bcons b (s : bits) := bseq (b :: s).
Definition bsize (s : bits) := size s.
Definition bnth (s : bits) i := nth false s i.
Definition bappend (s1 s2 : bits) := bseq (s1 ++ s2).
Definition bcount (b : bool) n m (s : bits) := count_mem b (take m (drop n s)).

Lemma seq_of_bits_of_seq s : seq_of_bits (bseq s) = s.
Proof. by []. Qed.

Lemma bits_of_seq_of_bits s : bseq (seq_of_bits s) = s.
Proof. by case s. Qed.

Lemma bcount_empty b m bs : bcount b m 0 bs = 0.
Proof. by rewrite /bcount take0. Qed.

Lemma bcount_single b m (bs : bits) : m < size bs -> bcount b m 1 bs = (b == bnth bs m).
Proof.
  move=> Hn.
  rewrite /bcount (take_nth false); last by rewrite size_drop -(subnn m) ltn_sub2r.
  by rewrite take0 nth_drop addn0 /= addn0 eq_sym.
Qed.

Lemma bcount_max (b:bool) (m n:nat) (bs:bits) : bcount b m n bs <= n.
Proof.
  rewrite /bcount.
  apply: (leq_trans (count_size _ _)).
  rewrite size_take.
  case: ifP => [|/negbT]; first by [].
  by rewrite -leqNgt.
Qed.

Lemma bcount_adjacent (b:bool) (m n1 n2:nat) (bs:bits) :
  bcount b m n1 bs + bcount b (m+n1) n2 bs = bcount b m (n1+n2) bs.
Proof.
  rewrite /bcount -count_cat.
  congr (_ _).
  rewrite addnC -drop_drop.
  move: (drop m bs) => bs'.
  rewrite -drop_take_inv -(take_take _ _ (n1 + n2)).
    by rewrite cat_take_drop.
  by apply leq_addr.
Qed.

Lemma bcount_adjacent2 (b:bool) (m n1 m2 n2:nat) (bs:bits) :
  m2 = m + n1 ->
  bcount b m n1 bs + bcount b m2 n2 bs = bcount b m (n1+n2) bs.
Proof.
  move=> ->.
  by rewrite bcount_adjacent.
Qed.

End Bits.
