From mathcomp Require Import ssreflect ssrbool eqtype ssrfun ssrnat seq.
Require Import monadification.monadification.

Module Type Monad.
Parameter M : Type -> Type.
Parameter ret : forall {A : Type}, A -> M A.
Parameter bind : forall {A B : Type}, M A -> (A -> M B) -> M B.
Parameter S' : nat -> M nat.
Parameter consM : forall {A : Type}, A -> list A -> M (list A).
End Monad.

Module MonadicSeq (Mo : Monad).

Include Mo.

Arguments ret [A].
Arguments bind [A B].
Arguments consM [A].

Monadify Type M.
Monadify Return @ret.
Monadify Bind @bind.

Notation "'return' t" := (ret t) (at level 100).
Notation "x >>= y" := (bind x y) (at level 65, left associativity).

Monadify Action S => S'.
Monadify Action cons => @consM.

Set Monadification Verbose. (* show the original definition and the monadified definition *)

Monadification cat.
Monadification map.
Monadification iter.
Monadification ncons.
Monadify Pure seqn. (* dependent type: seqn_type *)
Monadification iota.
Monadification mkseq.
Monadification head. (* head is pure *)
Monadification size.

(*
  Disable monadification of nat_eqType and seq_eqType.
  Monadification of them is not possible because
  thier definition uses Equality.type which contains
  a equality function: T -> T -> bool.
  Corresponding monadic equality function: T -> T -> M bool is
  required to monadify them but it means we can not use Equality.type and
  lemmas related to Equality.type.
*)

(* Monadify Pure nat_eqType seq_eqType. *)
Monadify Pure Datatypes_nat__canonical__eqtype_Equality Datatypes_list__canonical__eqtype_Equality.


Monadification nilp.
Monadification ohead.
Monadification behead.
Monadification last.
Monadification belast.

Monadification size.
Monadification shape.
Monadification nth.
Monadification set_nth.
Monadification incr_nth.
Monadification nilp.

Monadification find.
Monadify Pure index. (* pred1 returns SimplPred which contains a function *)
Monadification has.
Monadification all.
Monadification count. (* addn, addn_rec, Nat.add *)
Monadify Pure constant. (* pred1 *)
Monadify Pure uniq. (* in_mem, mem *)
Monadification eqseq.
Monadification andb.

Monadification subseq.
Monadify Pure perm_eq. (* pred1 *)
Monadification filter.
Monadification rem.
Monadify Pure undup. (* in_mem, mem *)
Monadification mask.
Monadification cat.
Monadification take.
Monadification drop.
Monadification rot.
Monadification rotr.
Monadification rev.
Monadification catrev.
Monadification map.
Monadification foldr.
Monadification allpairs.
Monadification pmap.
Monadification sumn.
Monadification foldl.
Monadification scanl.
Monadification pairmap.
Monadification zip.
Monadification unzip1.
Monadification unzip2.
Monadification flatten.
Monadification reshape.

End MonadicSeq.

Module IdMonad <: Monad.
Definition M (A : Type) := A.
Definition ret {A : Type} (a : A) := a.
Definition bind {A B : Type} (a : A) (f : A -> B) := f a.
Definition S' := S.
Definition consM := @cons.
End IdMonad.

Module IdMonadSeq := MonadicSeq IdMonad.

Goal @IdMonadSeq.addM = @Nat.add. Proof. reflexivity. Qed.
Goal @IdMonadSeq.addnM = @addn. Proof. reflexivity. Qed.
Goal @IdMonadSeq.addn_recM = @addn_rec. Proof. reflexivity. Qed.
Goal @IdMonadSeq.allM = @all. Proof. reflexivity. Qed.
Goal @IdMonadSeq.allpairsM = @allpairs. Proof. reflexivity. Qed.
Goal @IdMonadSeq.belastM = @belast. Proof. reflexivity. Qed.
Goal @IdMonadSeq.catM = @cat. Proof. reflexivity. Qed.
Goal @IdMonadSeq.catrevM = @catrev. Proof. reflexivity. Qed.
Goal @IdMonadSeq.countM = @count. Proof. reflexivity. Qed.
Goal @IdMonadSeq.filterM = @filter. Proof. reflexivity. Qed.
Goal @IdMonadSeq.findM = @find. Proof. reflexivity. Qed.
Goal @IdMonadSeq.flattenM = @flatten. Proof. reflexivity. Qed.
Goal @IdMonadSeq.foldlM = @foldl. Proof. reflexivity. Qed.
Goal @IdMonadSeq.foldrM = @foldr. Proof. reflexivity. Qed.
Goal @IdMonadSeq.hasM = @has. Proof. reflexivity. Qed.
Goal @IdMonadSeq.incr_nthM = @incr_nth. Proof. reflexivity. Qed.
Goal @IdMonadSeq.iotaM = @iota. Proof. reflexivity. Qed.
Goal @IdMonadSeq.iterM = @iter. Proof. reflexivity. Qed.
Goal @IdMonadSeq.mapM = @map. Proof. reflexivity. Qed.
Goal @IdMonadSeq.maskM = @mask. Proof. reflexivity. Qed.
Goal @IdMonadSeq.mkseqM = @mkseq. Proof. reflexivity. Qed.
Goal @IdMonadSeq.nat_of_boolM = @nat_of_bool. Proof. reflexivity. Qed.
Goal @IdMonadSeq.nconsM = @ncons. Proof. reflexivity. Qed.
Goal @IdMonadSeq.nilpM = @nilp. Proof. reflexivity. Qed.
Goal @IdMonadSeq.pairmapM = @pairmap. Proof. reflexivity. Qed.
Goal @IdMonadSeq.pmapM = @pmap. Proof. reflexivity. Qed.
Goal @IdMonadSeq.remM = @rem. Proof. reflexivity. Qed.
Goal @IdMonadSeq.reshapeM = @reshape. Proof. reflexivity. Qed.
Goal @IdMonadSeq.revM = @rev. Proof. reflexivity. Qed.
Goal @IdMonadSeq.rotM = @rot. Proof. reflexivity. Qed.
Goal @IdMonadSeq.rotrM = @rotr. Proof. reflexivity. Qed.
Goal @IdMonadSeq.scanlM = @scanl. Proof. reflexivity. Qed.
Goal @IdMonadSeq.set_nthM = @set_nth. Proof. reflexivity. Qed.
Goal @IdMonadSeq.shapeM = @shape. Proof. reflexivity. Qed.
Goal @IdMonadSeq.sizeM = @size. Proof. reflexivity. Qed.
Goal @IdMonadSeq.sumnM = @sumn. Proof. reflexivity. Qed.
Goal @IdMonadSeq.takeM = @take. Proof. reflexivity. Qed.
Goal @IdMonadSeq.unzip1M = @unzip1. Proof. reflexivity. Qed.
Goal @IdMonadSeq.unzip2M = @unzip2. Proof. reflexivity. Qed.
Goal @IdMonadSeq.zipM = @zip. Proof. reflexivity. Qed.

Module OptionMonad <: Monad.
Definition M (A : Type) := option A.
Definition ret {A} (x : A) := Some x.
Definition bind {A} {B} (x' : option A) (f : A -> option B) :=
  match x' with
  | None => None
  | Some x => f x
  end.
Definition S' a := Some (S a).
Definition consM {T} (a : T) (s : list T) := Some (cons a s).
End OptionMonad.

Module OptionMonadSeq := MonadicSeq OptionMonad.
