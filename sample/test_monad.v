From mathcomp Require Import ssreflect ssrbool eqtype ssrfun ssrnat seq.
Require Import monadification.monadification.

Module Type Monad.
Parameter M : Type -> Type.
Parameter ret : forall {A : Type}, A -> M A.
Parameter bind : forall {A B : Type}, M A -> (A -> M B) -> M B.
Parameter OM : M nat.
Parameter SM : nat -> M nat.
End Monad.

Module MonadicSeq (Mo : Monad).

Include Mo.

Arguments ret [A].
Arguments bind [A B].

Monadify Type M.
Monadify Return @ret.
Monadify Bind @bind.

Notation "'return' t" := (ret t) (at level 100).
Notation "x >>= y" := (bind x y) (at level 65, left associativity).

Monadify Action O => OM.
Monadify Action S => SM.

Set Monadification Verbose. (* show the original definition and the monadified definition *)

Monadification O.
Monadification S.

Definition funcS := S.
Monadification funcS.

Definition funcargs1 (x1 : nat) := O.
Monadification funcargs1.

Definition funcargs2 (x1 x2 : nat) := O.
Monadification funcargs2.

Definition funcargs3 (x1 x2 x3 : nat) := O.
Monadification funcargs3.

Definition letrel (x : nat) := let x' := O in x'.
Monadification letrel.

Definition appcstrm x := S x.
Monadification appcstrm.

Definition appcstrm2 x := S (S x).
Monadification appcstrm2.

Definition matchexprzero (x: nat) := match O with O => false | S _ => true end.
Monadification matchexprzero.

Definition matchbrzero (x: nat) := match x with O => O | S _ => O end.
Monadification matchbrzero.

Definition matchbrpuredown (x : bool) :=
  match x with
  | true => fun (x:nat) => O
  | false => let o := O in fun (x:nat) => o
  end.
Monadification matchbrpuredown.

Definition matchbrpuredownapp (x : bool) :=
  (match x with
  | true => fun (x:nat) => O
  | false => let o := O in fun (x:nat) => o
  end) O.
Monadification matchbrpuredownapp.

(* pass a two-arguments function for one-argument function argument *)
Definition mapfun2arg s := map (fun x y => x + y) s.
Monadification mapfun2arg.

(* funtion type for a parameter for inductive type *)
Monadification fst snd.
Definition applypair {T1 T2 T3} (p : (T1 -> T2) * (T1 -> T3)) (v : T1) :=
  (fst p v, snd p v).
Monadification applypair.

(* the body of fixpoint should be puredown to the approximated impure arity *)
Fixpoint recbodypuredown (n:nat) :=
  let x := fun (z:unit) => 1 in
  false.
Definition invoke_recbodypuredown n :=
  let x := recbodypuredown n in 0.
Monadification recbodypuredown.
Monadification invoke_recbodypuredown.

End MonadicSeq.

Module IdMonad <: Monad.
Definition M (A : Type) := A.
Definition ret {A : Type} (a : A) := a.
Definition bind {A B : Type} (a : A) (f : A -> B) := f a.
Definition OM := O.
Definition SM := S.
End IdMonad.

Module IdMonadSeq := MonadicSeq IdMonad.

Goal @IdMonadSeq.OM = O. Proof. reflexivity. Qed.
Goal @IdMonadSeq.SM = S. Proof. reflexivity. Qed.
Goal @IdMonadSeq.funcSM = IdMonadSeq.funcS. Proof. reflexivity. Qed.
Goal @IdMonadSeq.funcargs1M = @IdMonadSeq.funcargs1. Proof. reflexivity. Qed.
Goal @IdMonadSeq.funcargs2M = @IdMonadSeq.funcargs2. Proof. reflexivity. Qed.
Goal @IdMonadSeq.funcargs3M = @IdMonadSeq.funcargs3. Proof. reflexivity. Qed.
Goal @IdMonadSeq.letrelM = @IdMonadSeq.letrel. Proof. reflexivity. Qed.
Goal @IdMonadSeq.appcstrmM = @IdMonadSeq.appcstrm. Proof. reflexivity. Qed.
Goal @IdMonadSeq.appcstrm2M = @IdMonadSeq.appcstrm2. Proof. reflexivity. Qed.
Goal @IdMonadSeq.matchexprzeroM = @IdMonadSeq.matchexprzero. Proof. reflexivity. Qed.
Goal @IdMonadSeq.matchbrzeroM = @IdMonadSeq.matchbrzero. Proof. reflexivity. Qed.
Goal @IdMonadSeq.matchbrpuredownM = @IdMonadSeq.matchbrpuredown. Proof. reflexivity. Qed.
Goal @IdMonadSeq.matchbrpuredownappM = @IdMonadSeq.matchbrpuredownapp. Proof. reflexivity. Qed.
Goal @IdMonadSeq.mapfun2argM = @IdMonadSeq.mapfun2arg. Proof. reflexivity. Qed.
Goal @IdMonadSeq.applypairM = @IdMonadSeq.applypair. Proof. reflexivity. Qed.
