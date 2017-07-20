From mathcomp Require Import ssreflect ssrbool eqtype ssrfun ssrnat seq.
Require Import Monadification.monadification.

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

Definition nthM {T} (x0 : T) s n :=
  if n < size s then Some (nth x0 s n) else None.

Monadify Action nth => @nthM.

Compute nthM 100 (10::11::12::nil) 0. (* Some 10 *)
Compute nthM 100 (10::11::12::nil) 1. (* Some 11 *)
Compute nthM 100 (10::11::12::nil) 2. (* Some 12 *)
Compute nthM 100 (10::11::12::nil) 3. (* None *)
