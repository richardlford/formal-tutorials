(* This file shows some practical applications of coercions. *)

From Flocq Require Import Defs.
Print float.
Print Zaux.radix.
Require Import ZArith.
Require Export Reals.

Module MyRadix.
  Record radix := { radix_val :> Z ; radix_prop : Zle_bool 2 radix_val = true }.
  (* Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : x = x *)
  Definition radix2 := Build_radix 2 (eq_refl _).
  Check radix2.
  Check radix2:Z.
  Print Coercions.
  Definition radplustwo := (radix2+2)%Z.
  Compute radplustwo.
  Print Graph.
End MyRadix.

Coercion IZR : Z >-> R.
Coercion INR : nat >-> R.
Coercion Z_of_nat : nat >-> Z.
Print Graph.
