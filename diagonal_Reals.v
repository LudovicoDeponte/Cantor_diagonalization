From Cantor.utils Require Import Utilities.

(* TODO:   a) define set of digits with successor S function.
        b) define an addOne function that perform S on the n-th digit of the 
            sequence
        c) show that the thus obtained g' is not in the enumeration *)


(* Below does not work *)
Require Import Reals.
Theorem Cantor_Reals:
  Sur nat R -> False.
Proof.
    intros surj.
    destruct surj as (f' & surj_f').
    pose (g' := fun n => addOne (f' n)). (* Construction of g' *)
        (* PROBLEM HERE!: how do I build g' from R? *)