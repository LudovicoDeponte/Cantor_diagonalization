(* Surjective property *)
Record Sur { A B : Type } : Type :=
  { fSur_to      : A -> B
  ; surj_f       : forall (b : B), exists (a : A), b = fSur_to(a)
  }.
Arguments Sur : clear implicits.

(* Injective property *)
Definition injective {A B} (f : A -> B) := forall a1 a2, f a1 = f a2 -> a1 = a2.
(*
we use A B as general Types for any set, then we define a function
f_to, from A to B and we impose that it holds that surj_f, i.e.
f is surjective
*)

Require Import Bool.

Lemma Contradiction_bool (a : bool):
  a = negb a -> False.
Proof.
  (* intro.
  induction a. (* works also with destruct a *)
  + apply eq_true_false_abs with (b:= true).
    * reflexivity.
    * rewrite H.
      simpl.
      reflexivity.
  + apply eq_true_false_abs with (b:= negb false).
    * simpl.
      reflexivity.
    * rewrite <- H.
      reflexivity.

Restart. *)
  induction a; intro; eapply eq_true_false_abs; easy.
Qed.