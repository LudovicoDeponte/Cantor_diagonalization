From Cantor.utils Require Import Utilities.
(* THE POWER SET OF NATURAL NUMBERS IS UNCOUNTABLE *)

(* 
We formalize the power set of nats as the set of functions from nats to bool,
as each function defines a subset of nats. 
*)

Theorem Cantor_PowerNat:
  Sur nat (nat->bool) -> False.
Proof.
  intros surj.
  destruct surj as (f' & surj_f').
  pose (g' := fun n => negb (f' n n)). (* Construction of g' *)
  assert (forall (n : nat), g' = f' n -> False).  (* Assertion 1*)
  - intros.
    assert (f' n n = g' n -> False).              (* Assertion 2 *)
    + intro.
      unfold g' in H0.
      eapply Contradiction_bool.
      exact H0.
    + apply H0.
      rewrite H.
      reflexivity.
  - pose proof (surj_f' g'). (* Assume by contradiction that g' is in the enum*)
    destruct H0.
    eapply H.
    rewrite H0.
    reflexivity.
Qed.
