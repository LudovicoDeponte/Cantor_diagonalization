From Cantor.utils Require Import Utilities.

Theorem Cantor_PowerNat:
  Sur nat (nat->bool) -> False.
Proof.
  intros; destruct H as (f' & surj_f').
  pose (g' := fun n => negb (f' n n)).
  assert (forall (n : nat), g' = f' n -> False).
  - intros.
    assert (f' n n = g' n -> False).
    + intro.
      unfold g' in H0.
      now apply Contradiction_bool with (a:= f' n n).
    + now apply H0; rewrite H.
  - pose proof (surj_f' g').
    destruct H0.
    now apply H with (n := x).
Qed.