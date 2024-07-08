From Cantor.utils Require Import Utilities.

(* THE SET OF SEQUENCES OF NATURAL NUMBERS IS UNCOUNTABLE *)

(*
Cantor's proof states that there is no surjective function from natural numbers
to sequences of natural numbers (nat).
We model sequences of naturals using type (nat -> nat). Intuitively, a sequence of
nats is completely defined by a function f that takes a nat i and returns the ith
nat in the sequence. Hence, there is bijection between the set of infinite
sequences of nat and the set of functions from nat to nat.


Cantor's result is proved by contradiction: we assume that there is a surjective
function f' that maps nats into sequences of nats, and we show that this leads
to contradiction.

NOTATION: we use f' as in other proofs by diagonalization it is sometimes assumed
that the function from A to B is bijective, hance having an inverse.
Thus we use the following notation:
    f   : B -> A                     (nat -> nat) -> nat
    f'  : A -> B                     nat -> (nat -> nat)
    g   : nat -> nat                 is one sequence of nats
    g^n : nat -> nat                 the n-th sequence of nats given by f'(n)
    g'  : nat -> nat                 the new sequence of nats
*)

Theorem Cantor_NatSeq:
  Sur nat (nat->nat) -> False.
Proof.
  intros surj.                  (* We suppose that there is a surjective f'*)
  destruct surj as (f' & surj_f').
  (*  now we want to perform the diagonalization.
      To do this, we have to define a new sequence of nats that does not appear
      in the enumeration induced by f'.
      So we define g', a new sequence. g' (n+1)th element is defined as the
      successor of the nth element of the nth sequence that is returned by f', plus
      one.

      In other words, we compute f'(n), obtaining g^n, the n-th sequence of nats.
      Since sequences are encoded as functions from nats to nats, we then compute
      g^n(n), obtaining the successor of the n-th element of the n-th sequence.
      To make sure that g' is different then all the previously enumerated g^i,
      we fix g'(n)= S(g^n(n)).
  *)
  pose (g' := fun n => S (f' n n)). (* Construction of g' *)
  (*  Then we assert by contradiction
      that g' is indeed different then all the other g^i : *)
  assert (forall (n : nat), g' = f' n -> False).  (* Assertion 1*)
  - intros.
    (*  firstly we show that if g'(n)=f'(nn)=g^n(n) then a contradiction follows;
        this follows directly by construction of g' . *)
    assert (f' n n = g' n -> False).              (* Assertion 2 *)
    + intro.
      unfold g' in H0.       (* def of g' *)
      eapply n_Sn.           (* library result: n = S n is always false *)
      exact H0.              (* exactly the assumption towards contradiction*)
    (*  then we show the goal of Assertion 1: g' is not in the enumeration.
        This follows directly from Assertion 2.*)
    + apply H0.              (* apply Assertion 2 *)
      rewrite H.             (* apply the assumption towards a contradiction*)
      reflexivity.
    (* Finally, we assume that f' is surjective, and specifically that there
       is a proof that there is x:nat s.t. f'(x)=g'.
       From this assumption we arrive at a contradiction by a direct application
       of Assertion 1 and of the definition of g' . *)
  - pose proof (surj_f' g'). (* Assume by contradiction that g' is in the enum*)
    destruct H0.             (* implied by the assumption *)
    eapply H.                (* apply Assertion 1 *)
    rewrite H0.              (* apply def of g' *)
    reflexivity.