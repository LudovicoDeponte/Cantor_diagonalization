(* we define the surjective property *)
Record Sur { A B : Type } : Type :=
  { fSur_to      : A -> B
  ; surj_f       : forall (b : B), exists (a : A), b = fSur_to(a)
  }.
Arguments Sur : clear implicits.

(* and the injective property *)
Definition injective {A B} (f : A -> B) := forall a1 a2, f a1 = f a2 -> a1 = a2.

(*
we use A B as general Types for any set, then we define a function
f_to, from A to B and we impose that it holds that surj_f, i.e.
f is surjective
*)

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
    g   : nat -> nat                 is the sequence of nats
    g^n : nat -> nat
*)
Theorem Cantor_InfNSeq:
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

Restart. (* we also provide a compact version of the same proof *)

  intros; destruct H as (f' & surj_f').
  pose (g' := fun n => S (f' n n)).
  assert (forall (n : nat), g' = f' n -> False).
  - intros.
    assert (f' n n = g' n -> False).
    + intro.
      unfold g' in H0.
      now apply n_Sn with (n:= f' n n).
    + now apply H0; rewrite H.
  - pose proof (surj_f' g').
    destruct H0.
    now apply H with (n := x).
Qed.

(* 2. P(N) IS UNCOUNTABLE *)
(*    a Formalize P(N): use a function nat->bol for each Set;
        f(n)=True iff n is in the set S
      b Replicate the diagonalization argument
*)
Require Import Bool.

Lemma Contradiction_bool (a : bool):
  a = negb a -> False.
Proof.
  intro.
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

Restart.

  induction a; intro; eapply eq_true_false_abs; easy.
Qed.

Theorem Cantor_PN:
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
Restart.
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

(* 3. RATIONALS ARE COUNTABLE *)
(*    a Formalize Q: use a tuple with a proof of reduction;
        - use Z for numerator and Z-0 for denominator
        - formalize divisibility
      b show a bijection between N and Q
        - show an injection from N to Q
        - show an injection from Q to N
        - Cantor-Schroder-Bernstein Theorem
*)

Require Export ZArith_base.

Definition ZDivisibility (a : Z) (b : positive) :=
  exists x:Z, ((Zpos b)*x = a)%Z.
Notation "( a | b )" := (ZDivisibility a b) (at level 0).

Definition ZGreatestCommonDivisor (a b :Z) (x :positive): Prop :=
 ((a | x) /\ (b | x)) /\ ((exists  x':positive, (a | x') /\ (b | x') /\ (x< x')%positive)-> False).
Notation "( a b | x )" := (ZGreatestCommonDivisor a b x) (at level 0).
Require Import Lia.

Lemma ABS_a_eq_1_and_a_grt_1 (a :positive):
  ((a = 1)%positive /\ (1 < a)%positive) -> False.
Proof.
  lia.
Qed.

Lemma mul_a_b_eq_1_imp_a_eq_1 (a: positive) (b :Z):
  (Z.pos a * b = 1)%Z -> (a = 1)%positive.
Proof.
  intro.
Admitted.

Lemma ABS_mul_a_b_eq_1_and_a_g_1 (a :positive) (b :Z):
  ((Z.pos a * b = 1)%Z/\(a>1)%positive) -> False.
Proof.
  intro.
  destruct H.
  apply mul_a_b_eq_1_imp_a_eq_1 in H.
  apply ABS_a_eq_1_and_a_grt_1 with (a:= a).
  lia.
Qed.

Lemma Z_one_GCD (a :Z):
  ZGreatestCommonDivisor a 1%Z 1%positive.
Proof.
unfold ZGreatestCommonDivisor.
split.
 + split.
   - unfold ZDivisibility.
     exists a.
     rewrite Z.mul_1_l.
     reflexivity.
   - unfold ZDivisibility.
     exists 1%Z.
     rewrite Z.mul_1_l.
     reflexivity.
 + intros.
   destruct H.
   destruct H as [eq1 H].
   destruct H as [eq2 dis].
   unfold ZDivisibility in eq1.
   unfold ZDivisibility in eq2.
   destruct eq1 as [x1 eq1].
   destruct eq2 as [x2 eq2].
   assert ((x =1)%positive \/ (x>1)%positive ).
   -  lia.
   -  destruct H.
      * eapply ABS_a_eq_1_and_a_grt_1.
        split.
        -- exact H.
        -- exact dis.
      * eapply ABS_mul_a_b_eq_1_and_a_g_1.
        split.
        -- exact eq2.
        -- exact H.

Restart.

unfold ZGreatestCommonDivisor.
split.
 + split; unfold ZDivisibility.
   - exists a.
     now rewrite Z.mul_1_l.
   - exists 1%Z.
     now rewrite Z.mul_1_l.
 + intros.
   destruct H.
   destruct H as [eq1 H].
   destruct H as [eq2 dis].
   unfold ZDivisibility in eq1.
   unfold ZDivisibility in eq2.
   destruct eq1 as [x1 eq1].
   destruct eq2 as [x2 eq2].
   assert ((x =1)%positive \/ (x>1)%positive ).
   -  lia.
   -  destruct H.
      * apply ABS_a_eq_1_and_a_grt_1 with (a := x); lia.
      * apply ABS_mul_a_b_eq_1_and_a_g_1 with (a := x) (b := x2); lia.
Qed. 

Record Q :=
  { Q_num: Z
  ; Q_den: positive

  ; Q_red: ZGreatestCommonDivisor Q_num (Zpos Q_den) 1%positive
  }.  

Require Import Coq.Logic.ProofIrrelevance. (* to equate Q_red proofs *)

Lemma Q_equivalence (a b : Q) :
a = b -> Q_num a = Q_num b /\ Q_den a = Q_den b.
Proof.
  intro.
  split.
  - now apply (f_equal Q_num) in H.
  - now apply (f_equal Q_den) in H.
Qed.

Lemma Q_equivalence' (a b : Q) :
  Q_num a = Q_num b -> Q_den a = Q_den b -> a = b.
Proof.
  destruct a as [a_num a_den a_red].
  destruct b as [b_num b_den b_red].
  simpl.
  intros eq_num eq_den.
  revert a_red.               (* opposite of intro *)
  revert b_red.
  rewrite <- eq_num.
  rewrite <- eq_den.
  intros.
  rewrite (proof_irrelevance _ a_red b_red).
  reflexivity.

Restart.

  destruct a as [a_num a_den a_red], b as [b_num b_den b_red].
  simpl.
  intros eq_num eq_den.
  revert a_red b_red.
  rewrite <- eq_num, <- eq_den.
  intros.
  now rewrite (proof_irrelevance _ a_red b_red).
Qed.

(* We want to show that there is an injection from N to Q *)
Program Definition f_N_to_Q (n: nat) : Q := {|
Q_num := Z.of_nat n;
Q_den := 1%positive;
|}.
Next Obligation.
  unfold ZGreatestCommonDivisor.
  split.
  + split.
    - unfold ZDivisibility.
      exists (Z.of_nat n).
      rewrite Z.mul_1_l.
      reflexivity.
    - unfold ZDivisibility.
      exists 1%Z.
      rewrite Z.mul_1_l.
      reflexivity.
  + apply Z_one_GCD.

Restart.

  unfold ZGreatestCommonDivisor; split.
  + split; unfold ZDivisibility.
    - exists (Z.of_nat n); now rewrite Z.mul_1_l.
    - exists 1%Z; now rewrite Z.mul_1_l.
  + apply Z_one_GCD.
Qed.
 Require Import Znat.
Theorem inj_N_to_Q:
  injective f_N_to_Q.
Proof.
  unfold injective.
  intros a b H.
  unfold f_N_to_Q in H.
  apply Q_equivalence in H.
  destruct H as [eq_num eq_den].
  simpl in eq_num.
  simpl in eq_den.
  apply Nat2Z.inj. (* injectivity of Z.of_nat*)
  exact eq_num.

Restart.

  unfold injective.
  intros a b H.
  unfold f_N_to_Q in H; apply Q_equivalence in H; destruct H; simpl in H.
  now apply Nat2Z.inj.
Qed.

(* We want to show that there is an injection from Q to N *)
(* we do this by explicitly showing a function f_Q_to_N that is injective *)
Require Import Nat. (* used for powers - pow *)

(* we define a sign function from sign of Z to nat *)
(* this function assigns 1 to positive, 0 to other integers*)
(* we want the function to assign a non-negative number as later we are going
to apply it and use the result as an exponent for the Godel's encoding,
which must return an integer *)
Definition sign (z : Z) : nat :=
  match z with
  | 0%Z => 0
  | Zpos p => 1
  | Zneg p => 0
  end.

Lemma Z_abs_sgn_eq (a b : Z):
  Z.abs a = Z.abs b -> sign a = sign b -> a = b.
Proof.
  intros.
  unfold Z.abs in H.
  unfold sign in H0.
Admitted.

Lemma small_Godel (a1 a2 a3 b1 b2 b3: nat):
  (pow 2 a1)*(pow 3 a2)*(pow 5 a3) = (pow 2 b1)*(pow 3 b2)*(pow 5 b3) ->
  a1=b1 /\ a2 = b2 /\ a3 = b3.
Proof.
  intro.
Admitted.

Require Import PArith. (* for injectivity of Pos.to_nat *)

Definition f_Q_to_N (q : Q) : nat :=
  (pow 2 (Z.to_nat (Z.abs(Q_num q))))*(pow 3 (sign (Q_num q)))*(pow 5 (Pos.to_nat (Q_den q))).

Theorem inj_Q_to_N:
 injective f_Q_to_N.
Proof.
  unfold injective.
  intros a b H.
  unfold f_Q_to_N in H.
  destruct a as [a_num a_den a_red].
  destruct b as [b_num b_den b_red].
  simpl in H.
  apply small_Godel in H.
  destruct H as [eq_num_abs].
  destruct H as [eq_num_sgn eq_den].
  apply Q_equivalence'.
  - simpl.
    apply Z_abs_sgn_eq.
    + apply Z2Nat.inj in eq_num_abs.
      * exact eq_num_abs.
      * induction a_num.
        --  simpl.
            reflexivity.
        --  simpl.
            apply Pos2Z.is_nonneg.
        --  simpl.
            apply Pos2Z.is_nonneg.
      * induction b_num.
        --  simpl.
            reflexivity.
        --  simpl.
            apply Pos2Z.is_nonneg.
        --  simpl.
            apply Pos2Z.is_nonneg.
    + exact eq_num_sgn.
  - simpl.
    apply Pos2Nat.inj.
    exact eq_den.

Restart.

unfold injective.
intros a b H.
unfold f_Q_to_N in H.
destruct a as [a_num a_den a_red], b as [b_num b_den b_red].
simpl in H.
apply small_Godel in H.
destruct H as [eq_num_abs], H as [eq_num_sgn eq_den ].
apply Q_equivalence'; simpl.
  - apply Z_abs_sgn_eq.
    + apply Z2Nat.inj in eq_num_abs.
      * exact eq_num_abs.
      * lia.
      * lia.
    + exact eq_num_sgn.
  - now apply Pos2Nat.inj.
Qed.

Theorem C_B_S_Thm: forall(A B:Type) (f:A->B) (g:B->A),
    (forall a0 a1, f a0 = f a1 -> a0 = a1) ->
    (forall b0 b1, g b0 = g b1 -> b0 = b1) ->
    exists f : A -> B, exists g : B -> A,
      (forall a, g (f a) = a) /\ (forall b, f (g b) = b).
Proof.
Admitted.

(* finally, we show that Q is countably infinite by showing that
there is a bijection between nat and Q *)
Theorem Q_Countable:
  exists f : nat -> Q, exists g : Q -> nat,
  (forall a, g (f a) = a) /\ (forall b, f (g b) = b).
Proof.
  eapply C_B_S_Thm.
  - exact inj_N_to_Q.
  - exact inj_Q_to_N.
Qed.

(*
REFERENCES:
Cantor's arg  https://en.wikipedia.org/wiki/Cantor%27s_diagonal_argument

approach      https://github.com/bmsherman/finite/blob/master/Iso.v#L277-L291:~:text=Theorem%20Cantor%20%3A%20T%20nat%20(nat%20%2D%3E%20nat)%20%2D%3E%20False.

record dev    https://stackoverflow.com/questions/50924127/record-equality-in-coq

Q count diag  https://aminsaied.wordpress.com/2012/05/21/diagonal-arguments/
N to Q        https://stackoverflow.com/questions/55603662/proving-that-a-rational-function-is-monotonically-nondecreasing-in-coq
Q to N        https://math.stackexchange.com/questions/333221/how-to-prove-that-the-set-of-rational-numbers-are-countable

Cantor-Ber    https://www.researchgate.net/publication/339270363_A_Formal_Proof_in_Coq_of_Cantor-Bernstein-Schroeder's_Theorem_without_axiom_of_choice/link/61273e9b38818c2eaf5f0649/download
              https://gist.github.com/qnighy/093229b6a02e685bd5ef93c13ce53b1f

DOCUMENTATION
n_Sn          https://coq.inria.fr/library/Coq.Init.Peano.html#:~:text=Theorem%20n_Sn%20%3A%20forall%20n%3Anat%2C%20n%20%3C%3E%20S%20n.
pow           https://coq.inria.fr/library/Coq.Init.Nat.html
Z             https://coq.inria.fr/library/Coq.ZArith.ZArith_base.html
Z.abs         https://coq.inria.fr/library/Coq.ZArith.Zabs.html
Zpos Zneg     https://coq.inria.fr/library/Coq.ZArith.BinIntDef.html#Z.pos
Z to nat      https://coq.inria.fr/library/Coq.ZArith.Znat.html
Z.mul_1_l     https://coq.inria.fr/library/Coq.ZArith.BinInt.html
Z.of:nat inj  https://coq.inria.fr/library/Coq.ZArith.Znat.html#:~:text=Lemma%20inj%20n%20m%20%3A%20Z.of_nat%20n%20%3D%20Z.of_nat%20m%20%2D%3E%20n%20%3D%20m.
*)