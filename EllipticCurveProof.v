From mathcomp Require Import ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Nested Proofs Allowed.

Module SsrSyntax.

(* this proof should not be considered correct, 
   due to the no elliptic curve being defined for 
   point g. Please see the report for more details *)

(* Defines n as a prime *)
Definition valid_point_order (n: nat) :=
  prime n.

(* Defines the secret integer a as being less than n  *)
Definition valid_a_secret (a n: nat) :=
  valid_point_order n
  /\
  a < n.

(* Defines the secret integer b as being less than n *)
Definition valid_b_secret (b n: nat) :=
  valid_point_order n
  /\
  b < n.

(* Defines the theorrem to generate the key A *)
Definition key_a_generation (A G a: nat) :=
  A = a * G.

(* Defines the theorem to generate the key B *)
Definition key_b_generation (B G b: nat) :=
  B = b * G.

(* Checks that all of the variables are within
   their set constraints *)
Definition valid_key_pair (A B G a b n: nat) :=
  valid_a_secret a n
  /\
  valid_b_secret b n
  /\
  key_a_generation A G a
  /\
  key_b_generation B G b 
  /\
  valid_point_order n.

(* Defines the encryption fuunctions using A and B *)
Definition spec_of_enc_func_a 
          (encrypt: nat -> nat -> nat) :=
  forall A b: nat,
    encrypt A b = b * A.

Definition spec_of_enc_func_b
          (encrypt: nat -> nat -> nat) :=
  forall B a: nat,
    encrypt B a = a * B.

Definition ECC_secret_a (A b: nat) :=
  A * b.

Definition ECC_secret_b (B a: nat) :=
  B * a.

(* Assertion that encrypting using either keys will
   result in the same outcome *)
Theorem Prove_validity_of_ECC_DH:
  forall encrypt_a encrypt_b: nat -> nat -> nat,
    spec_of_enc_func_a encrypt_a ->
    spec_of_enc_func_b encrypt_b ->
    forall A B G a b n: nat,
      valid_key_pair A B G a b n ->
      encrypt_a A b = encrypt_b B a.

(* Proof to validate the Elliptic Curve 
   Diffie-Hellman theorem *)
Proof.
  intros encrypt_a encrypt_b h_encrypt_a h_encrypt_b A B G a b n h_valid_key_pair.
  assert (h_temp := h_valid_key_pair).
  unfold valid_key_pair in h_temp.
  destruct h_temp as [h_valid_a_secret h_valid_b_secret].
  destruct h_valid_b_secret as [h_valid_b_secret h_key_a_generation].
  destruct h_key_a_generation as [h_key_a_generation h_key_b_generation].
  destruct h_key_b_generation as [h_key_b_generation h_valid_point_order].
 
  unfold spec_of_enc_func_a in h_encrypt_a.
  unfold spec_of_enc_func_b in h_encrypt_b.
  unfold key_a_generation in h_key_a_generation.
  unfold key_b_generation in h_key_b_generation.
  unfold valid_a_secret in h_valid_a_secret.
  unfold valid_b_secret in h_valid_b_secret.
  unfold valid_point_order in h_valid_point_order.

  rewrite -> h_encrypt_a.
  rewrite -> h_encrypt_b.

  rewrite -> h_key_a_generation.
  rewrite -> h_key_b_generation.
  ring_simplify.
  reflexivity.
Qed.
Print Prove_validity_of_ECC_DH.




