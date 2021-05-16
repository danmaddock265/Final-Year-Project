From mathcomp Require Import ssreflect.all_ssreflect solvable.all_solvable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 
Set Nested Proofs Allowed.

Module SsrSyntax.

(* Defines p as a prime (known as modulus and grater than g) *)
Definition valid_modulus (p g: nat) :=
  0 < g < p
  /\
  prime p.

(* Defines g as a natural number (known as base) that is less than p *)
Definition valid_base (g: nat) :=
  exists p: nat,
    valid_modulus p g.

(* Defines the formula to get the public key *)
Definition valid_public_key (A g p a: nat) :=
    A = g ^ a %% p.


(* Defines the formula to get the private key *)
Definition valid_private_key (B g p b: nat) :=
    B = g ^ b %% p.


(* Checks that the key pairs are valid *)
Definition valid_key_pair (A B g p a b: nat) :=
  valid_public_key A g p a
  /\
  valid_private_key B g p b
  /\
  valid_base g.


(* Defines the encryption function using the public key *)
Definition spec_of_encryption_function_a 
          (encrypt: nat -> nat -> nat -> nat) :=
  forall p b A: nat,
    encrypt p b A = A ^ b %% p.

(* Defines the encryption function using the private key *)
Definition spec_of_encryption_function_b 
          (encrypt: nat -> nat -> nat -> nat) :=
  forall p a B: nat,
    encrypt p a B = B ^ a %% p.

(* The formula for both of the two equations *)
Definition Diffie_Hellman_encrypt_a (p b A: nat): nat :=
  A ^ b %% p.

Definition Diffie_Hellman_encrypt_b (p a B: nat): nat :=
  B ^ a %% p.


(* Assertion that encrypting using either keys will
   result in the same outcome *)
Theorem prove_validity_of_Diffie_Hellman:
  forall encrypt_a encrypt_b: nat -> nat -> nat -> nat,
    spec_of_encryption_function_a encrypt_a ->
    spec_of_encryption_function_b encrypt_b ->
    forall A B g p a b: nat,
      valid_key_pair A B g p a b ->
      encrypt_a p b A = encrypt_b p a B.

(* The proof to validate Diffie-Hellman theorem *)
Proof.
  intros encrypt_a encrypt_b h_encrypt_a h_encrypt_b A B g p a b h_valid_key_pair.
  assert (h_temp := h_valid_key_pair).
  unfold valid_key_pair in h_temp.
  destruct h_temp as [h_valid_public_key h_valid_private_key].
  destruct h_valid_private_key as [h_valid_private_key h_valid_base].

  unfold spec_of_encryption_function_a in h_encrypt_a.
  unfold spec_of_encryption_function_b in h_encrypt_b.
  rewrite -> h_encrypt_b.
  unfold valid_public_key in h_valid_public_key.
  unfold valid_private_key in h_valid_private_key.
  unfold valid_base in h_valid_base.

  rewrite -> h_valid_private_key.
  rewrite -> modnXm.
  rewrite <- expnAC. 
  rewrite <- modnXm.
  rewrite -> h_encrypt_a.
  rewrite <- h_valid_public_key.
  reflexivity.
  reflexivity.
Qed.
Print prove_validity_of_Diffie_Hellman.