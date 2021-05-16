From mathcomp Require Import ssreflect.all_ssreflect solvable.all_solvable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Nested Proofs Allowed.

Module SsrSyntax.

(* Defines n, p and q, where p and q are primes, 
   and n is the product of p and q *)
Definition valid_mod_primes (n p q: nat):=
  n = p * q
  /\
  prime p
  /\
  prime q
  /\
  p <> q.

(* Defines totient n, which is the product 
   of p -c1 and q - 1*)
Definition valid_totient_n (n p q: nat):=
  totient n = (p - 1) * (q - 1).

(* Checks that n, p, q and totient n are within 
   their set parameters *)
Definition valid_mod (n p q: nat):=
  valid_mod_primes n p q
  /\
  valid_totient_n n p q.

(* Defines e and d *)
Definition valid_exponents (d e n: nat):=
  e * d = 1 %% (totient n).

(* Defines Euler's Totient Theorem *)
Definition Eulers_theorem (n: nat) :=
  1 %% totient n = 1.

(* Checks that d, e, n, p, and q are within 
   their set parameters *)
Definition valid_key_pair (d e n p q: nat):=
  valid_exponents d e n
  /\
  valid_mod n p q.

(* Defines the encryption and decryption schemes
   for RSA *)
Definition spec_of_RSA_encrypt (encrypt: nat -> nat -> nat -> nat):=
  forall m e n: nat,
    encrypt m e n = m ^ e %% n.

Definition spec_of_RSA_decrypt (decrypt: nat -> nat -> nat -> nat):=
  forall c d n: nat,
    decrypt c d n = c ^ d %% n.

Definition RSA_encrypt (m e n: nat): nat :=
  m ^ e %% n.

Definition RSA_decrypt (c d n: nat): nat :=
  c ^ d %% n.

(* The assertion that decrypting an encrypted message will
   result in m %% n *)
Theorem RSA_encryption_scheme_valid:
forall encrypt decrypt: nat -> nat -> nat -> nat,
    spec_of_RSA_encrypt encrypt ->
    spec_of_RSA_decrypt decrypt ->
    forall d e n p q m : nat,
      valid_key_pair d e n p q ->
      Eulers_theorem n ->
      decrypt (encrypt m e n) d n = m %% n.

(* The proof to validate the RSA theorem *)
Proof.
  intros encrypt decrypt h_encrypt h_decrypt d e n p q m h_valid_key_pair h_Eulers_theorem.
  assert (h_temp := h_valid_key_pair).
  unfold valid_key_pair in h_temp.
  destruct h_temp as [h_valid_exponents h_valid_mod].
  unfold valid_mod in h_valid_mod.
  destruct h_valid_mod as [h_valid_mod_primes h_valid_totient_n].
  destruct h_valid_mod_primes as [h_valid_n h_valid_mod_primes].
  unfold valid_mod_primes in h_valid_mod_primes.
  unfold valid_totient_n in h_valid_totient_n.
  unfold valid_exponents in h_valid_exponents.
  unfold spec_of_RSA_encrypt in h_encrypt.
  unfold spec_of_RSA_decrypt in h_decrypt.
  unfold Eulers_theorem in h_Eulers_theorem.

  rewrite -> h_encrypt.
  rewrite -> h_decrypt.
  rewrite -> modnXm.
  rewrite <- expnM.
  rewrite -> h_valid_exponents.
  rewrite -> h_Eulers_theorem.
  rewrite -> expn1.
  reflexivity.
Qed.
Print RSA_encryption_scheme_valid.
