From mathcomp Require Import ssreflect.all_ssreflect solvable.all_solvable.
Set Implicit Arguments.
Unset Strict Implicit.
Set Printing All.
Unset Printing Implicit Defensive.
Set Nested Proofs Allowed.

Module SsrSyntax.

(* Defines p as a prime, as well as the constraints 
   for g and k*)
Definition valid_modulus (p g k: nat) :=
  0 < g < p - 1
  /\
  1 < k < p - 1
  /\
  prime p.

(* Defines g as a natural number *)
Definition valid_base (g k: nat) :=
  exists p: nat,
    valid_modulus p g k.

(* Defines y as the result of g ^ x *)
Definition valid_y (y g x: nat) :=
  y = (g ^ x).

(* Defines a as the result of g ^ k *)
Definition valid_a (a g k: nat) :=
  a = (g ^ k).

(* Defines b as being the secret key, which is 
   caluclated below *)
Definition valid_b (b s: nat) :=
  b = s.

(* Defines the formula for calculating the secret
   key when encrypting a message *)
Definition valid_enc_secret (s y k: nat) :=
  s = (y ^ k).

(* Defines the formula for calculating the secret 
   key ehrn decrypting a message *)
Definition valid_dec_secret (s a x: nat) :=
  s = (a ^ x).

(* checks that all of the variables are within
   their set constraints *)
Definition valid_keys (y b a g x k s: nat) :=
  valid_y y g x
  /\
  valid_a a g k
  /\
  valid_b b s
  /\
  valid_enc_secret s y k
  /\
  valid_dec_secret s a x
  /\
  valid_base g k.

(* Defines the decryption theorem for ElGamal *)
Definition spec_of_elgamal_encrypt_decrypt
  (decrypt: nat -> nat -> nat -> nat) :=
  forall b s m,
    decrypt b s m = ((b %| s) * m).

Definition elgamal_decrypt (b s m: nat) :=
  m = ((b %| s) * m).

(* The assertion that decrypting an encrypted message
   will result in the original message *)
Theorem prove_validity_of_ElGamal:
  forall decrypt: nat -> nat -> nat -> nat,
    spec_of_elgamal_encrypt_decrypt decrypt ->
      forall y b a g x k m s,
        valid_keys y b a g x k s->
        decrypt b s m = m.

(* The poof to validate the ElGamal theorem *)
Proof.
  intros decrypt h_decrypt y b a g x k m s h_valid_keys.
  assert (h_temp := h_valid_keys).
  unfold valid_keys in h_temp.
  destruct h_temp as [h_valid_y h_valid_a].
  destruct h_valid_a as [h_valid_a h_valid_b].
  destruct h_valid_b as [h_valid_b h_valid_enc_secret].
  destruct h_valid_enc_secret as [h_valid_enc_secret h_valid_dec_secret].
  destruct h_valid_dec_secret as [h_valid_dec_secret h_valid_base].
  unfold spec_of_elgamal_encrypt_decrypt in h_decrypt.

  rewrite -> h_decrypt.

  unfold valid_y in h_valid_y.
  unfold valid_a in h_valid_a.
  unfold valid_b in h_valid_b.
  unfold valid_enc_secret in h_valid_enc_secret.
  unfold valid_dec_secret in h_valid_dec_secret.
  unfold valid_base in h_valid_base.
  
  assert (h_secrets_equal: y ^ k = a ^ x).
    rewrite -> h_valid_y.
    rewrite -> h_valid_a.
    rewrite -> expnAC.
    rewrite <- h_valid_a.
    reflexivity.
    
  rewrite -> h_valid_dec_secret.
  rewrite -> h_valid_a.
  rewrite -> h_valid_b.
  rewrite -> h_valid_enc_secret.
  rewrite -> h_valid_y.
  rewrite <- (expnAC g x k).
  rewrite <- h_valid_y.
  rewrite -> (dvdnn (y ^ k)).
  simpl.
  rewrite -> mul1n.
  reflexivity.
Qed.
Print prove_validity_of_ElGamal.


  
