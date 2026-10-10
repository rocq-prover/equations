(* Test for issue #733: [dependent elimination] and [depelim] should be
   compatible with [Set Mangle Names]: user-given [as]-pattern names and
   pre-existing hypothesis names must be preserved, while generated names
   are mangled. *)
From Equations Require Import Equations.

Inductive vec : nat -> Type :=
| vnil : vec 0
| vcons : forall n, nat -> vec n -> vec (S n).
Derive Signature for vec.

(** Without [Mangle Names], the [as]-pattern names are honored, as
    documented. *)
Lemma dependent_elimination_ok n (v : vec (S n)) : nat.
Proof.
  dependent elimination v as [@vcons k x tl].
  exact (x + k).
Qed.

Set Mangle Names.

(** The [as]-pattern names must be bound under [Mangle Names]. *)
Lemma dependent_elimination_mangle n (v : vec (S n)) : nat.
Proof.
  dependent elimination v as [@vcons k x tl].
  exact (x + k).
Qed.

(** Hypotheses unrelated to the eliminated variable keep their names. *)
Lemma dependent_elimination_telescope n (v : vec (S n)) (m : nat) : nat.
Proof.
  dependent elimination v as [@vcons k x tl].
  exact (m + k + x).
Qed.

(** Same without a pattern: the telescope is preserved, while the names of
    the new hypotheses are generated and hence mangled. *)
Lemma dependent_elimination_nopat n (v : vec (S n)) (m : nat) : m = m.
Proof.
  dependent elimination v.
  exact (@eq_refl nat m).
Qed.

(** [depelim] preserves the names of unrelated hypotheses too. *)
Lemma depelim_telescope n (v : vec (S n)) (m : nat) : m = m.
Proof.
  depelim v.
  exact (@eq_refl nat m).
Qed.

(** [noconf] goes through the same block/reintroduction machinery: the names
    of the hypotheses it reverts must be preserved as well. *)
Inductive tree := Leaf : nat -> tree | Node : tree -> tree -> tree.
Derive NoConfusion for tree.

Lemma noconf_telescope (a b : nat) (H : Leaf a = Leaf b) (k : nat) : a = b.
Proof.
  noconf H.
  clear k.
  exact (@eq_refl nat a).
Qed.
