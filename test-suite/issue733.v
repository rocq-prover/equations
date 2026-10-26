(* Test for issue #733: [dependent elimination] and [depelim] should be
   compatible with [Set Mangle Names]: user-given [as]-pattern names and
   pre-existing hypothesis names must be preserved, while generated names
   are mangled. *)
From Equations Require Import Equations.

(** Reduced from MetaRocq's [arity_typing_spine]. Reserving the existing
    [na] as an implicit pattern used to consume a temporary [na0], changing
    the constructor argument to [na1] even with [Mangle Names] off. *)
Inductive spine : nat -> Type :=
| cons {ty hd na : nat} : ty = na -> spine ty.

Goal forall (na ty inst : nat) (H H' : spine ty), True.
Proof.
  intros na ty inst H H'.
  dependent elimination H' as [cons cum].
  assert (ty0 = na0) by exact cum.
  exact I.
Qed.

Goal forall (na na0 ty inst : nat) (H H' : spine ty), True.
Proof.
  intros na na0 ty inst H H'.
  dependent elimination H' as [cons cum].
  assert (ty0 = na1) by exact cum.
  exact I.
Qed.

Goal forall (na ty inst : nat) (H H' : spine ty), True.
Proof.
  intros na ty inst H H'.
  dependent elimination H'.
  assert (ty = na0) by exact e.
  exact I.
Qed.

(** Default-mode shadowing checks also retain their historical behavior. *)
Goal forall (a : nat) (b : nat * nat), True.
Proof.
  intros a b.
  Fail dependent elimination b as [(a, x)].
  dependent elimination b as [(x, y)].
  exact I.
Qed.

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

(** Explicit patterns take priority over implicitly preserved names. *)
Goal forall (a : nat) (b : nat * nat), nat.
Proof.
  intros a b.
  dependent elimination b as [(a, x)].
  exact (a + x).
Qed.

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

(** Read the option at tactic execution, rather than caching its initial
    value when the plugin is loaded. *)
Unset Mangle Names.

Goal forall (na ty inst : nat) (H H' : spine ty), True.
Proof.
  intros na ty inst H H'.
  dependent elimination H' as [cons cum].
  assert (ty0 = na0) by exact cum.
  exact I.
Qed.

Goal forall (na ty inst : nat) (H H' : spine ty), True.
Proof.
  intros na ty inst H H'.
  dependent elimination H'.
  assert (ty = na0) by exact e.
  exact I.
Qed.

Set Mangle Names.

Goal forall (na ty inst : nat) (H H' : spine ty), True.
Proof.
  intros na ty inst H H'.
  dependent elimination H' as [cons cum].
  Fail let T := type of hd in idtac.
  Fail let T := type of na0 in idtac.
  clear na inst.
  exact I.
Qed.

Set Mangle Names Light.
Set Mangle Names Prefix "generated_".

Goal forall (na ty inst : nat) (H H' : spine ty), True.
Proof.
  intros na ty inst H H'.
  dependent elimination H' as [cons cum].
  Fail let T := type of hd in idtac.
  Fail let T := type of na0 in idtac.
  clear na inst.
  exact I.
Qed.

Lemma dependent_elimination_light n (v : vec (S n)) (m : nat) : nat.
Proof.
  dependent elimination v as [@vcons k x tl].
  exact (m + k + x).
Qed.

(** Light mode and a custom prefix must not affect the disabled option. *)
Unset Mangle Names.

Goal forall (na ty inst : nat) (H H' : spine ty), True.
Proof.
  intros na ty inst H H'.
  dependent elimination H' as [cons cum].
  assert (ty0 = na0) by exact cum.
  exact I.
Qed.
