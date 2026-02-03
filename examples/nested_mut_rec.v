(** printing elimination %\coqdoctac{elimination}% *)
(** printing <= %\rightarrow% #⇐# *)
(** * Nested and mutual structurally recursive definitions

  Example of a term structure with two constructors taking lists of terms. *)

From Equations.Prop Require Import Equations.

From Stdlib Require Import Program Arith List Compare_dec.
Import ListNotations.

Scheme All for list.

(** A nested recursive definition of terms with lists of terms *)

Inductive term : Set :=
| Var (n : nat)
| Lam (t : term)
| App (t : term) (l : list term)
| MetaVar (n : nat) (l : list term).

(** Defining capture-avoiding substitution for this language:
    the case of variables. *)

Equations subst_var (k : nat) (u : term) (t : nat) : term :=
  subst_var k u n with k ?= n =>
   { | Eq => u;                                                                
     | Gt => Var n;
     | Lt => Var (pred n) }.

(** Nested recursive definition using a top-level [where] definition.

    The nested recursive fixpoint defined by [subst_tlist] can be used multiple
    time in [subst_term], and of course recursively call itself and [subst_term].
    The regular structural guardedness check is run on this definition to check
    that it is terminating. Note that one can optionally add a [struct x] annotation
    to [where] clauses to indicate which arguments decreases explicitely, otherwise
    _only the last argument_ is tried.
 *)

Equations subst_term (k : nat) (u : term) (t : term) : term := {
subst_term k u (Var n) => subst_var k u n;
subst_term k u (Lam t) => Lam (subst_term (S k) u t);
subst_term k u (App t l) => App (subst_term k u t) (subst_tlist k u l);
subst_term k u (MetaVar t l) => MetaVar t (subst_tlist k u l) }

where subst_tlist (k : nat) (u : term) (t : list term) : list term := {
  subst_tlist k u nil => nil;
  subst_tlist k u (cons t ts) => cons (subst_term k u t) (subst_tlist k u ts) }.

(** Remark that our definition of [subst_tlist] is equivalent to a [List.map]:
    but we need the "expanded" version to properly recognize recursive calls. *)

Lemma nested_map k u t : subst_tlist k u t = List.map (subst_term k u) t.
Proof.
  induction t; simpl; rewrite ?IHt; trivial.
Qed.

(** The elimination principle generated from this definition is giving a conjunction
    of two predicates as result. One may want to instantiate [P0] with [Forall P] to recover
    a [map]-like elimination principle. *)

Check subst_term_elim
  : forall (P : nat -> term -> term -> term -> Type)
           (P0 : nat -> term -> list term -> list term -> Type),
    (forall (k : nat) (u : term) (n : nat), P k u (Var n) (subst_var k u n)) ->
    (forall (k : nat) (u t : term),
        P (S k) u t (subst_term (S k) u t) -> P k u (Lam t) (Lam (subst_term (S k) u t))) ->
    (forall (k : nat) (u t0 : term) (l : list term),
        P k u t0 (subst_term k u t0) ->
        P0 k u l (subst_tlist k u l) ->
        P k u (App t0 l) (App (subst_term k u t0) (subst_tlist k u l))) ->
    (forall (k : nat) (u : term) (n0 : nat) (l0 : list term),
        P0 k u l0 (subst_tlist k u l0) -> P k u (MetaVar n0 l0) (MetaVar n0 (subst_tlist k u l0))) ->
    (forall (k : nat) (u : term), P0 k u []%list []%list) ->
    (forall (k : nat) (u t : term) (l : list term),
        P k u t (subst_term k u t) ->
        P0 k u l (subst_tlist k u l) ->
        P0 k u (t :: l)%list (subst_term k u t :: subst_tlist k u l)%list) ->

    (forall (k : nat) (u t : term), P k u t (subst_term k u t)) *
    (forall (k : nat) (u : term) (t : list term), P0 k u t (subst_tlist k u t)).

(** One can experiment to see that this provides the right induction hypotheses for App and MetaVar *)

Lemma subst_subst k u t : subst_term k u t = subst_term k u t.
Proof.
  revert k u t.
  refine (fst (subst_term_elim (fun k u t c => c = c) (fun k u l c => c = c) _ _ _ _ _ _));
  trivial.
Qed.
