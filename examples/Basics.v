(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)
(** printing elimination %\coqdoctac{elimination}% *)
(** printing noconf %\coqdoctac{noconf}% *)
(** printing simp %\coqdoctac{simp}% *)
(** printing by %\coqdockw{by}% *)
(** printing rec %\coqdockw{rec}% *)
(** printing Coq %\Coq{}% *)
(** printing funelim %\coqdoctac{funelim}% *)
(** printing Derive %\coqdockw{Derive}% *)
(** printing Signature %\coqdocclass{Signature}% *)
(** printing Subterm %\coqdocclass{Subterm}% *)
(** printing NoConfusion %\coqdocclass{NoConfusion}% *)
(** * Basic examples

  This file containts various examples demonstrating the features of Equations.
  If running this interactively you can ignore the printing
  and hide directives which are just used to instruct coqdoc. *)

#[warnings="-deprecated-library-file-since-8.20"]
From Stdlib Require Import Program Bvector List Relations.
From Equations Require Import Equations Signature.
From Stdlib Require Import Utf8.

Set Keyed Unification.

(** Just pattern-matching *)
Equations neg (b : bool) : bool :=
neg true := false ;
neg false := true.

(** A proof using the functional elimination principle derived for [neg]. *)
Lemma neg_inv : forall b, neg (neg b) = b.
Proof. intros b. funelim (neg b); auto. Qed.

Module Obligations.

  (** One can use equations similarly to Program or the [refine] tactic,
      putting underscores [_] for subgoals to be filled separately using
      the tactic mode. *)
  Equations? f (n : nat) : nat :=
  f 0 := 42 ;
  f (S m) with f m :=
  {
    f (S m) IH := _
  }.
  Proof. intros. exact IH. Defined.

End Obligations.

(** Structural recursion and use of the [with] feature to look at the result
    of a recursive call (here with a trivial pattern-matching. *)

Import List.
Equations app_with {A} (l l' : list A) : list A :=
app_with nil l := l ;
app_with (cons a v) l with app_with v l => {
  | vl := cons a vl }.


(** Structurally recursive function on natural numbers, with inspection of a recursive
    call result. We use [auto with arith] to discharge the obligations. *)

Local Obligation Tactic := program_simpl ; try CoreTactics.solve_wf ; auto with arith.

Equations equal (n m : nat) : { n = m } + { n <> m } :=
equal O O := in_left ;
equal (S n) (S m) with equal n m => {
  equal (S n) (S ?(n)) (left eq_refl) := left eq_refl ;
  equal (S n) (S m) (right p) := in_right } ;
equal x y := in_right.

(** Pattern-matching on the indexed equality type. *)
Equations eq_sym {A} (x y : A) (H : x = y) : y = x :=
eq_sym x _ eq_refl := eq_refl.

Equations eq_trans {A} (x y z : A) (p : x = y) (q : y = z) : x = z :=
eq_trans x _ _ eq_refl eq_refl := eq_refl.

Abbreviation vector := Vector.t.
Derive Signature for eq vector.

Module KAxiom.

  (** By default we disallow the K axiom, but it can be set. *)

  (** In this case the following definition fails as [K] is not derivable on type [A]. *)
  Fail Equations K {A} (x : A) (P : x = x -> Type) (p : P eq_refl) (H : x = x) : P H :=
    K x P p eq_refl := p.

  Set Equations With UIP.
  Axiom uip : forall A, UIP A.
  Local Existing Instance uip.
  Equations K_ax {A} (x : A) (P : x = x -> Type) (p : P eq_refl) (H : x = x) : P H :=
    K_ax x P p eq_refl := p.

  (** The definition is however using an axiom equivalent to [K], so it cannot reduce
      on closed or open terms. *)
End KAxiom.

Module KDec.
  (** However, types enjoying a provable instance of the [K] principle are fine using the [With UIP]
      option. Note that the following definition does *not* reduce according to its single clause
      on open terms, it instead computes using the decidable equality proof on natural numbers. *)

  Set Equations With UIP.

  Fail Equations K {A} (x : A) (P : x = x -> Type) (p : P eq_refl) (H : x = x) : P H :=
    K x P p eq_refl := p.

  Equations K (x : nat) (P : x = x -> Type) (p : P eq_refl) (H : x = x) : P H :=
    K x P p eq_refl := p.
  Print Assumptions K. (* Closed under the global context *)

End KDec.

(** The [with] construct allows to pattern-match on an intermediary computation.
    The "|" syntax provides a shortcut to repeating the previous patterns. *)
Section FilterDef.
  Context {A} (p : A -> bool).

  Equations filter (l : list A) : list A :=
  filter nil := nil ;
  filter (cons a l) with p a => {
                       | true := a :: filter l ;
                       | false := filter l }.

  (** By default, equations makes definitions opaque after definition,
      to avoid spurious unfoldings, but this can be reverted on a case by case
      basis, or using the global [Set Equations Transparent] option. *)
  Global Transparent filter.

End FilterDef.

(** We define inclusion of a list in another one, to specify the behavior of [filter] *)
Inductive incl {A} : relation (list A) :=
  stop : incl nil nil 
| keep {x : A} {xs ys : list A} : incl xs ys -> incl (x :: xs) (x :: ys)
| skip {x : A} {xs ys : list A} : incl xs ys -> incl (xs) (x :: ys).

(** Using [with] again, we can produce a proof that the filtered list is a
    sublist of the original list. *)
Equations sublist {A} (p : A -> bool) (xs : list A) : incl (filter p xs) xs :=
sublist p nil := stop ;
sublist p (cons x xs) with p x := {
  | true := keep (sublist p xs) ;
  | false := skip (sublist p xs) }.

(** Well-founded definitions: *)

From Stdlib Require Import Arith Wf_nat.

Create HintDb lt.

(** One can declare new well-founded relations using instances of the [WellFounded] typeclass. *)
#[local] Instance wf_nat : WellFounded lt := lt_wf.
#[local] Hint Resolve Nat.lt_succ_diag_r : lt.

(** The [by wf n lt] annotation indicates the kind of well-founded recursion we want. *)
Equations testn (n : nat) : nat by wf n lt :=
testn 0 := 0 ;
testn (S n) with testn n => {
  | 0 := S 0 ;
  | (S n') := S n' }.

(** Notations for vectors *)
Equations Derive NoConfusion NoConfusionHom for vector.

Arguments Vector.nil {A}.
Arguments Vector.cons {A} _ {n}.

Declare Scope vect_scope.
Notation " x |:| y " := (@Vector.cons _ x _ y) (at level 20, right associativity) : vect_scope.
Notation " x |: n :| y " := (@Vector.cons _ x n y) (at level 20, right associativity) : vect_scope.
Notation "[]v" := Vector.nil (at level 0) : vect_scope.
Local Open Scope vect_scope.

(** We can define functions by structural recursion on indexed datatypes like vectors. *)

Equations vapp {A} {n m} (v : vector A n) (w : vector A m) : vector A (n + m) :=
  vapp []v w := w ;
  vapp (Vector.cons a v) w := a |:| vapp v w.

(** We can also support well-founded recursion on indexed datatypes. *)

(** We show that decidable equality of the elements type implied decidable equality of vectors. *)

#[local] Instance vector_eqdec {A n} `(EqDec A) : EqDec (vector A n).
Proof. intros. intros x. induction x. left. now depelim y.
  intro y; depelim y.
  destruct (eq_dec h h0); subst. 
  destruct (IHx y). subst.
  left; reflexivity.
  right. intro. apply n0. noconf H0. constructor.
  right. intro. apply n0. noconf H0. constructor.
Defined.
Print Assumptions vector_eqdec.

(** We automatically derive the signature and subterm relation for
    vectors and prove it's well-foundedness. The signature provides
    a [signature_pack] function to pack a vector with its index. The
    well-founded relation is defined on the packed vector type. *)

Derive Subterm for vector.

(** The relation is actually called [t_subterm] as [vector] is just
    a notation for [Vector.t]. *)

Section foo.
  Context {A B : Type}.

  (** We can use the packed relation to do well-founded recursion on the vector.
      Note that we do a recursive call on a substerm of type [vector A n] which
      must be shown smaller than a [vector A (S n)]. They are actually compared
      at the packed type [{ n : nat & vector A n}]. *)

  Equations unzip {n} (v : vector (A * B) n) : vector A n * vector B n
    by wf (signature_pack v) (@t_subterm (A * B)) :=
  unzip []v := ([]v, []v) ;
  unzip (Vector.cons (x, y) v) with unzip v := {
    | pair xs ys := (Vector.cons x xs, Vector.cons y ys) }.
End foo.

(** Playing with lists and functional induction, we define a tail-recursive version
    of [rev] and show its equivalence with the "naïve" [rev]. *)

Equations app {A} (l l' : list A) : list A :=
app nil l := l;
app (cons a v) l := cons a (app v l).

#[warnings="-notation-overridden"]
Infix "++" := app (right associativity, at level 60) : list_scope.

Equations rev_acc {A} (l : list A) (acc : list A) : list A :=
rev_acc nil acc := acc;
rev_acc (cons a v) acc := rev_acc v (a :: acc).

Equations rev {A} (l : list A) : list A :=
rev nil := nil;
rev (cons a v) := rev v ++ (cons a nil).

Notation " [] " := List.nil.

Lemma app_nil : forall {A} (l : list A), l ++ [] = l.
Proof.
  intros.
  funelim (app l []); simpl. reflexivity.
  now rewrite H.
Qed.

Lemma app_assoc : forall {A} (l l' l'' : list A), (l ++ l') ++ l'' = l ++ (l' ++ l'').
Proof. intros. revert l''.
  funelim (l ++ l'); intros; simp app; trivial.
  now rewrite H.
Qed.

Lemma rev_rev_acc : forall {A} (l : list A), rev_acc l [] = rev l.
Proof.
  intros.
  replace (rev l) with (rev l ++ []) by apply app_nil.
  generalize (@nil A). 
  funelim (rev l). reflexivity.
  intros l'. simp rev_acc; trivial. rewrite H.
  rewrite app_assoc. reflexivity.
Qed.
#[local] Hint Rewrite @rev_rev_acc : rev_acc.
#[local] Hint Rewrite @app_nil @app_assoc : app.

Lemma rev_app : forall {A} (l l' : list A), rev (l ++ l') = rev l' ++ rev l.
Proof. intros. funelim (l ++ l'); simp rev app; trivial.
  now (rewrite H, <- app_assoc).
Qed.

Equations zip' {A} (f : A -> A -> A) (l l' : list A) : list A :=
zip' f nil nil := nil ;
zip' f (cons a v) (cons b w) := cons (f a b) (zip' f v w) ;
zip' f x y := nil.

Equations zip'' {A} (f : A -> A -> A) (l l' : list A) (def : list A) : list A :=
zip'' f nil nil def := nil ;
zip'' f (cons a v) (cons b w) def := cons (f a b) (zip'' f v w def) ;
zip'' f nil (cons b w) def := def ;
zip'' f (cons a v) nil def := def.

Import Vector.

(** Vectors *)

Equations vector_append_one {A n} (v : vector A n) (a : A) : vector A (S n) :=
vector_append_one nil a := cons a nil;
vector_append_one (cons a' v) a := cons a' (vector_append_one v a).

Equations vrev {A n} (v : vector A n) : vector A n :=
vrev nil := nil;
vrev (cons a v) := vector_append_one (vrev v) a.

Definition cast_vector {A n m} (v : vector A n) (H : n = m) : vector A m.
intros; subst; assumption. Defined.

Equations vrev_acc {A n m} (v : vector A n) (w : vector A m) : vector A (n + m) :=
vrev_acc nil w := w;
vrev_acc (cons a v) w := cast_vector (vrev_acc v (cons a w)) _.
(* About vapp'. *)

Record vect {A} := mkVect { vect_len : nat; vect_vector : vector A vect_len }.
Coercion mkVect : vector >-> vect.
Derive NoConfusion for vect. 

(** Splitting a vector into two parts. *)

Inductive Split {X : Type}{m n : nat} : vector X (m + n) -> Type :=
  append : ∀ (xs : vector X m)(ys : vector X n), Split (vapp xs ys).

Arguments Split [ X ].

(** We split by well-founded recursion on the index [m] here. *)

Equations split {X : Type} {m n} (xs : vector X (m + n)) : Split m n xs by wf m :=
split (m:=O) xs := append nil xs ;
split (m:=S m) (cons x xs) with split xs => {
  | append xs' ys' := append (cons x xs') ys' }.

(** The [split] and [vapp] functions are inverses. *)

Lemma split_vapp : ∀ (X : Type) m n (v : vector X m) (w : vector X n),
  let 'append v' w' := split (vapp v w) in
    v = v' /\ w = w'.
Proof.
  intros.
  funelim (vapp v w).
  destruct split. depelim xs; intuition.
  simp split in *. destruct split. simpl.
  intuition congruence.
Qed.

(* Eval compute in @zip''. *)

#[warnings="-deprecated-library-file-since-8.20"]
From Stdlib Require Import Bvector.

(** This function can also be defined by structural recursion on [m]. *)

Equations split_struct {X : Type} {m n} (xs : vector X (m + n)) : Split m n xs :=
split_struct (m:=0) xs := append nil xs ;
split_struct (m:=(S m)) (cons x xs) with split_struct xs => {
  split_struct (m:=(S m)) (cons x xs) (append xs' ys') := append (cons x xs') ys' }.

Lemma split_struct_vapp : ∀ (X : Type) m n (v : vector X m) (w : vector X n),
  let 'append v' w' := split_struct (vapp v w) in
    v = v' /\ w = w'.
Proof.
  intros. funelim (vapp v w); simp split_struct in *.
  destruct split_struct. depelim xs; intuition.
  destruct (split_struct (vapp v _)); simpl.
  intuition congruence.
Qed.

(** Taking the head of a non-empty vector. *)

Equations vhead {A n} (v : vector A (S n)) : A := 
vhead (cons a v) := a.

(** Mapping over a vector. *)

Equations vmap' {A B} (f : A -> B) {n} (v : vector A n) : vector B n :=
vmap' f nil := nil ;
vmap' f (cons a v) := cons (f a) (vmap' f v).
#[local] Hint Resolve Nat.lt_succ_diag_r : subterm_relation.
Transparent vmap'.

(** The same, using well-founded recursion on [n]. *)
Equations vmap {A B} (f : A -> B) {n} (v : vector A n) : vector B n by wf n :=
vmap f (n:=?(O)) nil := nil ;
vmap f (cons a v) := cons (f a) (vmap f v).

Transparent vmap.
Eval compute in (vmap' id (@nil nat)).
Eval compute in (vmap' id (@cons nat 2 _ nil)).

(** The image of a function. *)

Section Image.
  Context {S T : Type}.
  Variable f : S -> T.

  Inductive Imf : T -> Type := imf (s : S) : Imf (f s).

  (** Here [(f s)] is innaccessible. *)

  Equations inv (t : T) (im : Imf t) : S :=
  inv ?(f s) (imf s) := s.

End Image.

(** Working with a universe of types with an interpretation function. *)

Section Universe.

  Inductive univ : Set :=
  | ubool | unat | uarrow (from:univ) (to:univ).

  Equations interp (u : univ) : Set :=
  interp ubool := bool; interp unat := nat;
  interp (uarrow from to) := interp from -> interp to.

  Transparent interp.

  Definition interp' := Eval compute in @interp.

  Equations foo (u : univ) (el : interp' u) : interp' u :=
  foo ubool true := false ;
  foo ubool false := true ;
  foo unat t := t ;
  foo (uarrow from to) f := id ∘ f.

  Transparent foo.
  (* Eval lazy beta delta [ foo foo_obligation_1 foo_obligation_2 ] iota zeta in foo. *)

End Universe.

Equations vlast {A} {n} (v : vector A (S n)) : A by struct v :=
vlast (@cons a O _) := a ;
vlast (@cons a (S n) v) := vlast v.
Transparent vlast.

(** The parity predicate embeds a divisor of n or n-1 *)

Inductive Parity : nat -> Set :=
| even : forall n, Parity (mult 2 n)
| odd : forall n, Parity (S (mult 2 n)).

(* Eval compute in (fun n => mult 2 (S n)). *)
Definition cast {A B : Type} (a : A) (p : A = B) : B.
  intros. subst. exact a.
Defined.
  
Equations parity (n : nat) : Parity n :=
parity O := even 0 ;
parity (S n) with parity n => {
  parity (S ?(mult 2 k))     (even k) := odd k ;
  parity (S ?(S (mult 2 k))) (odd k)  := cast (even (S k)) _ }.

(** We can halve a natural looking at its parity and using the lower truncation. *)

Equations half (n : nat) : nat :=
half n with parity n => {
  half ?(S (mult 2 k)) (odd k) := k ;
  half ?(mult 2 k) (even k) := k }.

Equations vtail {A n} (v : vector A (S n)) : vector A n :=
  vtail (cons a v') := v'.

Equations diag {A n} (v : vector (vector A n) n) : vector A n :=
diag (n:=O) nil := nil ;
diag (n:=S ?(n)) (cons (@cons a n v) v') := cons a (diag (vmap vtail v')).
Transparent diag.

Definition mat A n m := vector (vector A m) n.

Equations vmake {A} (n : nat) (a : A) : vector A n :=
vmake O a := nil ;
vmake (S n) a := cons a (vmake n a).

Equations vfold_right {A : nat -> Type} {B} (f : ∀ n, B -> A n -> A (S n)) (e : A 0) {n} (v : vector B n) : A n :=
vfold_right f e nil := e ;
vfold_right f e (@cons a n v) := f n a (vfold_right f e v).

Equations vzip {A B C n} (f : A -> B -> C) (v : vector A n) (w : vector B n) : vector C n :=
vzip f nil _ := nil ;
vzip f (cons a v) (cons a' v') := cons (f a a') (vzip f v v').

Definition transpose {A m n} : mat A m n -> mat A n m :=
  vfold_right (A:=λ m, mat A n m)
  (λ m', vzip (λ a, cons a))
  (vmake n nil).

From Equations Require Import Examples.Fin.

Generalizable All Variables.

Opaque vmap. Opaque vtail. Opaque nth.

Lemma nth_vmap `(v : vector A n) `(fn : A -> B) (f : fin n) : nth (vmap fn v) f = fn (nth v f).
Proof. revert B fn. funelim (nth v f); intros; now simp nth vmap. Qed.

Lemma nth_vtail `(v : vector A (S n)) (f : fin n) : nth (vtail v) f = nth v (fs f).
Proof. funelim (vtail v); intros; now simp nth. Qed.

#[local] Hint Rewrite @nth_vmap @nth_vtail : nth.
  
Lemma diag_nth `(v : vector (vector A n) n) (f : fin n) : nth (diag v) f = nth (nth v f) f.
Proof. revert f. funelim (diag v); intros f.
  depelim f.

  depelim f; simp nth; trivial.
  rewrite H. now simp nth.
Qed.

Equations assoc (x y z : nat) : x + y + z = x + (y + z) :=
assoc 0 y z := eq_refl;
assoc (S x) y z with assoc x y z, x + (y + z) => {
assoc (S x) y z eq_refl _ := eq_refl }.

Section well_founded_recursion_and_auxiliary_function.

(** When recursive calls are made on results pattern-matching
   the output of auxiliary functions, you need enough information
   to prove that the argument of recursive calls are smaller.
   This is usually granted by the specification of the auxiliary
   function (see function pivot in the quicksort example).
   When the type of the recursive function is not informative
   enough, we can use an inspect pattern as illustrated
   in the following example. *)

Context {A : Type} (f : A -> option A) {lt : A -> A -> Prop}
 `{WellFounded A lt}.

Hypothesis decr_f : forall n p, f n = Some p -> lt p n.

(** The [inspect] definition is used to pack a value with a proof
  of an equality to itself. When pattern matching on the first component in 
  this existential type, we keep information about the origin of the pattern 
  available in the second component, the equality.  *)
Definition inspect {A} (a : A) : {b | a = b} :=
  exist _ a eq_refl.

Notation "x 'eqn:' p" := (exist _ x p) (only parsing, at level 20).

(** If one uses [f n] instead of [inspect (f n)] in the following definition,
   patterns should be patterns for the option type, but then there
   is an unprovable obligation that is generated as we don't keep information
   about the call to [f n] being equal to [Some p] to justify the recursive
   call to [f_sequence]. *)
Equations f_sequence (n : A) : list A by wf n lt :=
  f_sequence n with inspect (f n) := {
    | Some p eqn: eq1 => p :: f_sequence p;
    | None eqn:_ => List.nil
    }.

(** The following is an illustration of a theorem on f_sequence. *)
Lemma in_seq_image (n p : A) : List.In p (f_sequence n) ->
   exists k, f k = Some p.
Proof.
funelim (f_sequence n);[ | now intros abs; elim abs].
now simpl; intros [p_is_a | p_in_seq];[rewrite <- p_is_a; exists n | auto].
Qed.

End well_founded_recursion_and_auxiliary_function.

Module IdElim.
Import Sigma_Notations.
Set Equations Transparent.
Equations transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
transport P eq_refl u := u.

Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing).

Equations path_sigma {A : Type} {P : A -> Type} (u v : sigma P)
  (p : u.1 = v.1) (q : p # u.2 = v.2) : u = v := 
path_sigma (_ , _) (_ , _) eq_refl eq_refl := eq_refl.

Example foo := path_sigma_elim.
End IdElim.
