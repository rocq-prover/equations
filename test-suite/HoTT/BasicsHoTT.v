(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)
From Equations Require Import CoreTactics.
From Equations Require Import HoTT.All Equations.HoTT.WellFounded.
Require Import Stdlib.Unicode.Utf8.
Require HoTT.Basics.Overture.
From HoTT Require Import Types.Bool HoTT.Spaces.Nat HoTT.Spaces.List.Core.

Local Open Scope nat_scope.

Set Equations Transparent.
Equations neg (b : Bool) : Bool :=
neg true := false ;
neg false := true.

Lemma neg_inv : forall b, neg (neg b) = b.
Proof. intros b. funelim (neg b); auto. Qed.

Inductive le : nat -> nat -> Set :=
| le_0 n : le 0 (S n)
| le_S n m : le n m -> le (S n) (S m).

Derive Signature for le.

Equations congS {x y : nat} (p : x = y) : S x = S y :=
congS 1 := 1.
  
(* Equations antisym {x y : nat} (p : le x y) (q : le y x) : x = y := *)
(* antisym (le_S n m p) (le_S ?(m) ?(n) q) := congS (antisym p q). *)


Module TestF.

  Equations? f (n : nat) : nat :=
  f 0 := 42 ;
  f (S m)  with f m :=
  {
    f (S m) IH := _
  }.
  Proof. refine IH. Defined.

End TestF.

#[local]
Instance eqsig {A} (x : A) : Signature (x = x) A (fun a => x = a) := sigmaI _ x.

Module WithUIP.
Set Equations With UIP.
Polymorphic Axiom uip : forall A, UIP A.
Local Existing Instance uip.


Equations K {A} (x : A) (P : x = x -> Type) (p : P idpath) (H : x = x) : P H :=
K x P p idpath := p.
End WithUIP.
(* Test Equations WithUIP. should be off, setting is local to the module *)

Equations eq_sym {A} (x y : A) (H : x = y) : y = x :=
eq_sym x _ idpath := idpath.

Equations eq_trans {A} (x y z : A) (p : x = y) (q : y = z) : x = z :=
eq_trans x _ _ idpath idpath := idpath.

Section FilterDef.
  Context {A} (p : A -> Bool).

  Equations filter (l : list A) : list A :=
  filter nil := nil ;
  filter (cons a l) with p a => {
                         | true := a :: filter l ;
                         | false := filter l }.

End FilterDef.

Inductive incl {A} : Relation (list A) :=
  stop : incl nil nil 
| keep {x : A} {xs ys : list A} : incl xs ys -> incl (x :: xs)%list (x :: ys)%list
| skip {x : A} {xs ys : list A} : incl xs ys -> incl (xs) (x :: ys)%list.

Global Transparent filter.

Equations sublist {A} (p : A -> Bool) (xs : list A) : incl (filter p xs) xs :=
sublist p nil := stop ;
sublist p (cons x xs) with p x := {
  | true := keep (sublist p xs) ;
  | false := skip (sublist p xs) }.

(* Print Assumptions sublist. *)
Declare Scope vect_scope.

Inductive vector@{i | Set <= i} (A : Type@{i}) : nat -> Type@{i} :=
| nil : vector A 0
| cons {n} : A -> vector A n -> vector A (S n).
Arguments vector A%_type_scope n%_nat_scope.
Arguments nil {A}.
Arguments cons {A%_type_scope} {n%_nat_scope} a v%_vect_scope.

Notation " x |:| y " := (@cons _ _ x y) (at level 20, right associativity) : vect_scope.
Notation " x |: n :| y " := (@cons _ n x y) (at level 20, right associativity) : vect_scope.
Notation "[]v" := (@nil _) (at level 0) : vect_scope.
(* Derive Subterm for nat.  *)
Derive Signature NoConfusion for vector.

(*Show Obligation Tactic.*)

Derive Subterm for vector.

Axiom F : Funext.
#[local] Existing Instance F.

#[local] Existing Instance lt_wf.

Equations testn (n : nat) : nat by wf n WellFoundedInstances.lt :=
testn 0 := 0 ;
testn (S n) with testn n => {
  | 0 := S 0 ;
  | (S n') := S n' }.

Local Open Scope vect_scope.
Reserved Notation "x ++v y" (at level 60).

From HoTT Require Import Classes.implementations.peano_naturals.
(* Require Import HoTT.Classes.interfaces.canonical_names. *)

Equations vapp {A} {n m} (v : vector A n) (w : vector A m) : vector A (n + m)%nat :=
{ []v ++v w := w ;
  (cons a v) ++v w := cons a (v ++v w) }
where "x ++v y" := (vapp x y).

(* Print Assumptions vapp. *)
(* Ltac Equations.Init.solve_noconf_hom ::= idtac. *)
Set Universe Minimization ToSet.
Derive NoConfusionHom for vector.
Unset Universe Minimization ToSet.
From Equations Require Import HoTT.Tactics.

#[local] Instance vector_eqdec@{i +|+} {A : Type@{i}} {n} `(EqDec@{i} A) : EqDec (vector A n).
Proof.
  intros. intros x. intros y. induction x.
  - left. now depelim y.
  - depelim y.
    pose proof (Classes.eq_dec a a0).
    dependent elimination X as [inl idpath|inr Ha].
    -- specialize (IHx v).
       dependent elimination IHx as [inl idpath|inr neq].
       --- left; reflexivity.
       --- right. simplify *. now apply neq.
    -- right; simplify *. now apply Ha.
Defined.

Section foo.
  Context {A B : Type}.
  
  Equations unzipv {n} (v : vector (A * B) n) : vector A n * vector B n
   by wf (signature_pack v) (@vector_subterm (A * B)) :=
  unzipv []v := ([]v, []v) ;
  unzipv ((x, y) |:| v) with unzipv v := {
    | pair xs ys := (cons x xs, cons y ys) }.
End foo.

Global Typeclasses Transparent vector_subterm.

Equations nos_with (n : nat) : nat by wf n :=
nos_with O := O ;
nos_with (S m) with nos_with m := {
  | O := S O ;
  | S n' := O }.

Set Universe Minimization ToSet.

Equations equal (n m : nat) : (n = m) + (n <> m) :=
equal O O := inl idpath ;
equal (S n) (S m) with equal n m => {
  equal (S n) (S ?(n)) (inl idpath) := inl idpath ;
  equal (S n) (S m) (inr p) := inr (λ{ | idpath => p idpath }) } ;
equal x y := inr _.

Notation "[]" := (@List.Core.nil _) (at level 0) : list_scope.
Local Open Scope list_scope.

Equations app_with {A} (l l' : list A) : list A :=
app_with [] l := l ;
app_with (a :: v) l with app_with v l => {
  | vl := a :: vl }.

Equations plus' (n m : nat) : nat :=
plus' O n := n ; 
plus' (S n) m := S (plus' n m).

Equations head A (default : A) (l : list A) : A :=
head A default [] := default ;
head A default (a :: v) := a.

Equations tail {A} (l : list A) : list A :=
tail [] := [] ;
tail (a :: v) := v.

Equations app' {A}    (l l' : list A) : (list A) :=
app' [] l := l ;
app' (a :: v) l := a :: (app' v l).

Global Transparent app'.

Notation  " x +++ y " := (@app' _ x y%list)  (at level 60, right associativity).

Equations rev_acc {A} (l : list A) (acc : list A) : list A :=
rev_acc [] acc := acc;
rev_acc (a :: v) acc := rev_acc v (a :: acc).

Equations rev {A} (l : list A) : list A :=
rev [] := [];
rev (a :: v) := rev v +++ (a :: []).

Lemma app'_nil : forall {A : Type} (l : list A), l +++ [] = l.
Proof.
  intros.
  funelim (app' l []); auto.
  now rewrite X.
Qed.

Lemma app'_assoc : forall {A} (l l' l'' : list A), (l +++ l') +++ l'' = app' l (app' l' l'').
Proof. intros. revert l''.
  funelim (l +++ l'); intros; simp app'; trivial.
  now rewrite X.
Qed.

Tactic Notation "myreplace" constr(c) "with" constr(d) "by" tactic(tac) :=
  let H := fresh in
  assert (H : c = d) by try tac; [rewrite H; clear H].

Lemma rev_rev_acc : forall {A} (l : list A), rev_acc l [] = rev l.
Proof.
  intros. myreplace (rev l) with (rev l +++ []) by (symmetry; apply app'_nil).
  generalize (@List.Core.nil A).
  funelim (rev l).
  - intros. reflexivity.
  - intros l'. autorewrite with rev_acc. rewrite X.
    rewrite app'_assoc. reflexivity.
Qed.

#[local] Hint Rewrite @rev_rev_acc : rev_acc.

Lemma app'_funind : forall {A} (l l' l'' : list A), (l +++ l') +++ l'' = app' l (app' l' l'').
Proof.
  intros.
  funelim (l +++ l'); simp app'; trivial.
  rewrite X; auto.
Qed.

#[local] Hint Rewrite @app'_nil @app'_assoc : app'.

Lemma rev_app' : forall {A} (l l' : list A), rev (l +++ l') = rev l' +++ rev l.
Proof. intros. funelim (l +++ l'); simp rev app'; trivial.
  now (rewrite X, <- app'_assoc).
Qed.

Equations zip' {A} (f : A -> A -> A) (l l' : list A) : list A :=
zip' f [] [] := [] ;
zip' f (a :: v) (b :: w) := f a b :: zip' f v w ;
zip' f x y := [].

Equations zip'' {A} (f : A -> A -> A) (l l' : list A) (def : list A) : list A :=
zip'' f [] [] def := [] ;
zip'' f (a :: v) (b :: w) def := f a b :: zip'' f v w def ;
zip'' f [] (b :: w) def := def ;
zip'' f (a :: v) [] def := def.

Equations vector_append_one {A n} (v : vector A n) (a : A) : vector A (S n) :=
vector_append_one nil a := cons a nil;
vector_append_one (cons a' v) a := cons a' (vector_append_one v a).

Equations vrev {A n} (v : vector A n) : vector A n :=
vrev nil := nil;
vrev (cons a v) := vector_append_one (vrev v) a.

Definition cast_vector {A n m} (v : vector A n) (H : n = m) : vector A m.
intros. destruct H; assumption. Defined.

Require HoTT.Classes.interfaces.naturals HoTT.Classes.interfaces.abstract_algebra
        HoTT.Classes.tactics.ring_quote HoTT.Classes.tactics.ring_tac.

Equations? vrev_acc {A n m} (v : vector A n) (w : vector A m) : vector A (n + m) :=
vrev_acc nil w := w;
vrev_acc (cons (n:=n) a v) w := cast_vector (vrev_acc v (cons a w)) _.
Proof. clear.
  induction n.
  - simpl. constructor.
  - simpl. cbn. now rewrite IHn.
Defined.

Set Primitive Projections.
Record vect {A} := mkVect { vect_len : nat; vect_vector : vector A vect_len }.
Coercion mkVect : vector >-> vect.

Derive NoConfusion for vect.

Inductive Split {X : Type}{m n : nat} : vector X (m + n) -> Type :=
  append : ∀ (xs : vector X m)(ys : vector X n), Split (vapp xs ys).

Arguments Split [ X ].

(* Eval compute in @app'. *)
(* About nil. About vector. *)
(* Set Equations Debug. *)
Set Private Polymorphic Universes.
Equations split {X : Type} {m n : nat} (xs : vector X (add m n)) : Split m n xs by wf m :=
  split (m:=0) xs := append nil xs;
  split (m:=m .+1) (cons x xs) with split xs => {
    | append xs' ys' := append (cons x xs') ys' }.
(* Minimization could do a bit better here *)
Example test_split' := @split@{_ _ _ _}.

(* Definition split_lightu@{u0 u1 u2 | u0 < u1, u1 < u2} := @split@{u0 u1 u1 u2 u1}.*)

(* 2 universes: Set < i (type of splitset) < j (universe of the type) *)
Equations splitSet {X : Set} {m n : nat} (xs : vector X (add m n)) : Split m n xs by wf m :=
  splitSet (m:=0) xs := append nil xs;
  splitSet (m:=m .+1) (cons x xs) with splitSet xs => {
    | append xs' ys' := append (cons x xs') ys' }.
Definition test_splitSet := @splitSet@{_ _}.

Section SplitSetParam.
  Context {X : Set}.
  Obligation Tactic := idtac.
  (* Here, just 1 universe for the universe of Set. *)
  Equations splitSetParam {m n : nat} (xs : vector X (add m n)) : Split m n xs by wf m :=
  splitSetParam (m:=0) xs := append nil xs;
  splitSetParam (m:=m .+1) (cons x xs) with splitSetParam xs => {
    | append xs' ys' := append (cons x xs') ys' }.
  Next Obligation. solve_rec. Qed.
End SplitSetParam.

Definition test_splitSetParam := @splitSetParam@{_}.

Notation "( x , .. , y , z )" :=
  (@sigmaI _ _ x .. (@sigmaI _ _ y z) ..)
      (right associativity, at level 0,
       format "( x ,  .. ,  y ,  z )") : equations_scope.

Global Set Default Goal Selector "1".
Axiom cheat : forall {A}, A.
Notation plus := add.
Definition eta_vector@{i j k} {A : Type@{i}} (P : forall n : nat, vector@{i} A n -> Type@{j}) :
  forall (n : nat) (v : vector@{i} A n),
    paths@{k} (match v return Type@{j} with
    | nil => P 0 nil
    | cons n a v => P _ (cons a v)
    end) (P n v).
Proof.
  now destruct v.
Defined.

Lemma split' {X : Type} {m n} (xs : vector X (add m n)) : Split m n xs.
Proof.
  eassert ?[ty].
  revert m n xs. fix IH 3. intros m n xs.
  refine (match xs as xs' in @vector _ k return
                (match xs' as xs'' in vector _ n' return Type with
                 | nil => ((0, nil) = (plus m n, xs)) -> Split m n xs
                 | @cons _ n' x' xs'' =>
                   (S n', cons x' xs'') = (plus m n, xs) -> Split m n xs
                 end)
          with
          | nil => _
          | cons n x xs => _
          end).
  destruct m as [|m'].
  + simpl. simplify *.
    apply (append nil nil).
  + simplify *.
  + destruct m as [|m']; simpl.
    simplify *. simpl. apply (append nil (x |: n :| xs)).
    simplify *. simpl.
    specialize (IH m' n0 xs).
    rewrite (eta_vector (fun nv (v : vector X nv) => (nv, v) = (plus m' n0, xs) -> Split m' n0 xs)) in IH.
    specialize (IH idpath). destruct IH.
    refine (append (cons x xs) ys).
  + rewrite (eta_vector (fun nv v => (nv, v) = (plus m n, xs) -> Split m n xs)) in X0.
    apply (X0 idpath).
Defined.
Extraction Inline apply_noConfusion Empty_ind.

Register sigma as core.sig.type.

(* Extraction split'. *)

Lemma split_vapp : ∀ (X : Type) m n (v : vector X m) (w : vector X n),
  let 'append v' w' := split (vapp v w) in
    v = v' /\ w = w'.
Proof.
  intros.
  funelim (vapp v w); simp split; trivial; auto.
  destruct split; simp split.
  dependent elimination X as [pair idpath idpath].
  split; constructor.
Qed.

(* Eval compute in @zip''. *)

Equations split_struct {X : Type} {m n} (xs : vector X (plus m n)) : Split m n xs :=
split_struct (m:=0) xs := append nil xs ;
split_struct (m:=(S m)) (cons x xs) with split_struct xs => {
  split_struct (m:=(S m)) (cons x xs) (append xs' ys') := append (cons x xs') ys' }.
Transparent split_struct.
Lemma split_struct_vapp : ∀ (X : Type) m n (v : vector X m) (w : vector X n),
  let 'append v' w' := split_struct (vapp v w) in
    v = v' /\ w = w'.
Proof.
  intros. funelim (vapp v w); simp split_struct in *; try easy.
  destruct (split_struct (v ++v w)); simpl.
  dependent elimination X as [pair idpath idpath]; easy.
Qed.

Equations vhead {A n} (v : vector A (S n)) : A := 
vhead (cons a v) := a.

Equations vmap' {A B} (f : A -> B) {n} (v : vector A n) : vector B n :=
vmap' f nil := nil ;
vmap' f (cons a v) := cons (f a) (vmap' f v).

#[local] Hint Resolve lt_n_Sn : subterm_relation.

Equations vmap {A B} (f : A -> B) {n} (v : vector A n) : vector B n by wf n :=
vmap f nil := nil ;
vmap f (cons a v) := cons (f a) (vmap f v).

Transparent vmap.

Transparent vmap'.
(* Eval compute in (vmap' id (@Vnil nat)). *)
(* Eval compute in (vmap' id (@cons nat 2 _ Vnil)). *)

(* Eval compute in @vmap'. *)

Section Image.
  Context {S T : Type}.
  Variable f : S -> T.

  Inductive Imf : T -> Type := imf (s : S) : Imf (f s).

  Equations inv (t : T) (im : Imf t) : S :=
  inv ?(f s) (imf s) := s.

End Image.

Section Universe.

  Inductive univ : Set :=
  | ubool | unat | uarrow (from:univ) (to:univ).

  Equations  interp (u : univ) : Set :=
  interp ubool := Bool; interp unat := nat;
  interp (uarrow from to) := interp from -> interp to.

  (* Eval compute in interp. *)

  Transparent interp.

  Definition interp' := Eval compute in @interp.

  Equations foo (u : univ) (el : interp' u) : interp' u :=
  foo ubool true := false ;
  foo ubool false := true ;
  foo unat t := t ;
  foo (uarrow from to) f := f.

  Transparent foo.
  (* Eval lazy beta delta [ foo foo_obligation_1 foo_obligation_2 ] iota zeta in foo. *)

End Universe.

(* Eval compute in (foo ubool false). *)
(* Eval compute in (foo (uarrow ubool ubool) negb). *)
(* Eval compute in (foo (uarrow ubool ubool) id). *)

Inductive foobar : Set := bar | baz.

Equations bla (f : foobar) : Bool :=
bla bar := true ;
bla baz := false.

(* Eval simpl in bla. *)

Lemma eq_trans_eq A x : @eq_trans A x x x idpath idpath = idpath.
Proof. reflexivity. Qed.

Section vlast.
  Context {A : Type}.
  Equations vlast {n} (v : vector A (S n)) : A by wf (signature_pack v) (@vector_subterm A) :=
  vlast (cons a (n:=O) nil) := a ;
  vlast (cons a (n:=S n) v) := vlast v.
End vlast.
(* Transparent vlast. *)
(* Definition testvlast : 4 = (vlast (cons 2 (cons 5 (cons 4 nil)))) := idpath. *)

(* Fixpoint vapp {A n m} (v : vector A n) (w : vector A m) : vector A (n + m) := *)
(*   match v with *)
(*     | nil => w *)
(*     | cons a v' => cons a (vapp v' w) *)
(*   end. *)


(* Eval compute in (split (vapp Vnil (cons 2 Vnil))). *)
(* Eval compute in (split (vapp (cons 3 Vnil) (cons 2 Vnil))). *)

(* Recursive Extraction split. *)
(* Transparent split. *)
(* Eval cbv beta iota zeta delta [ split split_obligation_1 split_obligation_2  ] in @split. *)

Equations mult (n m : nat) : nat :=
mult O m := 0 ; mult (S n) m := mult n m + m.

Transparent mult.

(* Equations mult' (n m acc : nat) : nat := *)
(* mult' O m acc := acc ; mult' (S n) m acc := mult' n m (n + acc). *)

Inductive Parity : nat -> Set :=
| even : forall n, Parity (mult 2 n)
| odd : forall n, Parity (S (mult 2 n)).

(* Eval compute in (fun n => mult 2 (S n)). *)
Definition cast {A B : Type} (a : A) (p : A = B) : B.
  intros. destruct p. exact a.
Defined.

Equations parity (n : nat) : Parity n :=
parity O := even 0 ;
parity (S n) with parity n => {
  parity (S ?(mult 2 k))     (even k) := odd k ;
  parity (S ?(S (mult 2 k))) (odd k)  := cast (even (S k)) _ }.
Next Obligation.
  cbn. apply cheat.
Defined.

Equations half (n : nat) : nat :=
half n with parity n => {
  half ?(S (mult 2 k)) (odd k) := k ;
  half ?(mult 2 k) (even k) := k }.

Equations vtail {A n} (v : vector A (S n)) : vector A n :=
vtail (cons a v') := v'.

(** Well-founded recursion: note that it's polymorphic recursion in a sense:
    the type of vectors change at each recursive call. It does not follow
    a canonical elimination principle in this nested case. *)

Equations diag {A n} (v : vector (vector A n) n) : vector A n by wf n :=
diag nil := nil ;
diag (cons (cons a v) v') := cons a (diag (vmap vtail v')).

(** The computational content is the right one here: only the vector is
    matched relevantly, not its indices, which could hence
    disappear. *)

(* Extraction diag. *)

(** It can be done structurally as well but we're matching on the index now. *)
Equations diag_struct {A n} (v : vector (vector A n) n) : vector A n :=
diag_struct (n:=O) nil := nil ;
diag_struct (n:=(S _)) (cons (cons a v) v') := cons a (diag_struct (vmap vtail v')).

Definition mat A n m := vector (vector A m) n.

Equations vmake {A} (n : nat) (a : A) : vector A n :=
vmake O a := nil ;
vmake (S n) a := cons a (vmake n a).

Equations vfold_right {A : nat -> Type} {B} (f : ∀ n, B -> A n -> A (S n)) (e : A 0) {n} (v : vector B n) : A n :=
vfold_right f e nil := e ;
vfold_right f e (cons a v) := f _ a (vfold_right f e v).

Equations vzip {A B C n} (f : A -> B -> C) (v : vector A n) (w : vector B n) : vector C n :=
vzip f nil _ := nil ;
vzip f (cons a v) (cons a' v') := cons (f a a') (vzip f v v').

Definition transpose {A m n} : mat A m n -> mat A n m :=
  vfold_right (A:=λ m, mat A n m)
  (λ m', vzip (λ a, cons a))
  (vmake n nil).

(* Lemma vfold_right_e {A : Type} {B} {n} (f : ∀ n', B' -> vector (vector A 0) n' -> vector (vector A 0) (S n')) *)
(*   (e : vector (vector A 0) n) v : vfold_right f (vmake n Vnil) v =  *)
(* Typeclasses eauto :=. *)


Inductive fin : nat -> Set :=
| fz : forall {n}, fin (S n)
| fs : forall {n}, fin n -> fin (S n).
Derive Signature NoConfusion NoConfusionHom for fin.

Generalizable All Variables.

Opaque vmap. Opaque vtail.

Equations nth {A : Type} {n} (v : vector A n) (f : fin n) : A :=
nth (cons a v) fz := a ;
nth (cons a v) (fs f) := nth v f.

Lemma nth_vmap {A B n} (v : vector A n) (fn : A -> B) (f : fin n) : nth (vmap fn v) f = fn (nth v f).
Proof. revert B fn. funelim (nth v f); intros; now simp nth vmap. Qed.

Lemma nth_vtail `(v : vector A (S n)) (f : fin n) : nth (vtail v) f = nth v (fs f).
Proof. funelim (vtail v). intros; (* FIXME universe bug with [now simp nth] *) now autorewrite with nth. Qed.

#[local] Hint Rewrite @nth_vmap @nth_vtail : nth.
  
(* Lemma diag_nth `(v : vector (vector A n) n) (f : fin n) : nth (diag v) f = nth (nth v f) f. *)
(* Proof. revert f. funelim (diag v); intros f. *)
(*   depelim f. *)

(*   depelim f; simp nth; trivial. *)
(*   rewrite H. now simp nth. *)
(* Qed. *)

Infix "+" := plus.
Equations assoc (x y z : nat) : x + y + z = x + (y + z) :=
assoc 0 y z := idpath;
assoc (S x) y z with assoc x y z, x + (y + z) => {
assoc (S x) y z idpath _ := idpath }.

(*About assoc_elim.*)
