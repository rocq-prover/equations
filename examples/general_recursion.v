(** * General recursive functions

  This file explores a way to formalize general recursive functions
  without worrying about termination proofs, counters or monads.

  The definitions are actually defined by well-founded recursion on the
  total relation (which isn't well-founded).  Using fueling of the
  accessibility proof, we can however compute with these definitions
  inside Coq and reason on them independently of the termination
  proof. *)


(* begin hide *)
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
From Equations.Prop Require Import Equations.

From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Program.
From Stdlib Require Import Psatz.
From Stdlib Require Import Nat.
#[warnings="-warn-library-file-stdlib-vector"]
From Stdlib Require Import Vectors.VectorDef.
From Stdlib Require Import Relations.

Set Keyed Unification.
Set Equations Transparent.
(* end hide *)

(** The total relation. *)
Definition total_relation {A : Type} : A -> A -> Prop := fun x y => True.

(** We assume an inconsistent axiom here, one should be added function per function. *)
Axiom wf_total_init : forall {A}, WellFounded (@total_relation A).
#[local] 
Remove Hints wf_total_init : typeclass_instances.

(** We fuel it with some Acc_intro constructors so that definitions relying on it
    can unfold a fixed number of times still. *)
#[local] 
Instance wf_total_init_compute : forall {A}, WellFounded (@total_relation A).
  exact (fun A => Acc_intro_generator 10 wf_total_init).
Defined.

Set Warnings "-solve_obligation_error".

(** Now we define an obviously non-terminating function. *)
Equations? nonterm (n : nat) : nat by wf n (@total_relation nat) :=
  nonterm 0 := 0;
  nonterm (S n) := S (nonterm (S n)).
Proof.
  (* Every pair of arguments is in the total relation: so
     [total_relation (S n) (S n)] *) red.
  constructor.
Defined.
  Local Obligation Tactic := idtac.
  (** The automation has a little trouble here as it assumes
      well-founded definitions implicitely.  We show the second
      equation: [nonterm (S n) = S (nonterm (S n))] using the
      unfolding equation. *)
  Next Obligation.
    intros. now rewrite nonterm_unfold_eq at 1.
  Defined.

  (* Note this is a dangerous rewrite rule, so we should remove it from the hints *)
  (* Print Rewrite HintDb nonterm. *)

  (** Make nonterm transparent anyway so we can compute with it *)
  Transparent nonterm.

(** We can compute with it (for closed natural numbers) *)
Definition at_least_five (n : nat) : bool :=
  match n with
  | S (S (S (S (S x)))) => true
  | _ => false
  end.

Transparent wf_total_init_compute.

(** Indeed it unfolds enough so that [at_least_five] gives back a result. *)

Example check_10 := eq_refl : at_least_five (nonterm 10) = true.
Example check_0 := eq_refl : at_least_five (nonterm 0) = false.

(** The elimination principle completely abstracts away from the
    termination argument as well *)
Lemma nonterm_ge n : n <= nonterm n.
Proof.
  funelim (nonterm n).
  reflexivity.
  lia.
Defined.

(** We can go as far as defining the (call-by-name) Y combinator and computing with it. *)
Section Y.
  Context {A : Type}.
  Equations? Y (f : A -> A) : A by wf f (@total_relation (A -> A)) :=
  Y f := f (Y f).
  Proof.
    (* Every pair of arguments is in the total relation: so
     [total_relation f f] *) red. constructor.
  Defined.

  Obligation Tactic := idtac.
  (** The automation has a little trouble here as it assumes
      well-founded definitions implicitely.  We show the second
      equation: [nonterm (S n) = S (nonterm (S n))] using the
      unfolding equation. *)
  Next Obligation.
    intros. now rewrite Y_unfold_eq at 1.
  Defined.
End Y.

(** Using [Y], we can easily define any general recursive function. *)
Definition fact :=
  Y (fun (fact : nat -> nat) (x : nat) =>
       match x with
       | 0 => 1
       | S n => S n * fact n
       end).
#[warnings="-abstract-large-number"]
Check eq_refl : fact 8 = 40320.

(** [Y] is only good in call-by-name or call-by-need, so we switch to Haskell *)

Extraction Language Haskell.
Recursive Extraction fact.

(*
y :: (a1 -> a1) -> a1
y x =
  x (y x)

fact :: Nat -> Nat
fact =
  y (\fact0 x -> case x of {
                  O -> S O;
                  S n -> mul (S n) (fact0 n)})

*)

(** Let's define an efficient version whose termination is not entirely obvious. *)
Definition factN :=
  Y (fun (fact : N -> N) (x : N) =>
       match x with
       | N0 => 1%N
       | Npos n => (Npos n * fact (Pos.pred_N n))%N
       end).

(** [1001!] is pretty large. *)
Definition fact1001 :=
 402789647337170867317246136356926989705094239074925347176343710340368450911027649612636252695456374205280468598807393254690298539867803367460225153499614535588421928591160833678742451354915921252299285456946271396995850437959540645019696372741142787347450281325324373824456300226871609431497826989489109522725791691167945698509282421538632966523376679891823696900982075223188279465194065489111498586522997573307838057934994706212934291477882221464914058745808179795130018969175605739824237247684512790169648013778158661520384916357285547219660337504067910087936301580874662367543921288988208261944834178369169805682489420504038334529389177845089679546075023305854006141256288633820079940395329251563788399404652902154519302928365169452383531030755684578503851488154092323576150311569325891190105926118761607100286827930472944913272420825078912158741589850136017030887975452922434889688775883386977825215904423682478943313806072144097432418695807412571292308739802481089407002523955080148184062810447564594783139830113821372260474145316521647368313934670783858482781506915288378941348078689691815657785305896912277993200639858696294199549107738635599538328374931258525869323348477334798827676297868823693023377418942304272267800509765805435653787530370118261219994752588866451072715583785495394684524593296728611334955079882857173250037068541860372512693170819259309411027837176612444692649174536429745421086287708588130082168792750697158901737130221751430550976429258055277255676893874108456870904122902259417224707137723406125811549952159629766771063079472679280213882978523785424760309678138268708239764925768714349554665438389311198715040908077757086900159389712443987670244241787904585093011546861502058550090914877900852701619648229332192401075747543562989953271508977501771085759521631427816116191761031257454497039673414248149210836002497114107565960458576525212556159634975715552638678172137468172843066451093984443636560722213668172225585711566558134467392654185460222589723312097599987253417831473939565071006344352518096564427781204200068323913056897090916602712260306869786107237077572445866572945760977721639408338430009976028970539150822336553856613962747814621747092348996915755983464741082000337526945990059365493439921937093368896754791416759604324895514660325913157843796039917819613717350380997781225472000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000%N.

(** We can still compute with our [Y] combinator *)
Time Check (@eq_refl _ (fact1001) <: factN 1001 = fact1001).

(** It takes [0.8sec] using [vm_compute]. *)

(** An alternative is to use the total relation directly. *)
#[obligations]
Equations factN' (n : N) : N by wf n (@total_relation N) :=
| N0 => 1;
| Npos n => (Npos n * factN' (Pos.pred_N n)).
Next Obligation. constructor. Defined.

(** Unsurprisingly, this computes just as well *)

Time Check (@eq_refl _ (fact1001) <: factN' 1001 = fact1001).

(** It takes [0.8sec] using [vm_compute] as well. *)

(** [factN'] also makes sense in a strict/call-by-value language like OCaml. *)

Extraction Language OCaml.
Extraction factN'.

(*

(** val factN' : n -> n **)

let rec factN' = function
| N0 -> Npos XH
| Npos p -> N.mul (Npos p) (let y = Pos.pred_N p in factN' y)

*)
