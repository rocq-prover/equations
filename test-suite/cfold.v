(* same example in Coq using the Equations plugin.
   Proof size is now constant instead of quadratic.,
   but program is as straightforward as in Agda. *)

From Stdlib Require Import Arith.
From Equations.Prop Require Import Equations.

From Stdlib Require Import Bool.Bool.

Set Keyed Unification.
Set Implicit Arguments.
Set Asymmetric Patterns.
#[warning="-unknown-option"] Set Asymmetric Patterns No Implicits.

Inductive type : Set :=
| Nat : type
| Bool : type
| Prod : type -> type -> type.

Inductive exp : type -> Set :=
| NConst : nat -> exp Nat
| Plus : exp Nat -> exp Nat -> exp Nat
| Eq : exp Nat -> exp Nat -> exp Bool

| BConst : bool -> exp Bool
| And : exp Bool -> exp Bool -> exp Bool
| If : forall t, exp Bool -> exp t -> exp t -> exp t

| Pair : forall t1 t2, exp t1 -> exp t2 -> exp (Prod t1 t2)
| Fst : forall t1 t2, exp (Prod t1 t2) -> exp t1
| Snd : forall t1 t2, exp (Prod t1 t2) -> exp t2.

Fixpoint typeDenote (t : type) : Set :=
  match t with
    | Nat => nat
    | Bool => bool
    | Prod t1 t2 => typeDenote t1 * typeDenote t2
  end%type.

Fixpoint expDenote t (e : exp t) : typeDenote t :=
  match e with
    | NConst n => n
    | Plus e1 e2 => expDenote e1 + expDenote e2
    | Eq e1 e2 => if eq_nat_dec (expDenote e1) (expDenote e2) then true else false

    | BConst b => b
    | And e1 e2 => expDenote e1 && expDenote e2
    | If _ e' e1 e2 => if expDenote e' then expDenote e1 else expDenote e2

    | Pair _ _ e1 e2 => (expDenote e1, expDenote e2)
    | Fst _ _ e' => fst (expDenote e')
    | Snd _ _ e' => snd (expDenote e')
  end.

Derive NoConfusion EqDec for type.
Derive Signature NoConfusion  for exp.

Equations smartplus(e1 : exp Nat)(e2: exp Nat) : exp Nat :=
  smartplus (NConst n1) (NConst n2) := NConst (n1 + n2) ;
  smartplus e1 e2 := Plus e1 e2.

Equations smarteq(e1 : exp Nat)(e2: exp Nat) : exp Bool :=
  smarteq (NConst n1) (NConst n2) := BConst (if (eq_nat_dec n1 n2) then true else false) ;
  smarteq e1 e2 := Eq e1 e2.

Equations smartand(e1 : exp Bool)(e2: exp Bool) : exp Bool :=
  smartand (BConst n1) (BConst n2) := BConst (n1 && n2) ;
  smartand e1 e2 := And e1 e2.

Equations smartif {t} (e1 : exp Bool)(e2: exp t)(e3: exp t) : exp t :=
  smartif (BConst n1) e2 e3 := if n1 then e2 else e3 ;
  smartif e1 e2 e3 := If e1 e2 e3.

Equations smartfst {t1 t2} (e: exp (Prod t1 t2)) : exp t1 :=
  smartfst (Pair e1 e2) := e1;
  smartfst e := Fst e.

Equations smartsnd {t1 t2} (e: exp (Prod t1 t2)) : exp t2 :=
  smartsnd (Pair e1 e2) := e2;
  smartsnd e := Snd e.

Equations cfold {t} (e: exp t) : exp t :=
  cfold (NConst n) := NConst n ;
  cfold (Plus e1 e2) := smartplus (cfold e1) (cfold e2);
  cfold (Eq e1 e2) := smarteq (cfold e1) (cfold e2);
  cfold (BConst x) := BConst x;
  cfold (And e1 e2) := smartand (cfold e1) (cfold e2);
  cfold (If e1 e2 e3) := smartif (cfold e1) (cfold e2) (cfold e3);
  cfold (Pair e1 e2) := Pair (cfold e1) (cfold e2);
  cfold (Fst e) := smartfst (cfold e);
  cfold (Snd e) := smartsnd (cfold e).

Lemma cfoldcorrect: forall t (e: exp t), expDenote e = expDenote (cfold e).
 intros; funelim (cfold e); simpl; intros; try reflexivity;
 repeat match goal with [ H : expDenote ?e = _ |- context[expDenote ?e]] => rewrite H end;
 try (match goal with [ |- _ = expDenote ?f] => funelim f end); simpl;
 repeat match goal with [ H : _ = cfold ?e |- _] => rewrite <- H; simpl end; try reflexivity;
 repeat match goal with [  |- context[if ?e then _ else _]] => destruct e end; try reflexivity.
Qed.

Print Assumptions cfoldcorrect.
