From Equations.Prop Require Import Classes EqDec DepElim NoConfusion Tactics.

(** Standard instances. *)

Derive EqDec for unit bool nat.

#[export]
Instance prod_eqdec {A B} `(EqDec A) `(EqDec B) : EqDec (prod A B).
Proof. eqdec_proof. Defined.

#[export]
Polymorphic Instance sum_eqdec {A B} `(EqDec A) `(EqDec B) : EqDec (A + B).
Proof. eqdec_proof. Defined.

#[export]
Polymorphic Instance list_eqdec {A} `(EqDec A) : EqDec (list A).
Proof. eqdec_proof. Defined.

Local Set Equations With UIP.

#[export]
Polymorphic Instance sigma_uip {A B} `(UIP A) `(forall x, UIP (B x)) : UIP {x : A & B x}.
Proof.
  red. intros [x p] [y q]. repeat (simplify * || intro). reflexivity.
Defined.

#[export]
Polymorphic Instance sigma_eqdec {A B} `(EqDec A) `(forall x, EqDec (B x)) : EqDec {x : A & B x}.
Proof.
  eqdec_proof.
Defined.

Polymorphic Definition eqdec_sig@{i} {A : Type@{i}} {B : A -> Type@{i}}
            `(EqDec A) `(forall a, EqDec (B a)) :
  EqDec (sigma B).
Proof.
  intros. intros [x0 x1] [y0 y1].
  case (eq_dec x0 y0). intros ->. case (eq_dec x1 y1). intros ->. left. reflexivity.
  intros. right. red. apply simplification_sigma2_uip@{i Set}. apply n.
  intros. right. red. apply simplification_sigma1@{i Set}.
  intros e _; revert e. apply n.
Defined.

#[export] 
Existing Instance eqdec_sig.

Polymorphic Definition uip_sig@{i} {A : Type@{i}} {B : A -> Type@{i}}
            `(UIP A) `(forall a, UIP (B a)) :
  UIP (sigma@{i} B).
Proof.
  intros. intros x y <-. destruct x.
  refine (eq_simplification_sigma1_dep_dep@{i Set} _ _ _ _ _).
  intros e'. destruct (uip eq_refl e'). simpl.
  intros e'. destruct (uip eq_refl e'). constructor.
Defined.

#[export]
Existing Instance uip_sig.
