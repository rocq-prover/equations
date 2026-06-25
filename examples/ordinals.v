From Stdlib Require Import Arith.
From Stdlib Require Import Eqdep_dec.
From Stdlib Require Import Peano_dec.
From Stdlib Require Import List.
From Stdlib Require Import Recdef.
Set Warnings "-missing-proof-command".
(**
  Arithmétique
*)

(* Sur la soustraction (entière) *)
Lemma minus_Sn_n : forall (n:nat), (minus (S n) n) = (S 0).
Proof.
induction n; auto.
Qed.

Lemma lt_S_r : forall (n1 n2:nat),
  (lt n1 n2) -> exists (n:nat), n2 = (S n).
Proof.
destruct n2.
  intro. exfalso. apply (Nat.nlt_0_r n1). assumption.
  intro. exists n2. trivial.
Qed.

Lemma minus_lt_S : forall (n1 n2:nat),
  (lt n1 n2) -> exists (n:nat), (minus n2 n1) = (S n).
Proof.
intros. elim (lt_S_r n1 n2 H). intros n H1. rewrite H1.
exists (minus n n1). rewrite Nat.sub_succ_l.
  trivial.
  apply le_S_n. rewrite H1 in H. auto.
Qed.

(* Sur l'ordre strict 'lt' *)
Lemma lt_1_0 : forall (n:nat), (lt n 1) -> (n=0).
Proof.
destruct n.
  auto.
  intro. inversion H. exfalso. apply (Nat.nle_succ_0 (S n)). assumption.
Qed.

Lemma lt_S_case : forall (m n:nat), (lt m (S n)) -> (lt m n) \/ (m=n).
Proof.
intros m n. generalize m. induction n.
  intros. rewrite (lt_1_0 m0 H). tauto.
  destruct m0.    
    intro. auto with arith.
    intro. elim IHn with (m:=m0); auto with arith.
Qed.

Lemma not_lt_Sn_n : forall (n:nat), not (lt (S n) n).
Proof.
induction n.
  auto with arith.
  intro. auto with arith.
Qed.

(* Sur l'ordre large 'le' *)
Lemma not_le_Sn_n : forall (n:nat), not (le (S n) n).
Proof.
induction n.
  auto with arith.
  intro. auto with arith.
Qed.

(* Cas sur les entiers *)
Lemma nat_compare_case : forall (n1 n2:nat),
 (lt n1 n2) \/ (n1=n2) \/ (lt n2 n1).
Proof.
induction n1.
  destruct n2.
    tauto.
    left. auto with arith.
  destruct n2.
    right. right. auto with arith.
    elim (IHn1 n2).
      intro. left. auto with arith.
      intro. elim H.
        intro. right. left. auto.
        intro. right. right. auto with arith.
Qed.

(**
  Sur les listes
*)

(* Sur la longueur. *)
Lemma length_0_nil : forall (w:(list nat)),
  (length w)=0 -> w=nil.
destruct w.
  auto.
  intro. discriminate H.
Qed.

Lemma length_Sn_cons : forall (w:(list nat)) (n:nat),
  (length w)=(S n) -> exists (a:nat) (w':(list nat)), w = (cons a w').
destruct w.
  intros. discriminate H.
  intros. exists n. exists w. trivial.
Qed.

(* Principe d'induction sur la longueur des listes *)
Lemma list_length_ind_S : forall (P: (list nat) -> Prop),
  (P nil)
  -> (forall (n:nat), (forall (xs:(list nat)), (lt (length xs) (S n)) -> (P xs))
                      -> forall (xs:(list nat)), (length xs)=(S n) -> (P xs))
  -> forall (n:nat) (xs:(list nat)), (lt (length xs) (S n) -> (P xs)).
intros P P0 Plt. induction n.
  intros. assert (xs=nil).
    apply length_0_nil. apply lt_1_0. assumption.
    rewrite H0. assumption.
  intros. elim (lt_S_case (length xs) (S n) H).
    auto.
    intro. apply (Plt n); auto.
Qed.

Lemma list_length_ind : forall (P: (list nat) -> Prop),
  (P nil)
  -> (forall (n:nat), (forall (xs:(list nat)), (lt (length xs) (S n)) -> (P xs))
                      -> forall (xs:(list nat)), (length xs)=(S n) -> (P xs))
  -> forall (xs:(list nat)), (P xs).
intros. apply list_length_ind_S with (n:=(length xs)).
  assumption.
  assumption.
  auto with arith.
Qed.

(* Extension d'une liste avec des 0 (en tête) *)
Fixpoint zs (n:nat) : (list nat) :=
  match n with
      0 => nil
    | (S n) => (cons 0 (zs n))
  end.

Lemma zs_len: forall (n:nat), (length (zs n))=n.
induction n.
  auto.
  simpl. rewrite IHn. trivial.
Qed.

(* Complétion d'une liste en fonction d'une autre. 
   Le résultat est une liste de la longueur de la
   plus grande.                                   *)
Definition dist (w1:(list nat)) (w2:(list nat)) :=
  (minus (length w1) (length w2)).

Definition padd (w1:(list nat)) (w2:(list nat)) :=
  (app (zs (dist w2 w1)) w1).

Lemma padd_len_lt_cons : forall (w1 w2:(list nat)),
  (lt (length w1) (length w2)) 
  -> exists (w:(list nat)), (padd w1 w2)=(cons 0 w).
intros. unfold padd. unfold dist. 
elim (minus_lt_S (length w1) (length w2) H).
intros. rewrite H0. simpl. exists (app (zs x) w1). trivial.
Qed.

Lemma padd_len_le_len : forall (w1 w2:(list nat)),
  (le (length w1) (length w2))
  -> (length (padd w1 w2)) = (length w2).
intros. unfold padd. unfold dist. rewrite length_app.
rewrite zs_len.
rewrite Nat.sub_add by (exact H); reflexivity.
Qed.

Lemma padd_cons_0 : forall (w1 w2:(list nat)) (a:nat),
  (length w1) = (length w2) -> (padd w1 (cons a w2)) = (cons 0 w1).
intros. unfold padd. unfold dist. rewrite H. simpl length. 
rewrite (minus_Sn_n (length w2)). simpl. trivial.
Qed.

(**
  Sur l'accessibilité.
  Tribute to P. Casteran: 
      http://www.labri.fr/perso/casteran/Cantor/HTML/AccP.html#AccElim3
*)
Theorem AccElim2 :
forall (A B:Set) 
       (RA: A -> A -> Prop) (RB: B -> B -> Prop),
 forall (P : A -> B -> Prop),
 (forall x y,
    (forall (t : A), RA t x -> forall y', Acc RB y' -> P t y') ->
    (forall (t : B), RB t y -> P x t) -> 
    (P x y)) ->
  forall x y, Acc RA x -> Acc RB y -> P x y.
Proof.
 intros A B RA RB P H x y Ax; generalize y; clear y.
 elim Ax. clear Ax x; intros x HAccx Hrecx y Ay.
 elim Ay. clear Ay y. intros y HAccy Hrecy. apply H.
   auto.   
   auto.
Qed.

(**
  Relation d'ordre sur les listes d'entiers considérés comme des
  ordinaux (formes normales de Cantor à exposants finis).
*)
Inductive wlt : (list nat) -> (list nat) -> Prop :=
  wlt_nil : forall (a:nat)(w:(list nat)), (wlt nil (cons (S a) w))
| wlt_0_w : forall (w1 w2:(list nat)), (wlt w1 w2) -> (wlt (cons 0 w1) w2)
| wlt_w_0 : forall (w1 w2:(list nat)), (wlt w1 w2) -> (wlt w1 (cons 0 w2))
| wlt_len : forall (w1 w2:(list nat)) (a1 a2:nat),
   (length w1 < length w2) -> (wlt (cons (S a1) w1) (cons (S a2) w2))
| wlt_lt :  forall (w1 w2:(list nat)) (a1 a2:nat),
  (length w1 = length w2) -> (lt a1 a2) 
    -> (wlt (cons (S a1) w1) (cons (S a2) w2))
| wlt_wlt : forall (w1 w2:(list nat)) (a:nat),
  (length w1 = length w2) ->  (wlt w1 w2) 
    -> (wlt (cons (S a) w1) (cons (S a) w2)).

(* 'nil' est minimal *)
Lemma not_wlt_nil : forall (w:(list nat)), 
  not (wlt w nil).
induction w.
  intro. inversion H.
  case a.
   intro. inversion H. auto.
   intro. intro. inversion H.
Qed.

(* Lemmes d'inversion *)
Lemma wlt_0_w_inv: forall (w1 w2:(list nat)),
  (wlt (cons 0 w1) w2) -> (wlt w1 w2).
induction w2.
  intros. absurd (wlt (cons 0 w1) nil).
    apply (not_wlt_nil (cons 0 w1)).
    assumption.
  intro. inversion H.
    assumption.
    apply wlt_w_0. auto.
Qed.

Lemma wlt_w_0_inv: forall (w1 w2:(list nat)),
  (wlt w1 (cons 0 w2)) -> (wlt w1 w2).
induction w1.
  intros. inversion H. assumption.
  intros. inversion H. 
    apply wlt_0_w. auto.
    assumption.
Qed.

(* Autres résultats négatifs *)
Lemma not_wlt_len_left : forall (w1 w2:(list nat)) (a:nat),
  (le (length w2) (length w1)) -> not (wlt (cons (S a) w1) w2).
induction w2.

  intros. apply not_wlt_nil.

  intros. destruct a.
    intro. absurd (wlt (cons (S a0) w1) w2).
      apply IHw2. 
        apply Nat.le_trans with (m:=(length (cons 0 w2))).
          auto with arith.
          assumption.
        apply wlt_w_0_inv. assumption.
    intro. inversion H0.
      assert (lt (length (cons (S a) w2)) (length w2)).
        apply Nat.le_lt_trans with (m := (length w1)); assumption.
        apply (not_lt_Sn_n (length w2)). assumption.      
      rewrite H4 in H. apply (not_le_Sn_n (length w2)); assumption.
      rewrite H4 in H. apply (not_le_Sn_n (length w2)); assumption.
Qed.

Lemma not_wlt_Sn_0 : forall (w1 w2:(list nat)) (a:nat),
  (length w1) = (length w2) -> not (wlt (cons (S a) w1) (cons 0 w2)).
intros. intro. inversion H0. 
  apply (not_wlt_len_left w1 w2 a). 
    rewrite H. auto with arith.
    apply wlt_w_0_inv. assumption.  
Qed.

Lemma not_wlt_len: forall (w1 w2:(list nat)) (a:nat),
  (length w2 <= length w1) -> not (wlt (cons (S a) w1) w2).
induction w2.
  intros. intro. exfalso. apply (not_wlt_nil (cons (S a) w1)). assumption.
  intro. case a.
    intro. intro. apply IHw2 with (a:=a0).
      apply Nat.le_trans with (m:=(length (cons 0 w2))).
        simpl. auto with arith.
        assumption.
      apply wlt_w_0_inv. assumption.
    intros. intro. inversion H0.
      apply (Nat.lt_irrefl (length w1)).
        simpl in H. apply Nat.lt_trans with (m:=(length w2)); assumption.
      rewrite H4 in H. apply (Nat.nle_succ_diag_l (length w2)). assumption.
      rewrite H4 in H. apply (Nat.nle_succ_diag_l (length w2)). assumption.
Qed. 

(* Invariance de 'wlt' pour la complétion à 0 (en tête) *)
Lemma wlt_wlt_zs_right : forall (n:nat) (w1 w2:(list nat)),
  (wlt w1 w2) -> (wlt w1 (app (zs n) w2)).
induction n.
  auto.
  intros. simpl. apply wlt_w_0. auto.
Qed.

Lemma wlt_zs_wlt_right : forall (n:nat) (w1 w2:(list nat)),
  (wlt w1 (app (zs n) w2)) -> (wlt w1 w2).
induction n.
  auto.
  simpl. intros. apply IHn. apply wlt_w_0_inv. assumption.
Qed.

Lemma wlt_wlt_zs_left : forall (n:nat) (w1 w2:(list nat)),
  (wlt w1 w2) -> (wlt (app (zs n) w1) (w2)).
induction n.
  auto.
  intros. simpl. apply wlt_0_w. auto.
Qed.     

(* Caractérisation en fonction de la longueur:
   si '(wlt w1 w2)' et '#w2 < #w1' alors 'w1' commence par des 0 *)
Lemma wlt_gt_length : forall (w1 w2:(list nat)),
  (wlt w1 w2) -> (lt (length w2) (length w1))
  -> exists (n:nat) (w:(list nat)),
       (w1 = (app (zs n) w))
       /\ (length w)=(length w2)
       /\ (wlt w w2).
induction w1 as [| a w1 IHw1]; [intros w2 _ []%Nat.nlt_0_r |].
intros w2 H Hl; simpl in Hl; apply <-Nat.succ_le_mono in Hl.
destruct a as [| a].
- apply Nat.le_lteq in Hl as [Hl | Hl].
  + apply wlt_0_w_inv in H; specialize (IHw1 w2 H Hl) as [n [w' [H'1 [H'2 H'3]]]].
    now exists (S n); exists w'; split; [rewrite H'1 | split].
  + exists (S 0); exists w1; split; [reflexivity | split]; [now symmetry |].
    exact (wlt_0_w_inv _ _ H).
- now exfalso; apply not_wlt_len_left with (2 := H).
Qed.
   
(**
   Restriction de l'ordre aux listes de même longueur.
   (avec complémentation possible à 0): 
   c'est l'ordre lexicographique.
*)
(* La relation sur les listes de même longueur *)
Inductive wlt_pad : (list nat) -> (list nat) -> Prop :=
  wlt_pad_len : forall (a:nat) (w1 w2:(list nat)),
    (le (length w1) (length w2)) ->
     (wlt_pad (padd  w1 (cons (S a) w2)) (cons (S a) w2))
| wlt_pad_lt : forall (a1 a2:nat) (w1 w2:(list nat)),
    (length w1) = (length w2) -> (lt a1 a2) ->
     (wlt_pad (cons (S a1) w1) (cons (S a2) w2))
| wlt_pad_wlt_pad : forall (a:nat) (w1 w2:(list nat)),
    (length w1) = (length w2) -> (wlt_pad w1 w2) ->
     (wlt_pad (cons a w1) (cons a w2)).

(* Relations entre l'ordre sur toute liste et l'ordre restreint. *)
Lemma wlt_wlt_pad : forall (w1 w2:(list nat)),
  (length w1) = (length w2) -> (wlt w1 w2)
  -> (wlt_pad w1 w2).
intros w1 w2. generalize w1. clear w1. induction w2.

  intros. exfalso. apply (not_wlt_nil w1). assumption.

  destruct w1.

    intros. discriminate H.       

    intros. inversion H0.
    (* 1: wlt_0_w *)
    destruct a.
      apply wlt_pad_wlt_pad.
        auto.
        apply IHw2.
          auto.
          apply wlt_w_0_inv. assumption. 
      rewrite <- (padd_cons_0 w1 w2 a). 
        apply wlt_pad_len. injection H. intro. rewrite H5. auto with arith.
        auto.
    (* 2: wlt_w_0 *)
    destruct n.    
      apply wlt_pad_wlt_pad.
        auto with arith.
        apply IHw2.
          auto with arith.
          apply wlt_w_0_inv. apply wlt_0_w_inv. rewrite <- H1 in H0. assumption.
      exfalso. apply (not_wlt_Sn_0 w1 w2 n). 
        auto with arith.
        rewrite <- H1 in H0. assumption.
    (* 3 *)
    exfalso. apply (Nat.lt_irrefl (length w2)). injection H.
    intro. rewrite H6 in H2. assumption.
    (* 4 *)
    apply wlt_pad_lt.
      auto with arith.
      assumption.
    (* 5 *)
    apply wlt_pad_wlt_pad.  
      auto with arith.
      apply IHw2.
        auto with arith.
        assumption.
Qed.

Lemma wlt_wlt_pad_zs : forall (w1 w2:(list nat)),
  (length w1) < (length w2) -> (wlt w1 w2)
  -> (wlt_pad (padd w1 w2) w2).
intros. apply wlt_wlt_pad. 
  apply padd_len_le_len. auto with arith.
  apply wlt_wlt_zs_left. assumption. 
Qed.
  
(**
  Accessibilité pour l'ordre restreint.
*)
Lemma Acc_wlt_pad_ind : forall (n:nat),
  (forall (w:(list nat)), (lt (length w) (S n)) -> Acc wlt_pad w) 
    -> forall (w:(list nat)), (length w)=(S n) -> Acc wlt_pad w. 
intros. elim (length_Sn_cons w n H0). intros a H1. elim H1. clear H1.
intros w' H1. rewrite H1. rewrite H1 in H0. clear H1. generalize H0. 
pattern a, w'.
apply AccElim2 with (RA:=lt) (RB:=wlt_pad).
 
  intros a' w'' H1 H2 H3. apply Acc_intro. intros w''' H4.
  inversion H4.   

    elim (padd_len_lt_cons  w1 (cons (S a0) w'')).
      intros w0 H9. rewrite H9. apply H1.  
        rewrite <- H5. auto with arith.    
        apply H.    
          assert (lt (length (cons 0 w0)) (S (S n))).        
            rewrite <- H9. rewrite padd_len_le_len.
              rewrite H5. rewrite H3. auto with arith.
              simpl. auto with arith.
            auto with arith.
          rewrite <- H9. rewrite padd_len_le_len. 
            rewrite H5. assumption.
            simpl. auto with arith.
      simpl. auto with arith.

    apply H1.
      rewrite <- H5. auto with arith.
      apply H.
        rewrite H8. rewrite <- H3. auto with arith.
      simpl. rewrite H8. auto.

    apply H2.
      assumption.
      simpl. rewrite H8. auto.

  apply lt_wf.

  apply H.
    rewrite <- H0. auto with arith.

Qed.

Lemma Acc_wlt_pad_nil : (Acc wlt_pad nil).
apply Acc_intro. intros. inversion H.
Qed.

Lemma Acc_wlt_pad : forall (w:(list nat)), (Acc wlt_pad w).
induction w using list_length_ind.
  apply Acc_wlt_pad_nil.
  apply Acc_wlt_pad_ind with (n:=n); assumption.
Qed.

(**
  De l'accessibilté pour l'ordre restreint à l'accessibilité
  pour l'ordre sur tout liste.
*)
Lemma Acc_wlt_zs_Acc_wlt : forall (n:nat) (w:(list nat)),
  (Acc wlt (app (zs n) w)) -> (Acc wlt w).
intros. apply Acc_intro. intros w' H0. apply H.
apply wlt_wlt_zs_right. assumption.
Qed.

Lemma Acc_wlt_Acc_wlt_zs : forall (n:nat) (w:(list nat)),
  (Acc wlt w) -> (Acc wlt (app (zs n) w)).
intros. apply Acc_intro. intros w' H0. apply H. 
apply wlt_zs_wlt_right with (n:=n). assumption.
Qed.

Lemma Acc_wlt_pad_Acc_wlt : forall (w:(list nat)),
  (Acc wlt_pad w) -> (Acc wlt w).
intros. elim H. intros w' H0 H1. apply Acc_intro.
intros w'' H2. elim (nat_compare_case (length w'') (length w')).
  (* #w'' < #w' *)
  intro. apply Acc_wlt_zs_Acc_wlt with (n:=(dist w' w'')).
  apply H1. apply wlt_wlt_pad_zs; assumption.
  (* #w'' = #w4 \/ #w' < #w'' *)
  intro. elim H3.
    (* #w'' = #w' *)
    intro. apply H1. apply wlt_wlt_pad; assumption.
    (* #w' < #w'' *)
    intro. elim (wlt_gt_length w'' w' H2 H4). intros a H5.
    elim H5. intro w0. intro. decompose [and] H6.
    rewrite H7. apply Acc_wlt_Acc_wlt_zs. apply H1.
    apply wlt_wlt_pad; assumption.
Qed.

(**
  L'ordre sur toute liste est bien fondé !
*)
Theorem Acc_wlt : forall (w:(list nat)), (Acc wlt w).
intro. apply Acc_wlt_pad_Acc_wlt.
apply Acc_wlt_pad.
Qed.

(**
   Sur wlt
*)
Lemma wlt_len_gen : forall (w1 w2:list nat) (a:nat),
  (lt (length w1) (length (cons (S a) w2))) -> (wlt w1 (cons (S a) w2)).
induction w1.
  intros. apply wlt_nil.
  intros. destruct a. 
    apply wlt_0_w. apply IHw1. apply Nat.lt_trans with (m:=(length (cons 0 w1))).
      auto with arith.
      assumption.
    apply wlt_len. auto with arith.
Qed.

Lemma wlt_lt_gen : forall (a1 a2:nat) (w1 w2:list nat),
  (length w1) = (length w2) -> (lt a1 a2) 
    -> (wlt (cons a1 w1) (cons a2 w2)).
intros. destruct a2.
  exfalso. apply (Nat.nlt_0_r a1). assumption.
  destruct a1.
    apply wlt_0_w. apply wlt_len_gen. rewrite H. auto with arith.
    apply wlt_lt; auto with arith.
Qed.

Lemma wlt_wlt_gen : forall (a:nat) (w1 w2:list nat),
  (length w1) = (length w2) -> (wlt w1 w2) 
  -> (wlt (cons a w1) (cons a w2)).                                 
destruct a.
  intros. apply wlt_0_w. apply wlt_w_0. assumption.
  intros. apply wlt_wlt; assumption.
Qed.

Lemma wlt_wf_ind : forall (P: (list nat) -> Prop),
  (forall (w1:list nat), (forall (w2:list nat), (wlt w2 w1) -> P w2) -> P w1)
  -> forall (w:list nat), P w.
intros. apply well_founded_ind with (R:=wlt).
  unfold well_founded. apply Acc_wlt.
  intros. apply H. assumption.
Qed.

(* Utilitaire pour la définition des ordres *)
Definition make_mwlt (A:Set) (m : A -> list nat) (a1 a2:A) :=
  (wlt (m a1) (m a2)).
 
(** Un ordre basé sur une mesure ordinale est bien fondé *)
Lemma Acc_wlt_eq : 
  forall (A:Set) (m: A -> list nat) (w:list nat) (x:A) , 
    w = (m x) -> (Acc (fun x1 x2 : A => wlt (m x1) (m x2)) x).
induction w using wlt_wf_ind. intros. apply Acc_intro. intros.
  apply H with (w2:=(m y)).
    rewrite H0. assumption.    
    trivial.
Qed.

Lemma Acc_mwlt : forall (A:Set) (m: A -> list nat),
  forall (x:A), (Acc (fun x1 x2 => (wlt (m x1) (m x2))) x).
intros. apply Acc_wlt_eq with (w:=(m x)). trivial.
Qed.

(**
  Applications avec Program Fixpoint
*)
From Stdlib Require Program.Wf.

(* Tactique pour les preuves de bonne fondation. *)
Ltac by_Acc_mwlt mwlt := 
  unfold Wf.MR; unfold well_founded; intros; unfold mwlt; apply Acc_mwlt.

(* Ordre lexicographique sur les entiers *)
Definition wm_natxnat (xy:nat*nat) :=
  match xy with
    (x,y) => (cons x (cons y nil))
  end.

Definition lex_natxnat :=
  (make_mwlt (nat*nat) wm_natxnat).

Lemma lex_natxnat_fst : forall (x1 y1 x2 y2:nat),
  (lt x1 x2) -> (lex_natxnat (x1,y1) (x2,y2)).
intros. unfold lex_natxnat. unfold make_mwlt. simpl.
apply wlt_lt_gen; auto.
Qed.

Lemma lex_natxnat_snd : forall (x y1 y2:nat),
  (lt y1 y2) -> (lex_natxnat (x,y1) (x,y2)). 
intros. unfold lex_natxnat. unfold make_mwlt. simpl.
apply wlt_wlt_gen.
  auto.
  apply wlt_lt_gen; auto.
Qed.

Program Fixpoint ack_like (xy:nat*nat) {wf lex_natxnat xy} : nat :=
  match xy with
    (0, y) => (S y)
  | (S x, 0) => (ack_like (x, S 0))
  | (S x, S y) => (ack_like (x, (x + y))) +  (ack_like (S x, y))
  end.

Obligation 1.
apply lex_natxnat_fst.
auto with arith.
Qed.

Obligation 2.
apply lex_natxnat_fst.
auto with arith.
Qed.

Obligation 3. 
apply lex_natxnat_snd.
auto with arith.
Qed.

Obligation 4.
by_Acc_mwlt lex_natxnat.
Defined.

Program Fixpoint ack (xy:nat*nat) {wf lex_natxnat xy} : nat :=
  match xy with
    (0, y) => (S y)
  | (S x, 0) => (ack (x, S 0))
  | (S x, S y) => (ack (x, ack (S x, y)))
  end.
 
Obligation 1.
apply lex_natxnat_fst.
auto with arith.
Qed.

Obligation 2.
apply lex_natxnat_snd.
auto with arith.
Qed.

Obligation 3.
apply lex_natxnat_fst. inversion Heq_xy. auto with arith.
Qed.

Obligation 4.
by_Acc_mwlt lex_natxnat.
Defined.

(* Ordre lexicographique sur les longueurs des listes *)
Definition wm_listxlist (A:Set) (xys: list A * list A) :=
  match xys with
    (xs,ys) => (wm_natxnat (length xs, length ys))
  end.

Definition lex_listxlist (A:Set) :=
  (make_mwlt (list A * list A) (wm_listxlist A)).

Parameter ltb : nat -> nat -> bool.

Program Fixpoint merge (xys: list nat * list nat) {wf (lex_listxlist nat) xys} : list nat :=
  match xys with
      (nil, ys) => ys
    | (xs, nil) => xs
    | (cons x xs, cons y ys) =>
      if (ltb x y) then (cons x (merge (xs, (cons y ys))))
      else (cons y (merge ((cons x xs), ys)))
  end.

Obligation 1.
unfold lex_listxlist. unfold make_mwlt. simpl. 
apply wlt_lt_gen; auto with arith.
Qed.

Obligation 2.
unfold lex_listxlist. unfold make_mwlt. simpl. apply wlt_wlt_gen.
  auto.
  apply wlt_lt_gen; auto with arith.
Qed.

Obligation 4.
by_Acc_mwlt lex_natxnat.
Defined.

(* Ordre sur les listes d'entiers:
     ordre lexicographique sur la taille et le premier élément *)
Definition m_list (xs:list nat) :=
  match xs with
      nil => nil
    | (cons x xs) => (cons (length (cons x xs)) (cons x nil))
  end.

Definition lt_list  :=
  (make_mwlt (list nat) m_list).

Program Fixpoint sum_list (xs:list nat) {wf lt_list xs} : nat :=
  match xs with
      nil => 0
    | (cons 0 xs) => (sum_list xs)
    | (cons (S x) xs) => S (sum_list (cons x xs))
  end.

Obligation 1.
unfold lt_list. unfold make_mwlt. simpl. destruct xs.
  simpl. apply wlt_nil.
  simpl. apply wlt_lt_gen; auto with arith.
Qed.

Obligation 2.
unfold lt_list. unfold make_mwlt. simpl. apply wlt_wlt_gen.
  auto.
  apply wlt_lt_gen; auto with arith.
Qed.

Obligation 3.
by_Acc_mwlt lex_natxnat.
Defined.

(* Analogue sur les listes de listes *)
Definition m_listlist (A:Set) (xss : list (list A)) :=
  match xss with
      nil => nil
    | (cons xs _) => (cons (length xss) (cons (length xs) nil))
  end.

Definition lt_listlist (A:Set) (xss yss : list (list A)) :=
  (wlt (m_listlist A xss) (m_listlist A yss)).

Parameter A:Set.

Program Fixpoint list_concat (xss : list (list A))
        {wf (lt_listlist A) xss} : list A :=
  match xss with
      nil => nil
    | (cons nil xss) => (list_concat xss)
    | (cons (cons x xs) xss) => (cons x (list_concat (cons xs xss)))
  end.

Obligation 1.
unfold lt_listlist. destruct xss.
  simpl. apply wlt_nil.
  simpl. apply wlt_lt_gen; auto with arith.
Qed.

Obligation 2.
unfold lt_listlist. simpl. apply wlt_wlt_gen.
  auto.
  apply wlt_lt_gen; auto with arith.
Qed.

Obligation 3.
by_Acc_mwlt lex_natxnat.
Defined.

(* Sur la longueur des listes *)
Definition mw_list (A:Set) (xs: list A) :=
  (cons (length xs) nil).

Definition lt_len_list (A:Set) :=
  (make_mwlt (list A) (mw_list A)).

Program Fixpoint bubble (xs:list nat) {wf (lt_len_list nat) xs} : list nat :=
  match xs with
      nil => nil
    | (cons x nil) => (cons x nil)
    | (cons x1 (cons x2 xs)) =>
      if (ltb x1 x2) then (cons x1 (bubble (cons x2 xs)))
      else (cons x2 (bubble (cons x1 xs)))
  end.

Obligation 1.
unfold lt_len_list. unfold make_mwlt. unfold mw_list. simpl. 
apply wlt_lt_gen; auto with arith.
Qed.

Obligation 2.
unfold lt_len_list. unfold make_mwlt. unfold mw_list. simpl. 
apply wlt_lt_gen; auto with arith.
Qed.

Obligation 3. 
by_Acc_mwlt lt_len_list.
Defined.

(* Le peigne *)
Inductive btree (A:Set) : Set :=
  Empty : (btree A)
| Node : (btree A) -> A -> (btree A) -> (btree A).

Arguments  Empty {A}.
Arguments Node [A] _ _ _.

Fixpoint btree_size (A:Set) (bt:btree A) :=
  match bt with
      Empty => 0
    | (Node bt1 x bt2) => S (plus (btree_size A bt1) (btree_size A bt2))
  end.

Definition m_btree (A:Set) (bt:btree A) :=
  match bt with
      Empty => nil
    | (Node bt1 x bt2) => (cons (btree_size A bt) (cons (btree_size A bt1) nil))
  end.

Definition lt_btree (A:Set) (bt1 bt2:btree A) :=
  (wlt (m_btree A bt1) (m_btree A bt2)).

Program Fixpoint to_list (bt:btree A)
        {wf (lt_btree A) bt} : list A :=
  match bt with
      Empty => nil
    | (Node Empty x bt) => (cons x (to_list bt))
    | (Node (Node bt1 x1 bt2) x2 bt3) => (to_list (Node bt1 x1 (Node bt2 x2 bt3)))
  end.

Obligation 1.
unfold lt_btree. destruct bt.
  simpl. apply wlt_nil.
  simpl. apply wlt_lt_gen; auto with arith.
Qed.

Obligation 2.
  unfold lt_btree. simpl. rewrite <-Nat.add_succ_comm. simpl.
  rewrite Nat.add_assoc. apply wlt_wlt_gen.
  auto.
  apply wlt_lt_gen; auto with arith.
Qed.

Obligation 3.
by_Acc_mwlt lt_btree.
Defined.

(* Theory *)
Axiom g1 : nat -> nat.
Axiom g2 : nat -> nat -> nat.
Axiom g3 : nat -> nat -> nat.
Axiom g4 : nat -> nat -> nat.
Axiom g5 : nat -> nat -> nat -> nat.
Axiom g6 : nat -> nat -> nat -> nat.
Axiom g7 : nat -> nat -> nat -> nat.
Axiom h1 : nat -> nat -> nat -> nat.
Axiom h2 : nat -> nat -> nat -> nat.
Axiom h3 : nat -> nat -> nat -> nat -> nat -> nat.

Definition wm_nat3 (xyz:nat * nat * nat) :=
  match xyz with
      (0, y, 0) => nil
    | (0, y, S z) => (cons (S z) nil)
    | (S x, 0, z) => (cons (S x) (cons 0 nil))
    | (S x, S y, z) => (cons (S x) (cons (S y) nil))
  end.

Definition rlex_nat3 :=
  (make_mwlt (nat * nat * nat) wm_nat3).

Program Fixpoint f (xyz : nat * nat * nat) {wf rlex_nat3 xyz} : nat :=
  match xyz with
      (0, y, 0) => (g1 y)
    | (0, y, S z) => (h1 y z (f (0, (g2 y z), z)))
    | (S x, 0, z) => (h2 x z (f (x, (g3 x z), (g4 x z))))
    | (S x, S y, z) =>
         (h3 x y z (f (x, (g5 x y z), (g6 x y z)))
                   (f (S x, y, (g7 x y z))))
  end.

Lemma rlex_nat3_1 : forall (y z m : nat),
  (rlex_nat3 (0, y, z) (0, m, S z)).
intros. unfold rlex_nat3. unfold make_mwlt. destruct z.
  simpl. apply wlt_nil.
  simpl. apply wlt_lt; auto with arith.
Qed.

Lemma rlex_nat3_2 : forall (x z m1 m2 : nat),
  (rlex_nat3 (x, m1, m2) (S x, 0, z)).
unfold rlex_nat3. unfold make_mwlt. destruct x.
  destruct m2.
    simpl. apply wlt_nil.
    simpl. apply wlt_len; auto with arith.
  intros. destruct m1.
    simpl. apply wlt_lt; auto with arith.
    simpl. apply wlt_lt; auto with arith.
Qed.

Lemma rlex_nat3_3 : forall (x y z m1 m2 : nat),
  (rlex_nat3 (x, m1, m2) (S x, S y, z)).
unfold rlex_nat3. unfold make_mwlt. destruct x.                     
  intros. destruct m2.
    simpl. apply wlt_nil.
    simpl. apply wlt_len; auto with arith.
  intros. destruct m1.
    simpl. apply wlt_lt; auto with arith.
    simpl. apply wlt_lt; auto with arith.
Qed.

Lemma rlex_nat3_4 : forall (x y z m : nat),
  (rlex_nat3 (S x, y, m) (S x, S y, z)).
Proof.
unfold rlex_nat3. unfold make_mwlt. destruct y.
  intros. simpl. apply wlt_wlt. 
    auto with arith.
    simpl. apply wlt_0_w. apply wlt_nil.
  intros. simpl. apply wlt_wlt.
    auto with arith.
    apply wlt_lt; auto with arith.
Qed.

Obligation 1.
apply rlex_nat3_1. 
Qed.

Obligation 2.
apply rlex_nat3_2.
Qed.

Obligation 3.
apply rlex_nat3_3.
Qed.

Obligation 4.
apply rlex_nat3_4.
Qed.
 
Obligation 5.
by_Acc_mwlt wm_nat3.
Defined.

(* Bootstrap *)
Parameter eqb : nat -> nat -> bool.

Program Fixpoint listordi (xsys : list nat * list nat) {wf (lex_listxlist nat) xsys} : bool :=
  match xsys with
    (_, nil) => false
  | (xs, (cons 0 ys)) => (listordi (xs, ys))
  | (nil, (cons (S y) ys)) => true
  | ((cons 0 xs), (cons (S y) ys)) => (listordi (xs, (cons (S y) ys)))
  | ((cons (S x) xs), (cons (S y) ys)) =>
     (orb (ltb (length xs) (length ys))
	  (andb (eqb (length xs) (length ys))
		(orb (ltb x y) (listordi (xs, ys)))))
  end.

Obligation 1.
unfold lex_listxlist. unfold make_mwlt. simpl.
apply wlt_wlt_gen.
  auto.
  apply wlt_lt_gen; auto with arith.
Qed.

Obligation 2.
unfold lex_listxlist. unfold make_mwlt. simpl.
apply wlt_lt_gen; auto with arith.
Qed.

Obligation 3.
unfold lex_listxlist. unfold make_mwlt. simpl.
apply wlt_lt_gen; auto with arith.
Qed.
 
Obligation 4.  
by_Acc_mwlt lex_natxnat.
Defined.

(* Dershowitz/Manna: "counting tips of binary trees" *)

Fixpoint list_btree_size (A:Set) (bts:list (btree A)) : nat :=
  match bts with
      nil => 0
    | (cons bt bts) => (plus (btree_size A bt) (list_btree_size A bts))
  end.

Definition wm_list_btree (A:Set) (bts:list (btree A)) : (list nat) :=
  (cons (list_btree_size A bts) (cons (length bts) nil)).

Definition lt_list_btree (A:Set) :=
  (make_mwlt (list (btree A)) (wm_list_btree A)).

Program Fixpoint count_tips (bts:(list (btree A))) 
        {wf (lt_list_btree A) bts} : nat :=
  match bts with
      nil => 0
    | (cons Empty bts) => S (count_tips bts)
    | (cons (Node bt1 x bt2) bts) => (count_tips (cons bt1 (cons bt2 bts)))
  end.

Obligation 1.
unfold lt_list_btree. unfold make_mwlt. unfold wm_list_btree. 
simpl. apply wlt_wlt_gen.
  auto.
  apply wlt_lt_gen; auto with arith.
Qed.

Obligation 2.
unfold lt_list_btree. unfold make_mwlt. unfold wm_list_btree.
apply wlt_lt_gen.
  auto.
  simpl. rewrite Nat.add_assoc. auto with arith.
Qed.

Obligation 3.
by_Acc_mwlt lt_list_btree.
Defined.

Print Assumptions count_tips.
