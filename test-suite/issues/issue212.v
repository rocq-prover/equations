From Stdlib Require Import List.
From Stdlib Require Import Lia ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.
#[warning="-unknown-option"] Set Asymmetric Patterns No Implicits.

Import ListNotations.

From Equations.Prop Require Import Equations.

Section list_size.
    Context {A : Type} (f : A -> nat).
    Equations list_size (l : list A) : nat :=
      {
        list_size nil := 0;
        list_size (cons x xs) := S (f x + list_size xs)
      }.
End list_size.

Section Map.
  
  Equations map_In {A B : Type}
     (l : list A) (f : forall (x : A), In x l -> B) : list B :=
  map_In nil _ := nil;
  map_In (cons x xs) f := cons (f x _) (map_In xs (fun x H => f x _)).
  
End Map.


Section Test.

  Variables (L U R : Type).

  Inductive Foo : Type :=
  | C1 : L -> Foo
  | C3 : L -> list Foo -> Foo.

  Inductive Result : Type :=
  | ULeaf : U -> Result
  | UNode : list Result -> Result.
  (* Derive NoConfusion for Result. *)

  Fixpoint rsize (r : Result) :=
    match r with
    | ULeaf a => 0
    | UNode l => S (list_size rsize l)
    end.

  Lemma In_result_rsize_leq r res :
    In r res ->
    rsize r < (list_size rsize res).
  Proof.
    funelim (list_size rsize res) => //=.
    case=> [-> | Hin]; [| have Hleq := (H r Hin)]; lia.
  Qed.



  
  Variables (Null : R) (resolve : U -> Result).

Set Equations  Debug.
  Equations? (noind) execute (initial_value : U) (foos : list Foo) : list R  :=
    {
      execute _ [] := [];
      
      execute initial_value (_ :: qs) := (complete_value (resolve initial_value)) ++ execute initial_value qs
            
          where complete_value (res : Result) : list R by wf (rsize res) :=
                  {
                    complete_value (UNode res) := 
                    concat (map_In res (fun r Hin => complete_value r)); 
      
                    complete_value (ULeaf res) := []
                  }
            
    }.

  all: do ?[by have Hleq := (In_result_rsize_leq r res Hin); lia].
  Qed.
  Print execute_unfold_clause_2_complete_value.

  
End Test.
