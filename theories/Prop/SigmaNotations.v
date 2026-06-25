From Equations Require Import Init.

Set Warnings "-notation-overridden".

Module Sigma_Notations.

Notation "'Σ' x .. y , P" := (sigma (fun x => .. (sigma (fun y => P)) ..))
  (at level 10, x binder, y binder, P at level 200,
  format "'[  ' '[  ' Σ  x  ..  y ']' ,  '/' P ']'") : type_scope.

Notation "( x , .. , y , z )" :=
  (@sigmaI _ _ x .. (@sigmaI _ _ y z) ..)
      (right associativity, at level 0,
       format "( x ,  .. ,  y ,  z )") : equations_scope.

Notation "x .1" := (pr1 x) : equations_scope.
Notation "x .2" := (pr2 x) : equations_scope.

End Sigma_Notations.

Import Sigma_Notations.