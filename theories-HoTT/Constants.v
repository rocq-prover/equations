Set Warnings "-notation-overridden".

From Equations Require Import Init.
From Equations.HoTT Require Import Logic DepElim EqDec Classes.
From HoTT Require Import Spaces.Nat.

(** Naturals *)
Register Basics.Overture.O as equations.nat.zero.
Register Basics.Overture.S as equations.nat.succ.
Register Basics.Overture.nat as equations.nat.type.

(* Sigma Types *)
Register Equations.Init.sigma as equations.sigma.type.
Register Equations.Init.sigmaI as equations.sigma.intro.
Register Equations.Init.pr1 as equations.sigma.pr1.
Register Equations.Init.pr2 as equations.sigma.pr2.

(** Classes *)

Register DepElim.DependentEliminationPackage as equations.depelim.class.
Register Classes.ImpossibleCall as equations.impossiblecall.class.

(** Logic parameterization *)

Derive Signature for paths.

Register Basics.Overture.paths as equations.equality.type.
Register Basics.Overture.idpath as equations.equality.refl.
Register Equations.HoTT.Logic.transport_r as equations.equality.case.
Register Equations.HoTT.Logic.paths_rect_dep_r as equations.equality.elim.

Register Classes.EqDec as equations.eqdec.class.
Register Classes.dec_eq as equations.eqdec.dec_eq.

Register Classes.UIP as equations.uip.class.
Register Classes.uip as equations.uip.uip.

Register Basics.Overture.Empty as equations.bottom.type.
Register Empty_rec as equations.bottom.case.
Register Empty_ind as equations.bottom.elim.

Register Basics.Overture.Unit as equations.top.type.
Register Basics.Overture.tt as equations.top.intro.
Register Basics.Overture.Unit_ind as equations.top.elim.

(* Should be in HoTT? *)
Register Init.Datatypes.prod as core.prod.type.
Register Init.Datatypes.pair as core.prod.intro.
Register Init.Datatypes.fst as core.prod.proj1.
Register Init.Datatypes.snd as core.prod.proj2.

Register Init.Datatypes.prod as equations.conj.type.
Register Init.Datatypes.pair as equations.conj.intro.

Register Basics.Overture.Unit as equations.unit.type.
Register Basics.Overture.tt as equations.unit.intro.

Register Init.Datatypes.prod as equations.product.type.
Register Init.Datatypes.pair as equations.product.intro.

(* FIXME not polymorphic *)
Register Classes.WellFounded as equations.wellfounded.class.
Register WellFounded.well_founded as equations.wellfounded.type.
Register Basics.Overture.Relation as equations.relation.type.
Register Relation.trans_clos as equations.relation.transitive_closure.

(* Dependent elimination constants *)

Register DepElim.solution_left as equations.depelim.solution_left.
Register DepElim.solution_left_dep as equations.depelim.solution_left_dep.
Register DepElim.solution_right as equations.depelim.solution_right.
Register DepElim.solution_right_dep as equations.depelim.solution_right_dep.

Register Classes.NoConfusionPackage as equations.noconfusion.class.
Register Classes.apply_noConfusion as equations.depelim.apply_noConfusion.

Register Classes.NoCyclePackage as equations.nocycle.class.
Register Classes.apply_noCycle_left as equations.depelim.apply_noCycle_left.
Register Classes.apply_noCycle_right as equations.depelim.apply_noCycle_right.

Register DepElim.simplification_sigma1 as equations.depelim.simpl_sigma.
Register DepElim.simplification_sigma1_dep as equations.depelim.simpl_sigma_dep.
Register DepElim.simplification_sigma1_nondep_dep as equations.depelim.simpl_sigma_nondep_dep.
Register DepElim.simplification_sigma1_dep_dep as equations.depelim.simpl_sigma_dep_dep.

Register DepElim.simplify_ind_pack as equations.depelim.simplify_ind_pack.
Register DepElim.simplify_ind_pack_inv as equations.depelim.simplify_ind_pack_inv.
Register DepElim.opaque_ind_pack_inv as equations.depelim.opaque_ind_pack_eq_inv.

Register DepElim.pack_sigma as equations.depelim.pack_sigma_eq.
Register DepElim.simplification_K_uip as equations.depelim.simpl_uip.
