(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Environ
open EConstr

val derive_noConfusion_package :
  pm:Declare.OblState.t ->
  Environ.env ->
  poly:PolyFlags.t ->
  Names.inductive ->
  Names.Id.t ->
  prefix:string ->
  tactic:unit Proofview.tactic ->
  Names.Constant.t ->
  Declare.OblState.t

val derive_no_confusion_hom :
  pm:Declare.OblState.t ->
  env -> Evd.evar_map -> poly:PolyFlags.t -> Names.inductive * EInstance.t ->
  Declare.OblState.t * Declare.Proof.t option
