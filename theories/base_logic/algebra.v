(** Upstream Iris removed [iris.base_logic.algebra]: the internalized
properties of the CMRA constructions are now proved for any [Sbi] in
[iris.bi.algebra] (which is exported by [iris.bi.bi]). The only renaming is
[agree_validI] → [agree_op_invI]. This file is kept for backwards
compatibility of the module path. *)
From iris.bi Require Export algebra.
From iris.prelude Require Import options.
