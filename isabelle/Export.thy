theory Export
  imports Prover
begin

code_lazy_type stream

declare Stream.smember_code [code del]
lemma [code]: "Stream.smember x (y ## s) = (x = y \<or> Stream.smember x s)"
  unfolding Stream.smember_def by auto

code_printing
  constant the \<rightharpoonup> (Haskell) "MaybeExt.fromJust"
| constant Option.is_none \<rightharpoonup> (Haskell) "MaybeExt.isNothing"

code_printing code_module "MaybeExt" \<rightharpoonup> (Haskell) 
  \<open>module MaybeExt(fromJust, isNothing) where
     import Data.Maybe(fromJust, isNothing);\<close>

code_identifier
  code_module Stream \<rightharpoonup> (Haskell) Prover
| code_module Prover \<rightharpoonup> (Haskell) Prover
| code_module Export \<rightharpoonup> (Haskell) Prover
| code_module MaybeExt \<rightharpoonup> (Haskell) Prover
| code_module Abstract_Completeness \<rightharpoonup> (Haskell) Prover

definition \<open>secavTreeCode \<equiv> i.mkTree (\<lambda>r s. Some (effect r s)) rules\<close>
definition \<open>secavProverCode \<equiv> \<lambda>x . secavTreeCode ([], x)\<close>

export_code open secavProverCode in Haskell

end