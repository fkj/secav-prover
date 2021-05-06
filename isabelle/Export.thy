theory Export
  imports Prover
begin

code_lazy_type stream

declare Stream.smember_code [code del]
lemma [code]: "Stream.smember x (y ## s) = (x = y \<or> Stream.smember x s)"
  unfolding Stream.smember_def by auto

code_identifier
  code_module Stream \<rightharpoonup> (Haskell) Stream
| code_module Export \<rightharpoonup> (Haskell) Stream

code_identifier
  code_module MaybeExt \<rightharpoonup> (Haskell) Abstract_Completeness
| code_module Abstract_Completeness \<rightharpoonup> (Haskell) Abstract_Completeness

code_printing
  constant the \<rightharpoonup> (Haskell) "MaybeExt.fromJust"
| constant Option.is_none \<rightharpoonup> (Haskell) "MaybeExt.isNothing"

code_printing code_module "MaybeExt" \<rightharpoonup> (Haskell) 
  \<open>module MaybeExt(fromJust, isNothing) where
     import Data.Maybe(fromJust, isNothing);\<close>

export_code open secavProver in Haskell

end