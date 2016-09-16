(*<*)
theory individualTests
imports "../definitions/god/godessentialConst" "../definitions/entailment/individualEntailment"
(*imports "../definitions/god/godessentialConstNecessary" "../definitions/entailment/individualEntailment" *)
begin
(*>*)

axiomatization where T: T_sem

lemma andClosedGodessential:
  assumes closedGodessential: "\<lfloor>closed godessential\<rfloor>"
  shows  "\<lfloor>\<^bold>\<box>(godessential P \<^bold>\<and> godessential Q) \<^bold>\<rightarrow> godessential (\<lambda>x. P x \<^bold>\<and> Q x)\<rfloor>"
nitpick[user_axioms = true] oops
text\<open>this is not true because there is no single element in the set of godessential properties that entails P AND Q\<close>

lemma "False" nitpick[user_axioms = true] oops

(*<*)
end
(*>*)