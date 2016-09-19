(*<*)
theory individualTests
imports "../definitions/god/godessentialConst" "../definitions/entailment/individualEntailment"
(*imports "../definitions/god/godessentialConstNecessary" "../definitions/entailment/individualEntailment" *)
begin
(*>*)

axiomatization where T: T_sem

text\<open>Check: If two Properties are necessarily included in a closed collection of properties, then the Property
   of having both Properties is also in the collection.
This is not true because there is not necessarily a single property in the collection that entails P AND Q\<close>

lemma andClosedGodessential:
  assumes closedGodessential: "\<lfloor>closed godessential\<rfloor>"
  shows  "\<lfloor>\<^bold>\<box>(godessential P \<^bold>\<and> godessential Q) \<^bold>\<rightarrow> godessential (\<lambda>x. P x \<^bold>\<and> Q x)\<rfloor>"
nitpick[user_axioms = true] oops


lemma "False" nitpick[user_axioms = true] oops

(*<*)
end
(*>*)