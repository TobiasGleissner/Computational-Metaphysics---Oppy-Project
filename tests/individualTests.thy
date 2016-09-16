(*<*)
theory individualTests
imports introGodlikeConst
begin
(*>*)

lemma andClosedGodessential:
  assumes closedGodessential: "\<lfloor>closed godessential\<rfloor>"
  shows  "\<lfloor>\<^bold>\<box>(godessential P \<^bold>\<and> godessential Q) \<^bold>\<rightarrow> godessential (\<lambda>x. P x \<^bold>\<and> Q x)\<rfloor>"
using T by blast

lemma "False" nitpick[user_axioms = true]

(*<*)
end
(*>*)