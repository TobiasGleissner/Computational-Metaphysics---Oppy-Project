(*<*)
theory introCollectionGodessentialConstNecessary
imports "../definitions/god/godessentialConstNecessary" "../definitions/entailment/collectionEntailment"
begin
(*>*)

theorem 
assumes "\<lfloor>\<^bold>\<exists>x. godlike x\<rfloor>"
shows "\<lfloor>(\<^bold>\<exists>P. godessential P) \<^bold>\<and> (\<^bold>\<exists>P. \<^bold>\<not> godessential P) \<^bold>\<and> closed godessential\<rfloor>"
nitpick[user_axioms]
oops

axiomatization where S5: S5_sem

theorem 
assumes "\<lfloor>(\<^bold>\<exists>P. godessential P) \<^bold>\<and> (\<^bold>\<exists>P. \<^bold>\<not> godessential P) \<^bold>\<and> closed godessential\<rfloor>"
shows "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. godlike x)\<rfloor>"
(*sledgehammer[remote_leo2, verbose](assms S5)*)
nitpick[user_axioms]
oops

(*<*)
end
(*>*)
