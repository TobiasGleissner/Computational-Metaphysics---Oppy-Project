(*<*)
theory introGodessentialConstNecessary
imports collectionEntailment
begin
(*>*)
  
abbreviation godlike :: "\<mu> \<Rightarrow> \<sigma>" 
  where "godlike x \<equiv> \<^bold>\<box>(\<^bold>\<forall>P. godessential P \<^bold>\<rightarrow> (P x))"

theorem
assumes "\<lfloor>\<^bold>\<exists>x. godlike x\<rfloor>"
shows "\<lfloor>(\<^bold>\<exists>P. godessential P) \<^bold>\<and> (\<^bold>\<exists>P. \<^bold>\<not> godessential P) \<^bold>\<and> closed godessential\<rfloor>"
nitpick[user_axioms]
oops

theorem 
assumes "\<lfloor>(\<^bold>\<exists>P. godessential P) \<^bold>\<and> (\<^bold>\<exists>P. \<^bold>\<not> godessential P) \<^bold>\<and> closed godessential\<rfloor>"
shows "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. godlike x)\<rfloor>"
(*sledgehammer[remote_leo2, verbose, timeout = 300](assms S5)*)
(*nitpick[user_axioms, timeout = 300]*)
oops

(*<*)
end
(*>*)