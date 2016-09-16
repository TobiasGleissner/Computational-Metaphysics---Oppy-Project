(*<*)
theory introGodessentialConst
imports collectionEntailment
begin
(*>*)
  
abbreviation godlike :: "\<mu> \<Rightarrow> \<sigma>" 
  where "godlike x \<equiv> (\<^bold>\<forall>P. godessential P \<^bold>\<rightarrow> (P x))"

theorem
assumes "\<lfloor>\<^bold>\<exists>x. godlike x\<rfloor>"
shows "\<lfloor>(\<^bold>\<exists>P. godessential P) \<^bold>\<and> (\<^bold>\<exists>P. \<^bold>\<not> godessential P) \<^bold>\<and> closed godessential\<rfloor>"
nitpick[user_axioms]
text\<open>Counterexample: godessential is empty,
even if we say that we fix some godessential properties that 
must be there we can still have an entailed property that is not godessential so we don't get closed 
under entailment\<close>
oops

theorem 
assumes "\<lfloor>(\<^bold>\<exists>P. godessential P) \<^bold>\<and> (\<^bold>\<exists>P. \<^bold>\<not> godessential P) \<^bold>\<and> closed godessential\<rfloor>"
shows "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. godlike x)\<rfloor>"
sledgehammer[remote_leo2, verbose, timeout = 300](assms S5)
by (metis assms)

(*no contradiction*)
lemma 
assumes "\<lfloor>(\<^bold>\<exists>P. godessential P) \<^bold>\<and> (\<^bold>\<exists>P. \<^bold>\<not> godessential P) \<^bold>\<and> closed godessential\<rfloor>"
shows "False" nitpick[user_axioms] oops

(*<*)
end
(*>*)
