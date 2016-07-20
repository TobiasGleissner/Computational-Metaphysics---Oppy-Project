(*<*)
theory introGodessentialConstAllWorlds
imports QML
begin
(*>*)

axiomatization where T: "T_sem"
axiomatization where S5: "S5_sem"

consts godessential :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> bool"
  
abbreviation godlike :: "\<mu> \<Rightarrow> \<sigma>" 
  where "godlike x \<equiv> \<^bold>\<forall>P. ( \<lambda> i. godessential P ) \<^bold>\<rightarrow> \<^bold>\<box> (P x)"

axiomatization 
  where godessentialex: "\<exists>P. godessential P"
  and godessentialnot: "\<exists>P. \<not> godessential P"

(*
theorem
  assumes "closed godessential"
  assumes "\<exists>P. godessential P"
  assumes "\<exists>P. \<not> godessential P"
  shows "\<forall>\<Phi>. (godessential(\<Phi>)) \<longrightarrow> (\<not>(godessential (\<^sup>\<not>\<Phi>)))"
nitpick[user_axioms] oops

theorem
  assumes "\<exists>P. godessential P \<and> godessential (\<^sup>\<not>P)"
  assumes "closed godessential"
  shows "\<forall>Q. godessential Q"
  nitpick[user_axioms] oops
*)
(*
theorem
assumes "\<lfloor>\<^bold>\<exists>x. godlike x\<rfloor>"
shows "\<exists> P. \<not> godessential P \<and> closed godessential"
nitpick[user_axioms]
oops
*)

theorem 
assumes "\<lfloor>(\<^bold>\<exists>P. \<^bold>\<not> ( \<lambda> i. godessential P) ) \<rfloor>"
assumes "closed godessential"
shows "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. godlike x)\<rfloor>"
nitpick[user_axioms] 
oops

theorem "False"
nitpick[user_axioms] oops
(*<*)
end
(*>*)
