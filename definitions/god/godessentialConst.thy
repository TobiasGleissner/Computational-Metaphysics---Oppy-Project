(*<*)
theory godessentialConst
imports "../../QML"
begin
(*>*)  
consts godessential :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"

abbreviation godlike :: "\<mu> \<Rightarrow> \<sigma>" 
  where "godlike x \<equiv> (\<^bold>\<forall>P. godessential P \<^bold>\<rightarrow> (P x))"
(*<*)
end
(*>*)
