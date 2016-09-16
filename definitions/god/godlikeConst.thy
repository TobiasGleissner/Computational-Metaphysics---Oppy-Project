(*<*)
theory godlikeConst
imports "../../QML"
begin
(*>*)

consts godlike :: "\<mu> \<Rightarrow> \<sigma>" 

text "there will be a collection of properties 
– ‘God’s essential properties’ – that God possesses of necessity"
abbreviation godessential :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"
  where "godessential P \<equiv> \<^bold>\<forall>x. (godlike x \<^bold>\<rightarrow> \<^bold>\<box>(P x))"

(*<*)
end
(*>*)
