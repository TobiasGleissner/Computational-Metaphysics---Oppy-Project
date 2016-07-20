(*<*)
theory collectionEntailment
imports "../QML"
begin
(*>*)

abbreviation entails :: "((\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>) \<Rightarrow> (\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (infix "\<^enum>" 50)
  where "SET \<^enum> P  \<equiv> \<^bold>\<box>(\<^bold>\<forall>x. (\<^bold>\<forall>Q. SET(Q) \<^bold>\<rightarrow> Q(x)) \<^bold>\<rightarrow> (P x))" 

abbreviation isSubset :: "((\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>) \<Rightarrow> ((\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (infix "\<^bold>\<subseteq>" 50)
  where "SET1 \<^bold>\<subseteq> SET2 \<equiv> \<^bold>\<forall>x. SET1 x \<^bold>\<rightarrow> SET2 x" 

abbreviation closedunderentailment::  "((\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("closed")
  where "closed (SET) \<equiv> \<^bold>\<forall>Q. \<^bold>\<forall>SUBSET. ((SUBSET \<^bold>\<subseteq> SET) \<^bold>\<and> (SUBSET \<^enum> Q)) \<^bold>\<rightarrow> SET Q"
(*<*) 
end
(*>*)