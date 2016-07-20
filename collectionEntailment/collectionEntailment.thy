(*<*)
theory collectionEntailment
imports "../QML"
begin
(*>*)

abbreviation entails :: "((\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>) \<Rightarrow> (\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (infix "\<^enum>" 50)
  where "SET \<^enum> P  \<equiv> \<^bold>\<box>(\<^bold>\<forall>x. (\<^bold>\<forall>Q. SET(Q) \<^bold>\<rightarrow> Q(x)) \<^bold>\<rightarrow> (P x))" 

abbreviation closedunderentailment::  "((\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("closed")
  where "closed (SET) \<equiv> \<^bold>\<forall>SUBSET. \<^bold>\<forall>R. \<^bold>\<forall>P. (((SUBSET (P) \<^bold>\<rightarrow> SET (P)) \<^bold>\<and> (SUBSET \<^enum> R))) \<^bold>\<rightarrow> SET(R)"

(*<*)
end
(*>*)