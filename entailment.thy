(*<*)
theory entailment
imports QML
begin
(*>*)

text "We shall say that one property entails a second just in case it is necessarily
  true that anything that possesses the first property also possesses the second
  property."

abbreviation entails :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> (\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (infix "\<^enum>" 50)
  where "P \<^enum> Q  \<equiv> \<^bold>\<box>(\<^bold>\<forall>x. (P x) \<^bold>\<rightarrow> (Q x))" 

text "closed under entailment: any property that is entailed
by some collection of God’s essential properties is, itself, one of God’s essential
properties"

abbreviation closedunderentailment::  "((\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("closed")
  where "closed (SET) \<equiv> \<^bold>\<forall>P. \<^bold>\<forall>Q. (SET P \<^bold>\<and> (P \<^enum> Q)) \<^bold>\<rightarrow> SET Q"

(*<*)
end
(*>*)