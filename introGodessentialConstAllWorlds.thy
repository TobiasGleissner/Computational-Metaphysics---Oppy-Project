(*<*)
theory introGodessentialConstAllWorlds
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

abbreviation closedunderentailment::  "((\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> bool ) \<Rightarrow> bool" ("closed")
  where "closed (SET) \<equiv> \<forall>R. \<forall>Q. (SET (Q) \<and> \<lfloor>(Q  \<^enum> R)\<rfloor>) \<longrightarrow> SET(R)"

axiomatization where T: "T_sem"
axiomatization where S5: "S5_sem"

consts godessential :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> bool"
  
abbreviation godlike :: "\<mu> \<Rightarrow> \<sigma>" 
  where "godlike x \<equiv> \<^bold>\<forall>P. ( \<lambda> i. godessential P ) \<^bold>\<rightarrow> \<^bold>\<box> (P x)"

axiomatization 
  where godessentialex: "\<exists>P. godessential P"

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
nitpick[user_axioms]

lemma "\<lfloor>(\<^bold>\<forall>x. (\<^bold>\<forall>Q. (godessential Q) \<^bold>\<rightarrow> \<^bold>\<box>(Q x)) \<^bold>\<rightarrow> (godlike x))\<rfloor>" sledgehammer[remote_leo2]
by blast

(*<*)
end
(*>*)
