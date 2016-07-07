(*<*)
theory IntroductionTim
imports QML Main
begin
(*>*)

axiomatization where T: "T_sem"

abbreviation entails :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> (\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (infix "\<^enum>" 50)
  where "P \<^enum> Q  \<equiv> \<^bold>\<box>(\<^bold>\<forall>x. (P x) \<^bold>\<rightarrow> (Q x))" 

abbreviation closedunderentailment::  "((\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("closed")
  where "closed (P) \<equiv> \<^bold>\<forall>R. \<^bold>\<forall>Q. (P (Q) \<^bold>\<and> (Q \<^enum> R)) \<^bold>\<rightarrow> P(R)"

consts god :: "\<mu> \<Rightarrow> \<sigma>" 

abbreviation godessential :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"
  where "godessential P \<equiv> \<^bold>\<forall>x. (god x \<^bold>\<rightarrow> \<^bold>\<box>(P x))"

(*
consts NE :: "\<mu> \<Rightarrow> \<sigma>" 
  where "NE x \<equiv> \<^bold>\<box>(\<^bold>\<exists> y. x \<^bold>= y)"

axiomatization 
  where godessentialNE: "\<lfloor>godessential NE\<rfloor>"*)

theorem
assumes "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>x. god x)\<rfloor>"
shows "\<lfloor>((\<^bold>\<exists>P. \<^bold>\<not> godessential P) \<^bold>\<and> closed godessential)\<rfloor>"
using assms T  by blast

theorem 
assumes "\<lfloor>((\<^bold>\<exists>P. \<^bold>\<not> godessential P) \<^bold>\<and> closed godessential)\<rfloor>"
shows "\<lfloor>(\<^bold>\<exists>x. god x)\<rfloor>"
nitpick[satisfy, eval = "godessential" "god", card = 2, format = 2]
using assms by blast

lemma True nitpick [satisfy, user_axioms, expect = genuine] by simp
end
(*>*)
