(*<*)
theory tests
imports introGodessentialConstAllWorlds
begin
(*>*)

(*collection entails test*)
consts prop1 :: "(\<mu> \<Rightarrow> \<sigma>)"
consts prop2 :: "(\<mu> \<Rightarrow> \<sigma>)"

lemma
  "\<lfloor>(\<lambda>P. (P = prop1) \<or> (prop2 = P)) \<ee> (\<lambda>x. prop1 x \<^bold>\<and> prop2 x)\<rfloor>"
by auto

lemma "False" nitpick[user_axioms] oops
lemma True nitpick [satisfy, user_axioms, expect = genuine] by simp

lemma conjAreGodess:
  assumes "closed godessential"
  shows  "(godessential P \<and> godessential Q) \<longrightarrow> godessential (\<lambda>x. P x \<^bold>\<and> Q x)"
nitpick

lemma
  assumes "closed godessential"
  shows  "(godessential P \<and> godessential Q \<and> \<lfloor>\<^bold>\<forall>y. P y \<^bold>\<and> Q y\<rfloor>) \<longrightarrow> godessential (\<lambda>x. P x \<^bold>\<and> Q x)"
by (metis ext)

lemma "\<exists>P. godessential P \<and> godessential (\<^sup>\<not>P)" nitpick[satisfy, expect = genuine, user_axioms] oops

lemma falseEntailsAnything:
  assumes "closed godessential"
  assumes "\<exists>P. godessential P \<and> godessential (\<^sup>\<not>P)"
  shows "\<forall>Q. godessential Q"
nitpick oops

lemma falseEntailsAnything2:
  assumes "closed godessential"
  shows "\<exists>P. (godessential P \<and> godessential (\<^sup>\<not>P)) \<longrightarrow> \<lfloor>\<^bold>\<forall>Q. (P \<^enum> Q)\<rfloor>"
nitpick[user_axioms] oops

lemma "\<lfloor>\<^bold>\<forall>Q. (\<lambda>x. \<^bold>\<bottom>) \<^enum> Q\<rfloor>"
by simp
  
lemma
  assumes "\<exists>P. (godessential P \<and> godessential (\<^sup>\<not>P))"
  shows "godessential (\<lambda>x. \<^bold>\<bottom>)"
nitpick[user_axioms] oops

lemma
 assumes "\<exists>P. (godessential P \<and> godessential (\<^sup>\<not>P))"
 shows "\<exists>P. (godessential (\<lambda>x. P x \<^bold>\<and> (\<^sup>\<not>P) x))"
nitpick[user_axioms] oops

lemma
  assumes "\<exists>P. (godessential (\<lambda>x. P x \<^bold>\<and> (\<^sup>\<not>P) x))"
  shows "godessential (\<lambda>x. \<^bold>\<bottom>)"
using assms by auto

(*<*)
end
(*>*)