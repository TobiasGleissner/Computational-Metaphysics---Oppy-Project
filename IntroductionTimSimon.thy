(*<*)
theory IntroductionTimSimon
imports QML Main
begin
(*>*)

abbreviation entails   :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> (\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (infix "\<^enum>" 50)
  where "P \<^enum> Q  \<equiv> \<^bold>\<box>(\<^bold>\<forall>x. (P x) \<^bold>\<rightarrow> (Q x)) " 

abbreviation  closedunderentailment::  "((\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("closed")
  where "closed (P) \<equiv> \<^bold>\<forall>R. \<^bold>\<forall>Q. (P (Q) \<^bold>\<and> (Q \<^enum> R)) \<^bold>\<rightarrow> P(R)"
text "Hier vielleicht noch mal abändern: In allen Welten? \<Rightarrow>bool? "

consts godessential :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"

abbreviation NE :: "\<mu> \<Rightarrow> \<sigma>" 
  where "NE x \<equiv> \<^bold>\<box>(\<^bold>\<exists> y. x \<^bold>= y)"

consts omni :: "\<mu> \<Rightarrow> \<sigma>" 

axiomatization 
  where godessentialNE: "\<lfloor>godessential NE\<rfloor>"
  and godessentialomni: "\<lfloor>godessential omni\<rfloor>"
  (*and noteverygodessential: "\<lfloor>\<^bold>\<exists>P. \<^bold>\<not> godessential P\<rfloor>"*)
  
abbreviation god :: "\<mu> \<Rightarrow> \<sigma>" 
  where "god x \<equiv> \<^bold>\<forall>P. godessential P \<^bold>\<rightarrow> P x"

theorem
assumes "\<lfloor>\<^bold>\<exists>x. god x\<rfloor>"
shows "\<lfloor>(\<^bold>\<exists>P. \<^bold>\<not> godessential P) \<^bold>\<and> closed godessential\<rfloor>"
(*sledgehammer[remote_satallax]*)
nitpick[user_axioms]
oops

theorem 
assumes "\<lfloor>(\<^bold>\<exists>P. \<^bold>\<not> godessential P) \<^bold>\<and> closed godessential\<rfloor>"
shows "\<lfloor>\<^bold>\<exists>x. god x\<rfloor>"
nitpick[user_axioms] 
oops

(* OLD FROM VERA?!
abbreviation godess::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("GodEss")
  where "GodEss (P) \<equiv> \<^bold>\<forall>y.(GOD(y) \<^bold>\<rightarrow> \<^bold>\<box> P(y))"*)
(*
theorem 
assumes "\<lfloor>\<^bold>\<exists>(C:: (\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>). C P \<^bold>\<rightarrow> (essential (P) \<^bold>\<and> C (NE)) \<^bold>\<and> closed (C) \<^bold>\<and> \<^bold>\<exists>()\<rfloor>"
assumes "\<lfloor>\<^bold>\<exists> P. GodEss(P) \<rfloor>"
assumes "\<lfloor>closed ( GodEss ) \<rfloor>"

shows "\<lfloor>\<^bold>\<exists>x. (x)\<rfloor>"
*)
(*

theorem "\<lfloor>\<^bold>\<exists> P. GodEss(P) \<^bold>\<and> closed ( GodEss ) \<^bold>\<rightarrow> ( \<^bold>\<exists>x. GOD(x))\<rfloor>"

nitpick
oops
*)
(*<*)
end

(*>*)
