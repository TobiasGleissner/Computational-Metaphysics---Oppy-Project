(*<*)
theory ProofIntroVera


imports QML Main

begin

(*>*)

abbreviation entails   :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> (\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (infix "\<^enum>" 50)
  where "P \<^enum> Q  \<equiv> \<^bold>\<box>(\<^bold>\<forall>x. (P x) \<^bold>\<rightarrow> (Q x)) " 


abbreviation  closedunderentailment::  "((\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("closed")
  where "closed (P) \<equiv> \<^bold>\<forall>R. \<^bold>\<forall>Q. (P (Q) \<^bold>\<and> (Q \<^enum> R)) \<^bold>\<rightarrow> P(R)"
text "Hier vielleicht noch mal abändern: In allen Welten? \<Rightarrow>bool? "

consts omnipotent :: "\<mu> \<Rightarrow> \<sigma>"

consts omniscient :: "\<mu> \<Rightarrow> \<sigma>"

consts perfectlygood :: "\<mu> \<Rightarrow> \<sigma>"

abbreviation god :: "\<mu> \<Rightarrow> \<sigma>" ("GOD")
  where "GOD (x) \<equiv> (\<^bold>\<box>( \<^bold>\<exists> y. x \<^bold>= y)) \<^bold>\<and> (\<^bold>\<box> omnipotent (x)) \<^bold>\<and>  (\<^bold>\<box> omniscient (x)) \<^bold>\<and> (\<^bold>\<box> perfectlygood (x)) "


abbreviation  godess::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("GodEss")
  where "GodEss (P) \<equiv> \<^bold>\<forall>y.(GOD(y) \<^bold>\<rightarrow> \<^bold>\<box> P(y))"

theorem 
assumes "\<lfloor>(\<^bold>\<exists>P. \<^bold>\<not> GodEss P)\<rfloor>"
assumes "\<lfloor>closed ( GodEss ) \<rfloor>"
shows "\<lfloor>\<^bold>\<exists>x. GOD(x)\<rfloor>"
using assms(1) by auto
(*<*)
end

(*>*)
