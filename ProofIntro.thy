(*<*)
theory ProofIntro
imports QMLS5U Main
begin
(*>*)

abbreviation entails   :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> (\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (infix "\<^enum>" 50)
  where "P \<^enum> Q  \<equiv> \<^bold>\<box>(\<^bold>\<forall>x. (P x) \<^bold>\<rightarrow> (Q x))"

abbreviation  closedunderentailment::  "((\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("closed")
  where "closed (P) \<equiv> \<^bold>\<forall>R. \<^bold>\<forall>Q. (P (Q) \<^bold>\<and> (Q \<^enum> R)) \<^bold>\<rightarrow> P(R)"

(*Hier vielleicht noch mal abändern: In allen Welten? \<Rightarrow> bool?"*)

consts godessential :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"

definition god :: "(\<mu> \<Rightarrow> \<sigma>)" where "god x \<equiv> \<^bold>\<forall>\<phi>. (godessential \<phi> \<^bold>\<rightarrow> \<phi> x)"

(*Problem? definition godessential and definition god is a circle?*)

theorem "\<lfloor>\<^bold>\<exists>x. god x \<^bold>\<rightarrow> closed godessential\<rfloor>" 
oops
(*<*)
end
(*>*)
