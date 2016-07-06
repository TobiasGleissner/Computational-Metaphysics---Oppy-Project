(*<*)
theory ProofIntro
imports QMLS5U Main
begin
(*>*)

axiomatization where S5: "S5_sem" 

abbreviation entails   :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> (\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (infix "\<^enum>" 50)
  where "P \<^enum> Q  \<equiv> \<^bold>\<box>(\<^bold>\<forall>x. (P x) \<^bold>\<rightarrow> (Q x))"

abbreviation  closedunderentailment::  "((\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("closed")
  where "closed (P) \<equiv> \<^bold>\<forall>R. \<^bold>\<forall>Q. (P (Q) \<^bold>\<and> (Q \<^enum> R)) \<^bold>\<rightarrow> P(R)"

(*Hier vielleicht noch mal abändern: In allen Welten? \<Rightarrow> bool?"*)

consts god :: "\<mu>"

abbreviation godessential :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" 
  where "godessential P \<equiv> P god" 

theorem "\<lfloor>(\<^bold>\<not> (\<^bold>\<exists>x. (meq x god))) \<^bold>\<rightarrow> closed godessential\<rfloor>"
using S5 by blast
(*
proof -
  {
    fix w
    fix R
    fix Q
    have "((godessential (Q) \<^bold>\<and> (Q \<^enum> R)) \<^bold>\<rightarrow> godessential(R)) w"
    proof (cases)
      assume "godessential(R) w"
      show ?thesis by (simp add: \<open>godessential R w\<close>)
    next
      assume "(\<^bold>\<not> godessential(R)) w"
      show ?thesis
      proof cases
        assume "(godessential (Q) \<^bold>\<and> (Q \<^enum> R)) w"
        hence "godessential(R) w" using S5 by blast (*HELLO S5 for kicking out the box!*)
        hence "False" by (simp add: \<open>godessential (\<^sup>\<not>R) w\<close>)
        thus ?thesis by simp
      next
        assume "(\<^bold>\<not>(godessential (Q) \<^bold>\<and> (Q \<^enum> R))) w"
        show ?thesis by (simp add: \<open>(\<^bold>\<not>(godessential Q \<^bold>\<and> \<^bold>\<box>(\<lambda>v. \<forall>x. (Q x \<^bold>\<rightarrow> R x) v))) w\<close>)
      qed
    qed
  }
  thus ?thesis by blast
qed
*)  
(*<*)
end
(*>*)
