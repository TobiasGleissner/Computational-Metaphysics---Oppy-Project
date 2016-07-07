(*<*)
theory IntroductionTimSimon
imports QML Main
begin
(*>*)

axiomatization where T: "T_sem"
axiomatization where S5: "S5_sem"

abbreviation entails   :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> (\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (infix "\<^enum>" 50)
  where "P \<^enum> Q  \<equiv> \<^bold>\<box>(\<^bold>\<forall>x. (P x) \<^bold>\<rightarrow> (Q x))" 

abbreviation  closedunderentailment::  "((\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("closed")
  where "closed (P) \<equiv> \<^bold>\<forall>R. \<^bold>\<forall>Q. (P (Q) \<^bold>\<and> (Q \<^enum> R)) \<^bold>\<rightarrow> P(R)"

consts godessential :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"

abbreviation NE :: "\<mu> \<Rightarrow> \<sigma>" 
  where "NE x \<equiv> \<^bold>\<box>(\<^bold>\<exists> y. x \<^bold>= y)"

axiomatization 
  where godessentialNE: "\<lfloor>godessential NE\<rfloor>"
  (*and noteverygodessential: "\<lfloor>\<^bold>\<exists>P. \<^bold>\<not> godessential P\<rfloor>"*)
  
abbreviation god :: "\<mu> \<Rightarrow> \<sigma>" 
  where "god x \<equiv> \<^bold>\<forall>P. godessential P \<^bold>\<rightarrow> \<^bold>\<box> (P x)"

theorem
assumes "\<lfloor>\<^bold>\<exists>x. god x\<rfloor>"
shows "\<lfloor>(\<^bold>\<exists>P. \<^bold>\<not> godessential P) \<^bold>\<and> closed godessential\<rfloor>"
nitpick
oops
(*
proof -
  {
    fix w
    from assms have "(\<^bold>\<exists>x. god x) w" by simp
    then obtain g where "(god g) w" by blast
    hence "(NE g) w" by blast
    hence "\<not>(( (\<^sup>\<not>NE g))w)"
  }
 show ?thesis sorry
qed*)

theorem 
assumes "\<lfloor>(\<^bold>\<exists>P. \<^bold>\<not> godessential P) \<^bold>\<and> closed godessential\<rfloor>"
shows "\<lfloor>\<^bold>\<exists>x. god x\<rfloor>"
nitpick[user_axioms] 
oops

end

(*>*)
