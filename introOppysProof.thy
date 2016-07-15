(*<*)
theory introOppysProof
imports introGodessentialConst
begin
(*>*)

abbreviation peq :: "(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>"  
  where "peq P Q \<equiv> \<lambda>w. (P = Q)"

theorem 
assumes "\<lfloor>(\<^bold>\<exists>P. \<^bold>\<not> godessential P) \<^bold>\<and> closed godessential\<rfloor>"
shows "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. godlike x)\<rfloor>"
proof -
  {
    fix w
    from assms have "((\<^bold>\<exists>P. \<^bold>\<not> godessential P) \<^bold>\<and> closed godessential) w" by simp
    {
      from godessentialex obtain p where "godessential p w" by blast
      {
        assume impGod: "(\<^bold>\<not>\<^bold>\<diamond>(\<^bold>\<exists>x. godlike x)) w"
        {
          assume "\<not> ((\<^bold>\<forall>Q. ((godessential Q) \<^bold>\<and> \<^bold>\<not> (peq p Q)) \<^bold>\<rightarrow> \<^bold>\<box>(Q x)) \<^bold>\<rightarrow> (\<^bold>\<not> \<^bold>\<box>(p x))) w"
          hence  "(\<^bold>\<not> (\<^bold>\<forall>Q. ((godessential Q) \<^bold>\<and> \<^bold>\<not> (peq p Q)) \<^bold>\<rightarrow> \<^bold>\<box>(Q x)) \<^bold>\<rightarrow> (\<^bold>\<not> \<^bold>\<box>(p x))) w" by blast
          hence  "((\<^bold>\<forall>Q. ((godessential Q) \<^bold>\<and> \<^bold>\<not> (peq p Q)) \<^bold>\<rightarrow> \<^bold>\<box>(Q x)) \<^bold>\<and> (\<^bold>\<box> ((p) x))) w" using \<open>\<not> ((\<forall>xa. godessential xa w \<and> p \<noteq> xa \<longrightarrow> (\<^bold>\<box>xa x) w) \<longrightarrow> (\<^bold>\<not>\<^bold>\<box>p x) w)\<close> by blast
          hence "(\<^bold>\<forall>x. godlike x) w" by (metis T \<open>(\<^bold>\<not>\<^bold>\<diamond>(\<lambda>v. \<exists>x. \<forall>xa. (godessential xa \<^bold>\<rightarrow> \<^bold>\<box>xa x) v)) w\<close>) 
          from this impGod have  "False" by (meson S5)
        }
        hence "((\<^bold>\<forall>Q. ((godessential Q) \<^bold>\<and> \<^bold>\<not> (peq p Q)) \<^bold>\<rightarrow> \<^bold>\<box>(Q x)) \<^bold>\<rightarrow> (\<^bold>\<not> \<^bold>\<box>(p x))) w" by blast
        hence "((\<^bold>\<forall>Q. ((godessential Q) \<^bold>\<and> \<^bold>\<not> (peq p Q)) \<^bold>\<rightarrow> \<^bold>\<box>(Q x)) \<^bold>\<rightarrow> (\<^bold>\<diamond>((\<^sup>\<not>p) x))) w" by blast
        hence "((\<^bold>\<forall>Q. ((godessential Q)) \<^bold>\<rightarrow> \<^bold>\<box>(Q x)) \<^bold>\<rightarrow> (\<^bold>\<diamond>((\<^sup>\<not>p) x \<^bold>\<and> p x))) w" using \<open>godessential p w\<close> by blast
        hence "((\<^bold>\<forall>Q. ((godessential Q)) \<^bold>\<rightarrow> \<^bold>\<box>(Q x)) \<^bold>\<rightarrow> (\<^bold>\<diamond>(\<^bold>\<bottom>))) w" by blast
        have "False" sorry
      }
      hence "(\<^bold>\<diamond>(\<^bold>\<exists>x. godlike x)) w" by blast 
    }
  }
  thus ?thesis by simp
qed

(*<*)
end
(*>*)