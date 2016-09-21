(*<*)
theory introOppysProof

imports "../definitions/god/godessentialConst" "../definitions/entailment/collectionEntailment"
(*imports "../definitions/god/godessentialConstNecessary" "../definitions/entailment/collectionEntailment"*)
(*imports "../definitions/god/godessentialConstNecessary" "../definitions/entailment/individualEntailment"*)
(*imports "../definitions/god/godessentialConst" "../definitions/entailment/individualEntailment"*)
begin
(*>*)

axiomatization where T: T_sem
theorem 
assumes "\<lfloor>(\<^bold>\<exists>P. \<^bold>\<not> godessential P)\<rfloor>"
assumes "\<lfloor>(\<^bold>\<exists>P. godessential P)\<rfloor>"
assumes "\<lfloor>closed godessential\<rfloor>"
(*assumes "\<lfloor>godessential godlike\<rfloor>"*)
shows "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. godlike x)\<rfloor>"
proof -
  {
    fix w
    {
      assume impGod: "\<not> (\<^bold>\<diamond>(\<^bold>\<exists>x. godlike x)) w"
      {
        fix x
        assume "(godlike x) w"
        with this impGod have "False" using T by blast
        hence "((\<lambda>x. \<^bold>\<bottom>) x) w" by blast
      }
      hence "(\<^bold>\<forall>x. (godlike x \<^bold>\<rightarrow> (\<lambda>x. \<^bold>\<bottom>) x)) w" by blast
      have "(godessential \<^enum> ((\<lambda>x. \<^bold>\<bottom>))) w" (*sledgehammer[remote_satallax, verbose]*) using impGod by auto
      hence A: "godessential (\<lambda>x. \<^bold>\<bottom>) w" by (metis assms(3))
      have "(\<^bold>\<forall>P. (\<lambda>p. \<lambda>i. p = (\<lambda>x. \<^bold>\<bottom>)) \<^enum> P) w" by auto
      with this A have "(\<^bold>\<forall>P. godessential P) w" by (metis \<open>(\<^bold>\<box>(\<lambda>v. \<forall>x. (\<forall>xa. (godessential xa \<^bold>\<rightarrow> xa x) v) \<longrightarrow> False)) w\<close> assms(3))
      hence "False" using assms(1) by auto
    }
    hence "(\<^bold>\<diamond>(\<^bold>\<exists>x. godlike x)) w" by blast
  }
  then show ?thesis by blast
qed
(*<*)
end
(*>*)