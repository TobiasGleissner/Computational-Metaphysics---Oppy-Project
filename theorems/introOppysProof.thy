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
      (*hence "(godessential \<^enum> ((\<lambda>x. \<^bold>\<bottom>) ) )w" sledgehammer[remote_satallax ] using impGod by auto*)
      hence "godessential (\<lambda>x. \<^bold>\<bottom>) w" (* sledgehammer[remote_satallax, verbose]*) by (metis assms(3) impGod) (*Isabell directly shows FALSE hence this steps are only to visualize Oppie's proofs*)
      hence "(\<^bold>\<forall>P. godessential P) w" by (metis assms(3) impGod)
      hence "False" using assms(1) by auto
    }
    hence "(\<^bold>\<diamond>(\<^bold>\<exists>x. godlike x)) w" by blast
  }
  then show ?thesis by blast
qed
(*<*)
end
(*>*)