(*<*)
theory collectionTests
(*imports "../definitions/god/godessentialConst" "../definitions/entailment/collectionEntailment"*)
imports "../definitions/god/godessentialConstNecessary" "../definitions/entailment/collectionEntailment"
begin
(*>*)

lemma "False" nitpick[user_axioms] oops
lemma True nitpick [satisfy, user_axioms, expect = genuine] by simp (*TODO was heißt das?*)

(*collection entails test *)

consts prop1 :: "(\<mu> \<Rightarrow> \<sigma>)"
consts prop2 :: "(\<mu> \<Rightarrow> \<sigma>)"


text\<open>Check: A collection of properties entails the property of having all the properties in the collection\<close>

abbreviation propSet :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (*This is the set {prop1, prop2}*)
  where  "propSet \<equiv> (\<lambda>P.(\<lambda>w. (P = prop1) \<or> (P = prop2)))" (*the lamda w function is 
                                                            to get from boolean to sigma*)

lemma andEntailment:
  shows "\<lfloor>propSet \<^enum> (\<lambda>x. prop1 x \<^bold>\<and> prop2 x)\<rfloor>"
by simp


text\<open>Check: If Properties are necessarily included in a collection of properties, then this collection 
  entails the Property of having these Properties\<close> 

lemma andEntailmentGodessential:
  shows "\<lfloor>\<^bold>\<box>(godessential P \<^bold>\<and> godessential Q) \<^bold>\<rightarrow> (godessential \<^enum> (\<lambda>x. P x \<^bold>\<and> Q x))\<rfloor>"
by meson  


text\<open>Check: If two Properties are necessarily included in a closed collection of properties, then the Property
   of having both Properties is also in the collection\<close>

lemma andClosedGodessential:
  assumes closedGodessential: "\<lfloor>closed godessential\<rfloor>"
  shows  "\<lfloor>\<^bold>\<box>(godessential P \<^bold>\<and> godessential Q) \<^bold>\<rightarrow> godessential (\<lambda>x. P x \<^bold>\<and> Q x)\<rfloor>"
proof -
  {
  fix w
  assume "(\<^bold>\<box>(godessential P \<^bold>\<and> godessential Q)) w"
  from this have godessentialEntails: "(godessential \<^enum> (\<lambda>x. P x \<^bold>\<and> Q x)) w" by meson
  have godessentialSubset: "(godessential \<^bold>\<subseteq> godessential) w" by simp
  from closedGodessential godessentialEntails godessentialSubset  have "(godessential (\<lambda>x. P x \<^bold>\<and> Q x)) w" by (metis (mono_tags, lifting))
  }
  thus ?thesis by blast
qed

text\<open>Check: If a collection of properties contains a contradiction and it is closed, 
then it contains every property\<close>

lemma contradictionEntailsAnything:
  assumes "\<lfloor>closed godessential\<rfloor>"
  assumes "\<lfloor>\<^bold>\<exists>P. godessential P \<^bold>\<and> godessential (\<^sup>\<not>P)\<rfloor>"
  shows "\<lfloor>\<^bold>\<forall>Q. godessential Q\<rfloor>"
by (metis assms(1) assms(2))

lemma falseEntailsAnything:
  assumes "\<lfloor>godessential (\<lambda>x. \<^bold>\<bottom>)\<rfloor>"
  shows "\<lfloor>(\<^bold>\<forall>Q. godessential \<^enum> Q)\<rfloor>"
using assms by fastforce
 
lemma contradictionGodessentialFalse:
  assumes "\<lfloor>closed godessential\<rfloor>"
  assumes "\<lfloor>\<^bold>\<exists>P. (godessential P \<^bold>\<and> godessential (\<^sup>\<not>P))\<rfloor>"
  shows "\<lfloor>godessential (\<lambda>x. \<^bold>\<bottom>)\<rfloor>"
by (metis assms(1) assms(2))


text\<open>Check: If a collection of properties is non-trivial and closed, 
then the property of being "godlike" is in the collection\<close>

lemma
  assumes "\<lfloor>(\<^bold>\<exists>P. \<^bold>\<not> godessential P)\<rfloor>"
  assumes "\<lfloor>(\<^bold>\<exists>P. godessential P)\<rfloor>"
  assumes "\<lfloor>closed godessential\<rfloor>"
  shows "\<lfloor>godessential godlike\<rfloor>"
oops

axiomatization where S5: S5_sem

text\<open>Check: the final step of Oppy's proof: the possibility of necessary existence implies 
necessary existence. (The \<lambda>-function is supposed to model the property of necessary existence.
We are not sure of its accuracy) \<close>

lemma possiblyNecessaryExistence:
  assumes "\<lfloor>\<^bold>\<diamond>(\<^bold>\<box>(\<^bold>\<exists>x. godlike x))\<rfloor>"
  shows "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>x. godlike x)\<rfloor>"
using S5 assms by blast


text\<open>Check: If necessary existence is a property in a collection of properties and it 
is possible that there is a godlike being , then it is necessary that there is a godlike being 
(can fortunately not be proven in our formalization)\<close>

lemma absurdumTest:
  assumes "\<lfloor>godessential (\<lambda>x. \<^bold>\<box>(\<^bold>\<exists>y. meq y x))\<rfloor>"
  assumes "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. godlike x)\<rfloor>"
  shows "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>x. godlike x)\<rfloor>"
(*nitpick oops*)
by (metis S5 assms(2))
(*<*)
end
(*>*)