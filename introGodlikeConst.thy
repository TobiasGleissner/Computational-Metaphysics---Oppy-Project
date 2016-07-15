(*<*)
theory introGodlikeConst
imports entailment
begin
(*>*)

axiomatization where T: "T_sem"
axiomatization where S5: "S5_sem"

consts godlike :: "\<mu> \<Rightarrow> \<sigma>" 

text "there will be a collection of properties 
– ‘God’s essential properties’ – that God possesses of necessity"
abbreviation godessential :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"
  where "godessential P \<equiv> \<^bold>\<forall>x. (godlike x \<^bold>\<rightarrow> \<^bold>\<box>(P x))"

text "It is clear that, 
if God exists, 
then the collection of God’s essential properties is non-trivially closed under entailment"
theorem
assumes "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>x. godlike x)\<rfloor>"
shows "\<lfloor>((\<^bold>\<exists>P. \<^bold>\<not> godessential P) \<^bold>\<and> closed godessential)\<rfloor>"
using assms T by blast

text "it is also true that, 
if the collection of God’s essential properties is non-trivially closed under entailment, 
then God exists"
theorem 
assumes "\<lfloor>((\<^bold>\<exists>P. \<^bold>\<not> godessential P) \<^bold>\<and> closed godessential)\<rfloor>"
shows "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>x. godlike x)\<rfloor>"
using assms by blast

(* BUT *)
text "BUT closed godessential is a tautology"
theorem "\<lfloor>closed godessential\<rfloor>"
by blast

(*just drag the not into the defintion of godessential.. *)
theorem 
assumes "\<lfloor>(\<^bold>\<exists>P. \<^bold>\<not> godessential P)\<rfloor>"
shows "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>x. godlike x)\<rfloor>"
using assms by blast

(*identity is always godessential*)
lemma "\<lfloor>(\<^bold>\<exists>P. godessential P)\<rfloor>" by blast
lemma "\<lfloor>godessential (\<lambda>x. meq x x)\<rfloor>" by blast

(*no contradiction*)
lemma "False" nitpick[user_axioms] oops

(*<*)
end
(*>*)
