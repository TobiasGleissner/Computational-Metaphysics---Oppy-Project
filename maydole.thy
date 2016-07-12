(*<*)
theory maydole
imports entailment
begin
(*>*)
consts greaterthan :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>"
consts perfect :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"

abbreviation supreme :: "\<mu> \<Rightarrow> \<sigma>"
  where "supreme x  \<equiv> \<^bold>\<box>(\<^bold>\<forall>y. \<^bold>\<not>(meq x y) \<^bold>\<rightarrow> (greaterthan x y))"

axiomatization 
  where A1: "\<lfloor>\<^bold>\<forall>P. perfect P \<^bold>\<rightarrow> \<^bold>\<not> perfect (\<^sup>\<not> P)\<rfloor>"
  and A2: "\<lfloor>closed perfect\<rfloor>"
  and A3: "\<lfloor>perfect supreme\<rfloor>"

theorem "\<lfloor>\<^bold>\<exists>x. supreme x \<rfloor>" oops
(*<*)
end
(*>*)
