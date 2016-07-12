(*<*)
theory IntroductionTobias
imports entailment
begin
(*>*)

axiomatization where S5: "S5_sem"

text "Define godessential to be a property of a property."
consts godessential :: "( \<mu> \<Rightarrow> \<sigma> ) \<Rightarrow> \<sigma>"

text "Define necessary existence as a property."
abbreviation NE :: "\<mu> \<Rightarrow> \<sigma>" 
  where "NE x \<equiv> \<^bold>\<box>( \<^bold>\<exists> y. x \<^bold>= y )"

text "Define omnipotence as a property."
consts omni :: "\<mu> \<Rightarrow> \<sigma>" 

text "Define god as the being which has all god essential properties."
abbreviation god :: "\<mu> \<Rightarrow> \<sigma>" 
  where "god x \<equiv> \<^bold>\<forall> P. godessential P \<^bold>\<rightarrow> P x"

(*
TODO
i dont think this axiomatization is/should be needed to derive the latter theorem
it will be repeated in the assumptions of the meta theorem anyway
text "Assume necessary existence to be a god essential property as axiom hence to be
  part of the collection of god essential properties"
axiomatization 
  where godessentialNE: "\<lfloor> godessential NE \<rfloor>"
  and godessentialomni: "\<lfloor> godessential omni \<rfloor>"
  and noteverypropertygodessential: "\<lfloor> \<^bold>\<exists> P. \<^bold>\<not> godessential P \<rfloor>"
*)

(*
WHY IS THIS NOT WORKING?
text "Define a set P as non-trivially closed under entailment as
  closed under entailment and
  there exists at least one property Q which is not part of the set P and
  the set P is not empty."
abbreviation ntclosedunderentailment :: "( ( \<mu> \<Rightarrow> \<sigma> ) \<Rightarrow> \<sigma> ) \<Rightarrow> \<sigma>" ( "ntclosed" )
  (*where "ntclosed P \<equiv> \<^bold>\<exists> Q. \<^bold>\<not>godessential Q \<^bold>\<and> closed P"*) (* WORKING *)
  where "ntclosed P \<equiv> \<^bold>\<exists> R. godessential R \<^bold>\<and> \<^bold>\<exists> Q. \<^bold>\<not>godessential Q \<^bold>\<and> closed P" (* NOT WORKING *)
*)

(* this can be used in the theorem below which proves non-trivially closed under entailment *)
text "Show that godessential properties are closed under entailment."
theorem
assumes "\<lfloor>\<^bold>\<exists>x. god x\<rfloor>"
shows "\<lfloor>closed godessential\<rfloor>"
proof -
  { fix bb :: "\<mu> \<Rightarrow> i \<Rightarrow> bool" and ii :: i and bba :: "\<mu> \<Rightarrow> i \<Rightarrow> bool"
    have "((\<forall>b. \<not> b) \<or> \<lfloor>(\<lambda>i. \<forall>p. (\<^bold>\<diamond>\<^bold>\<not>p \<^bold>\<or> p) i)\<rfloor> \<and> \<lfloor>(\<lambda>i. \<forall>p. \<lfloor>\<^bold>\<not>op r i \<^bold>\<or> \<^bold>\<not>p\<rfloor> \<or> \<lfloor>\<^bold>\<not>op r i \<^bold>\<or> \<^bold>\<diamond>p\<rfloor>)\<rfloor>) \<and> (((\<exists>i p. \<lfloor>\<^bold>\<not>op r i \<^bold>\<or> p\<rfloor> \<and> (\<^bold>\<not>p) i) \<or> (\<exists>i p. (\<^bold>\<diamond>p \<^bold>\<and> \<^bold>\<diamond>(\<lambda>i. \<lfloor>\<^bold>\<not>op r i \<^bold>\<or> \<^bold>\<not>p\<rfloor>)) i)) \<or> (\<forall>b. b))"
      by (metis S5) (* > 1.0 s, timed out *)
    then obtain iia :: "i \<Rightarrow> (i \<Rightarrow> bool) \<Rightarrow> i" and iib :: "i \<Rightarrow> (i \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> i" and iic :: i and bbb :: "i \<Rightarrow> bool" and iid :: i and iie :: i and bbc :: "i \<Rightarrow> bool" and iif :: i where
      ff1: "((\<forall>b. \<not> b) \<or> \<lfloor>(\<lambda>i. \<forall>p. (op r i \<^bold>\<and> \<^bold>\<not>p) (iia i p) \<or> p i)\<rfloor> \<and> \<lfloor>(\<lambda>i. \<forall>p. \<lfloor>\<^bold>\<not>op r i \<^bold>\<or> \<^bold>\<not>p\<rfloor> \<or> \<lfloor>(\<lambda>ia. (\<^bold>\<not>op r i) ia \<or> (op r ia \<^bold>\<and> p) (iib i p ia))\<rfloor>)\<rfloor>) \<and> ((\<lfloor>\<^bold>\<not>op r iic \<^bold>\<or> bbb\<rfloor> \<and> (\<^bold>\<not>bbb) iic \<or> (op r iid \<^bold>\<and> bbc) iie \<and> iid r iif \<and> \<lfloor>\<^bold>\<not>op r iif \<^bold>\<or> \<^bold>\<not>bbc\<rfloor>) \<or> (\<forall>b. b))"
      by moura (* > 1.0 s, timed out *)
    { assume "\<exists>b. \<not> b"
      have "godessential bb (iib ii (godessential bb) ii) \<and> iif r iib iid bbc iif \<longrightarrow> (\<exists>i. (\<^bold>\<not>op r i) i) \<or> (\<exists>b. (\<^bold>\<not>bbc) iie \<and> \<not> b) \<or> (\<exists>b. (\<^bold>\<not>op r iid) iie \<and> \<not> b) \<or> (\<exists>b. (\<^bold>\<not>op r iid) iif \<and> \<not> b)"
        using ff1 by metis
      then have "godessential bb (iib ii (godessential bb) ii) \<longrightarrow> (\<exists>i. (\<^bold>\<not>op r i) i) \<or> (\<exists>b. (\<^bold>\<not>bbc) iie \<and> \<not> b) \<or> (\<exists>b. (\<^bold>\<not>op r iid) iie \<and> \<not> b) \<or> (\<exists>b. (\<^bold>\<not>op r iid) iif \<and> \<not> b)"
        using ff1 by (metis (no_types))
      then have "(\<^bold>\<not>godessential bb \<^bold>\<or> \<^bold>\<diamond>(\<lambda>i. \<exists>m. (bb m \<^bold>\<and> (\<^sup>\<not>bba) m) i) \<^bold>\<or> godessential bba) ii"
        using ff1 by (metis (no_types)) }
    then have "(\<^bold>\<not>godessential bb \<^bold>\<or> \<^bold>\<diamond>(\<lambda>i. \<exists>m. (bb m \<^bold>\<and> (\<^sup>\<not>bba) m) i) \<^bold>\<or> godessential bba) ii"
      by blast }
  then show ?thesis
    by (metis (no_types))
qed

text "It is clear that, if God exists, then the collection of God’s essential properties 
  is non-trivially closed under entailment"
theorem
assumes "\<lfloor> \<^bold>\<exists> x. god x \<rfloor>"
shows "\<lfloor> \<^bold>\<exists> P. \<^bold>\<not> godessential P  \<^bold>\<and> closed godessential \<rfloor>"
(* Empty set has not been considered; anyway it would be an even stronger conclusion *)
oops

text "If we suppose that God’s essential properties form a collection
that includes necessary existence, necessary omnipotence, necessary omniscience 
and necessary perfect goodness, and if we suppose further that (a) this
collection of properties is closed under entailment and ( b) this collection
of properties does not include all properties, then we can conclude that
God exists."
theorem
assumes "\<lfloor> closed godessential \<rfloor>"
assumes "\<lfloor> \<^bold>\<exists> P. \<^bold>\<not> godessential P \<rfloor>" (* not all properties god essential *)
assumes "\<lfloor> \<^bold>\<exists> R. godessential R \<rfloor>" (* there are god essential properties *)
assumes "\<lfloor> godessential NE \<rfloor>"
assumes "\<lfloor> godessential omni\<rfloor>"
(* which one is meant? Could not find a proof for one of them *)
(* shows "\<lfloor>\<^bold>\<box>(\<^bold>\<exists> x. god x)\<rfloor>" *)
shows "\<lfloor>\<^bold>\<exists> x. god x\<rfloor>"
oops

