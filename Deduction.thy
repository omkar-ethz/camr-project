theory Deduction
  imports Term
begin

inductive deduce :: "msg set \<Rightarrow> msg \<Rightarrow> bool" ( infix "\<turnstile>" 72)
  where
(*do we need T \<turnstile> \<iota> as a rule? *)
Ax: "u \<in> T \<Longrightarrow> T \<turnstile> u"
| CompHash: "T \<turnstile> t \<Longrightarrow> T \<turnstile> msg.Hash t"
| CompPair: "\<lbrakk>T \<turnstile> t1; T \<turnstile> t2\<rbrakk>  \<Longrightarrow> T \<turnstile> msg.Pair t1 t2"
| CompSenc: "\<lbrakk>T \<turnstile> t1; T \<turnstile> t2\<rbrakk>  \<Longrightarrow> T \<turnstile> msg.Senc t1 t2"
| CompAenc: "\<lbrakk>T \<turnstile> t1; T \<turnstile> t2\<rbrakk>  \<Longrightarrow> T \<turnstile> msg.Aenc t1 t2"
| CompSign: "\<lbrakk>T \<turnstile> t\<rbrakk>  \<Longrightarrow> T \<turnstile> msg.Sign t msg.\<iota>"
| Proj1: "T \<turnstile> msg.Pair t1 t2 \<Longrightarrow> T \<turnstile> t1"
| Proj2: "T \<turnstile> msg.Pair t1 t2 \<Longrightarrow> T \<turnstile> t2"
| Sdec: "\<lbrakk>T \<turnstile> msg.Senc t k; T \<turnstile> k\<rbrakk> \<Longrightarrow> T \<turnstile> t"
| Adec: "\<lbrakk>T \<turnstile> msg.Aenc t msg.\<iota>\<rbrakk> \<Longrightarrow> T \<turnstile> t"

lemma "{msg.Senc (msg.Const ''a'') (msg.Const ''x''), msg.Const ''x''} \<turnstile> (msg.Const ''a'')"
  apply(rule Sdec)
   apply(rule Ax)
   apply auto
  apply(rule Ax)
  by auto

lemma "{\<langle>m, n\<rangle>} \<turnstile> \<h>(\<langle>n, m\<rangle>)"
proof -
  have 1:"{\<langle>m, n\<rangle>} \<turnstile> (\<langle>m,n\<rangle>)" by (auto intro: Ax)
  then have 2:"{\<langle>m, n\<rangle>} \<turnstile> m" by (auto intro: Proj1)
  from 1 have 3:"{\<langle>m, n\<rangle>} \<turnstile> n" by (auto intro:Proj2)
  from 3 2 have "{\<langle>m, n\<rangle>} \<turnstile> (\<langle>n,m\<rangle>)" by (auto intro:CompPair)
  thus "{\<langle>m, n\<rangle>} \<turnstile> \<h>(\<langle>n, m\<rangle>)" by (auto intro:CompHash)
qed

lemma "{\<lbrace>m\<rbrace>\<^sub>k, {k}\<^sub>\<iota>} \<turnstile> (\<langle>m,([k]\<^sub>\<iota>)\<rangle>)" (is "?T \<turnstile> ?u")
proof -
  have "?T \<turnstile> ({k}\<^sub>\<iota>)" by (auto intro:Ax)
  hence "?T \<turnstile> k" ..
  hence "?T \<turnstile> m" by (auto intro:Ax Sdec)
  from \<open>?T \<turnstile> k\<close> have "?T \<turnstile> ([k]\<^sub>\<iota>)" ..
  with \<open>?T \<turnstile> m\<close> show ?thesis ..
qed



lemma deduce_weaken:
assumes "G \<turnstile> t" and "G \<subseteq> H"
shows "H \<turnstile> t"
  using assms
  by(induction G t rule:deduce.induct) (auto intro:deduce.intros)


lemma deduce_cut:
assumes  "insert t H \<turnstile> u" and  "H \<turnstile> t" 
shows "H \<turnstile> u"
  using assms
  by(induction "insert t H" u rule:deduce.induct) (auto intro:deduce.intros)


datatype constraint =
Constraint "msg list" "msg list" "msg" ( "((2_/|_)/ \<Zrres>_) " [67,67,67]66)

type_synonym constraint_system = "constraint list"

fun fv_constraint::"constraint \<Rightarrow> string set" where
"fv_constraint (M | A  \<Zrres> t) = \<Union>(set(map fv_msg M)) \<union>  \<Union>(set(map fv_msg A)) \<union> fv_msg t"

fun fv_constraint_system::"constraint_system \<Rightarrow> string set" where
"fv_constraint_system cs = \<Union>(set(map fv_constraint cs))"

fun sapply_constraint::"subst_msg \<Rightarrow> constraint \<Rightarrow> constraint" where
"sapply_constraint \<sigma> (M | A \<Zrres> t) = map (sapply_msg \<sigma>) M | map  (sapply_msg \<sigma>) A \<Zrres>  sapply_msg \<sigma> t"

fun sapply_constraint_system::"subst_msg \<Rightarrow> constraint_system \<Rightarrow> constraint_system" where
"sapply_constraint_system \<sigma> cs = map (sapply_constraint \<sigma>) cs"

(*add main lemmas(?) about fv and sapply*)

definition sol::"constraint_system \<Rightarrow> subst_msg set" where
"sol cs = {\<sigma> | M A t \<sigma>. (M | A \<Zrres> t) \<in> set(cs) \<longrightarrow> set(map (sapply_msg \<sigma>) (M@A)) \<turnstile> sapply_msg \<sigma> t}"

lemma "sol (cs1@cs2 ) = sol (cs1 ) \<inter> sol (cs2)"
  sorry

lemma "\<tau> \<in> sol (sapply_constraint_system \<sigma> cs) \<Longrightarrow> scomp_msg \<tau> \<sigma> \<in> sol cs"
  sorry

fun is_variable::"msg \<Rightarrow> bool" where
"is_variable (Variable _) = True"
| "is_variable _ = False"

inductive rer1 :: "constraint \<Rightarrow> subst_msg \<Rightarrow> constraint_system \<Rightarrow> bool"
("(_)/\<leadsto>\<^sub>1[_]/ (_)" [64,64,64]63) where
Unifl: "\<lbrakk>\<not> is_variable t; u \<in> set(M) \<union> set(A); sapply_msg \<sigma> u = sapply_msg \<sigma> t\<rbrakk> 
          \<Longrightarrow> M | A \<Zrres> t \<leadsto>\<^sub>1[\<sigma>] Nil"

| CompHashl: "M | A \<Zrres> (\<h> t) \<leadsto>\<^sub>1[Variable] [M | A \<Zrres> t]"
| CompPairl: "M | A \<Zrres> (\<langle>t1,t2\<rangle>) \<leadsto>\<^sub>1[Variable] [M | A \<Zrres> t1, M | A \<Zrres> t2]"
| CompSencl: "M | A \<Zrres> (\<lbrace>t\<rbrace>\<^sub>k) \<leadsto>\<^sub>1[Variable] [M | A \<Zrres> t, M | A \<Zrres> k]"
| CompAencl: "M | A \<Zrres> ({t}\<^sub>k) \<leadsto>\<^sub>1[Variable] [M | A \<Zrres> t, M | A \<Zrres> k]"
| CompSignl: "M | A \<Zrres> ([t]\<^sub>\<iota>) \<leadsto>\<^sub>1[Variable] [M | A \<Zrres> t]"

| Projl: "((\<langle>u,v\<rangle>)#M) | A \<Zrres> t \<leadsto>\<^sub>1[Variable] [(u#v#M) | ((\<langle>u,v\<rangle>)#A) \<Zrres> t]"
| Sdecl: "((\<lbrace>u\<rbrace>\<^sub>k)#M) | A \<Zrres> t \<leadsto>\<^sub>1[Variable] [(u#M) | ((\<lbrace>u\<rbrace>\<^sub>k)#A) \<Zrres> t, M | ((\<lbrace>u\<rbrace>\<^sub>k)#A) \<Zrres> k]"
| Adecl: "(({u}\<^sub>\<iota>)#M) | A \<Zrres> t \<leadsto>\<^sub>1[Variable] [(u#M) | ((\<lbrace>u\<rbrace>\<^sub>\<iota>)#A) \<Zrres> t]"
| Ksubl:  "(let y = Variable x in (({u}\<^sub>y)#M)) | A \<Zrres> t \<leadsto>\<^sub>1[(Variable(x:=i))] 
            [sapply_constraint (Variable(x:=i)) ((let y = Variable x in (({u}\<^sub>y)#M)) | A \<Zrres> t)]"

inductive rer :: "constraint_system \<Rightarrow>subst_msg \<Rightarrow> constraint_system \<Rightarrow> bool"
("_/ \<leadsto>[_]/ _ " [73,73,73]72) where
Context: "c \<leadsto>\<^sub>1[\<sigma>] cs \<Longrightarrow> (c#cs') \<leadsto>[\<sigma>] (cs@cs')"

inductive rer_star :: "constraint_system \<Rightarrow>subst_msg \<Rightarrow> constraint_system \<Rightarrow> bool"
("_/ \<leadsto>\<^emph>[_]/ _ " [73,73,73]72) where
Refl: "cs \<leadsto>\<^emph>[Variable] cs"
| Trans: "\<lbrakk>cs \<leadsto>[\<sigma>] cs''; cs'' \<leadsto>\<^emph>[\<tau>] cs'\<rbrakk> \<Longrightarrow> cs \<leadsto>\<^emph>[\<tau> \<circ>\<^sub>s \<sigma>] cs'"


lemma "[Const ''a''] | [] \<Zrres> Const ''a''  \<leadsto>\<^sub>1[Variable] []"
  by (auto intro: rer1.intros)

end