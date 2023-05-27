theory Deduction
  imports Term
begin

subsection \<open>Assignment 6\<close>

(*
  chsp: You could define \<iota> as 'Const "iota"' instead of introducing a new constructor for msg, 
  which is not necessary.  
*)
inductive deduce :: "msg set \<Rightarrow> msg \<Rightarrow> bool" ( infix "\<turnstile>" 72)
  where
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

subsection \<open>Assignment 7\<close>

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

lemma sol_inter: "sol (cs1@cs2 ) = sol (cs1 ) \<inter> sol (cs2)"
  apply (auto simp add:sol_def)
  by (metis Ax Un_absorb all_not_in_conv list.set(2) rev_image_eqI singletonI)

lemma sol_subs: "\<tau> \<in> sol (sapply_constraint_system \<sigma> cs) \<Longrightarrow> scomp_msg \<tau> \<sigma> \<in> sol cs"
  apply(auto simp add:sol_def)
   apply (metis Ax all_not_in_conv list.simps(15) rev_image_eqI singletonI sup_idem)
  apply (metis Ax all_not_in_conv list.simps(15) rev_image_eqI singletonI sup_idem)
  done

fun is_variable::"msg \<Rightarrow> bool" where
"is_variable (Variable _) = True"
| "is_variable _ = False"

(*
  chsp:
  - Unifl: Please replace "sapply_msg \<sigma> u = sapply_msg \<sigma> t" by a proposition involving the
    unification algorithm on messages (as in Figure 2). -- DONE \<checkmark>
  - Your decomposition rules are not general enough. They assume the the analyzed message in 
    is at the head of M, whereas there is no such assumption in the set-based version of Fig. 2.
    Please make sure that the analyzed term may occur in any position of the list M. -- DONE \<checkmark>
  - I would replace the two instances of "let .. in .." in the rule Ksubl by a rule
    premise \<lbrakk> y = Variable x \<rbrakk> \<Longrightarrow> ... {u}\<^sub>y ...; then there is no duplication (you could also 
    have used a single "let .. in .." though) and no need to unfold Let_def. You could even 
    eliminate more redundancy using \<lbrakk> c = {u}\<^sub>y \<rbrakk> \<Longrightarrow> ... c ... -- DONE \<checkmark>
*)
inductive rer1 :: "constraint \<Rightarrow> subst_msg \<Rightarrow> constraint_system \<Rightarrow> bool"
("(_)/\<leadsto>\<^sub>1[_]/ (_)" [64,64,64]63) where
Unifl: "\<lbrakk>\<not> is_variable t; u \<in> set(M) \<union> set(A); Some \<sigma> = unify_msg [(t,u)]\<rbrakk> 
          \<Longrightarrow> M | A \<Zrres> t \<leadsto>\<^sub>1[\<sigma>] Nil"

| CompHashl: "M | A \<Zrres> (\<h> t) \<leadsto>\<^sub>1[Variable] [M | A \<Zrres> t]"
| CompPairl: "M | A \<Zrres> (\<langle>t1,t2\<rangle>) \<leadsto>\<^sub>1[Variable] [M | A \<Zrres> t1, M | A \<Zrres> t2]"
| CompSencl: "M | A \<Zrres> (\<lbrace>t\<rbrace>\<^sub>k) \<leadsto>\<^sub>1[Variable] [M | A \<Zrres> t, M | A \<Zrres> k]"
| CompAencl: "M | A \<Zrres> ({t}\<^sub>k) \<leadsto>\<^sub>1[Variable] [M | A \<Zrres> t, M | A \<Zrres> k]"
| CompSignl: "M | A \<Zrres> ([t]\<^sub>\<iota>) \<leadsto>\<^sub>1[Variable] [M | A \<Zrres> t]"

| Projl: "\<lbrakk>c = \<langle>u,v\<rangle>; c \<in> set(M); M' = list (set (M) - {c})\<rbrakk> \<Longrightarrow> 
            M | A \<Zrres> t \<leadsto>\<^sub>1[Variable] [(u#v#M') | (c#A) \<Zrres> t]"
| Sdecl: "\<lbrakk>c = \<lbrace>u\<rbrace>\<^sub>k; c \<in> set(M); M' = list (set (M) - {c})\<rbrakk> \<Longrightarrow> 
            M | A \<Zrres> t \<leadsto>\<^sub>1[Variable] [(u#M') | (c#A) \<Zrres> t, M' | (c#A) \<Zrres> k]"
| Adecl: "\<lbrakk>c = {u}\<^sub>\<iota>; c \<in> set(M); M' = list (set (M) - {c})\<rbrakk> \<Longrightarrow> 
            M | A \<Zrres> t \<leadsto>\<^sub>1[Variable] [(u#M') | (c#A) \<Zrres> t]"
| Ksubl: "\<lbrakk>y = Variable x; {u}\<^sub>y \<in> set(M)\<rbrakk> \<Longrightarrow> 
            M | A \<Zrres> t \<leadsto>\<^sub>1[(Variable(x:=\<iota>))] [sapply_constraint (Variable(x:=\<iota>)) (M | A \<Zrres> t)]"

(*
  chsp:
  Similar set vs list problem as with decomposition rules above. A constraint system in the
  project description is a set of constraints; here it is a list of constraints. 
  Left-hand side of rule is fine. On RHS, make sure that the c and cs can appear anywhere in 
  the ambient list, not only at the beginning. Otherwise, this severely restricts the 
  non-determinism of the constraint reduction relation: you could always only reduce the first 
  constraint. -- DONE \<checkmark>
*)

inductive rer :: "constraint_system \<Rightarrow>subst_msg \<Rightarrow> constraint_system \<Rightarrow> bool"
("_/ \<leadsto>[_]/ _ " [73,73,73]72) where
Context: "\<lbrakk>c \<leadsto>\<^sub>1[\<sigma>] cs; c \<in> set(A); set(cs) \<subseteq> set(B); set(A) = insert c cs'; 
            set(B) = set(cs) \<union> ((sapply_constraint \<sigma>) ` cs') \<rbrakk> \<Longrightarrow> A \<leadsto>[\<sigma>] B"


inductive rer_star :: "constraint_system \<Rightarrow>subst_msg \<Rightarrow> constraint_system \<Rightarrow> bool"
("_/ \<leadsto>\<^emph>[_]/ _ " [73,73,73]72) where
Refl: "cs \<leadsto>\<^emph>[Variable] cs"
| Trans: "\<lbrakk>cs \<leadsto>[\<sigma>] cs''; cs'' \<leadsto>\<^emph>[\<tau>] cs'\<rbrakk> \<Longrightarrow> cs \<leadsto>\<^emph>[\<tau> \<circ>\<^sub>s \<sigma>] cs'"


lemma "[Const ''a''] | [] \<Zrres> Const ''a''  \<leadsto>\<^sub>1[Variable] []"
  by (auto intro: rer1.intros)

fun simple_constraint :: "constraint \<Rightarrow> bool"
  where
"simple_constraint (Constraint M A (Variable x)) = True"
| "simple_constraint _ = False"

fun simple_constraint_system :: "constraint_system \<Rightarrow> bool"
  where
"simple_constraint_system [] = True"
| "simple_constraint_system (c#cs) = (if simple_constraint c then simple_constraint_system cs else False)"

definition red :: "constraint_system \<Rightarrow> subst_msg set"
  where
"red cs = {\<tau> \<circ>\<^sub>s \<sigma> | \<sigma> \<tau> cs'. simple_constraint_system cs' \<and> \<tau> \<in> sol cs' \<and> cs \<leadsto>\<^emph>[\<tau> \<circ>\<^sub>s \<sigma>] cs'}"

subsection \<open>Assignment 8\<close>
(*Soundness, lemmas:*)

lemma lemma7: "\<lbrakk>c \<leadsto>\<^sub>1[\<sigma>] cs; \<tau> \<in> sol cs\<rbrakk> \<Longrightarrow>  \<tau> \<circ>\<^sub>s \<sigma> \<in> sol [c]"
  by(erule rer1.cases) (auto simp add:sol_def)


lemma assumes 1: "cs \<leadsto>[\<sigma>] cs'" and 2:"\<tau> \<in> sol cs'" 
  shows "\<tau> \<circ>\<^sub>s \<sigma> \<in> sol cs"
proof -
  obtain c cs1 cs2
    where 3: "cs = c#cs2"  and 4: "cs' =  cs1 @  (sapply_constraint_system \<sigma> cs2)" 
  and  5: "c \<leadsto>\<^sub>1[\<sigma>] cs1" using 1 (*apply(rule Context)*) sorry
  from 2 4 have 6: "\<tau> \<in> sol cs1" and 7: "\<tau> \<in> sol (sapply_constraint_system \<sigma> cs2)" 
    by (auto simp add: sol_inter)
  with 5 have "\<tau> \<circ>\<^sub>s \<sigma> \<in> sol [c]" "\<tau> \<circ>\<^sub>s \<sigma> \<in> sol cs2" by (auto intro:lemma7 sol_subs)
  with 3 sol_inter show ?thesis
    by (metis IntI append_Cons append_Nil)
qed


end