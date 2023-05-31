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

lemma sol_inter_mult: "sol (cs1@c#cs2) = sol cs1 \<inter> sol [c] \<inter> sol cs2"
  using sol_inter
  by (metis append.left_neutral append_Cons inf_assoc)

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

chsp (ADDED, 30.5.2023):
  - decomposition rules: the constant "list" does not exist, it is just a (green!) variable below. 
    Please use "M1 @ \<langle>u,v\<rangle> # M2" (and similar for \<lbrace>u\<rbrace>\<^sub>k etc.) instead of M on left-hand sides. -- DONE \<checkmark>
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

| Projl: "(M1@(\<langle>u,v\<rangle>)#M2) | A \<Zrres> t \<leadsto>\<^sub>1[Variable] [(u#v#M1@M2) | ((\<langle>u,v\<rangle>)#A) \<Zrres> t]"
| Sdecl: "(M1@(\<lbrace>u\<rbrace>\<^sub>k)#M2) | A \<Zrres> t \<leadsto>\<^sub>1[Variable] 
                [(u#M1@M2) | ((\<lbrace>u\<rbrace>\<^sub>k)#A) \<Zrres> t, (M1@M2) | ((\<lbrace>u\<rbrace>\<^sub>k)#A) \<Zrres> k]"
| Adecl: "(M1@({u}\<^sub>\<iota>)#M2) | A \<Zrres> t \<leadsto>\<^sub>1[Variable] [(u#M1@M2) | (({u}\<^sub>\<iota>)#A) \<Zrres> t]"
| Ksubl: "y = Variable x \<Longrightarrow> 
            (M1@({u}\<^sub>y)#M2) | A \<Zrres> t \<leadsto>\<^sub>1[(Variable(x:=\<iota>))] 
                [sapply_constraint (Variable(x:=\<iota>)) ((M1@({u}\<^sub>y)#M2) | A \<Zrres> t)]"

(*
  chsp:
  Similar set vs list problem as with decomposition rules above. A constraint system in the
  project description is a set of constraints; here it is a list of constraints. 
  Left-hand side of rule is fine. On RHS, make sure that the c and cs can appear anywhere in 
  the ambient list, not only at the beginning. Otherwise, this severely restricts the 
  non-determinism of the constraint reduction relation: you could always only reduce the first 
  constraint. -- DONE \<checkmark>

chsp (ADDED 30.5.2023):
  Your definition will not allow you to prove termination of constrain reduction, since cs' may 
  be an infinite set of constraints. Also, it may make your proofs unnecessarily complicated.
  (Btw, the condition "set(cs) \<subseteq> set(B)" is redundant. Why? -- since it was implied by the last constraint)
  Please simplify it by using "cs1 @ c # cs2" on the left-hand side of \<leadsto>[\<sigma>] and adapting 
  the right-hand side accordingly. -- DONE \<checkmark>
*)

inductive rer :: "constraint_system \<Rightarrow>subst_msg \<Rightarrow> constraint_system \<Rightarrow> bool"
("_/ \<leadsto>[_]/ _ " [73,73,73]72) where
Context: "\<lbrakk>c \<leadsto>\<^sub>1[\<sigma>] cs\<rbrakk> \<Longrightarrow> 
  (cs1 @ c # cs2) \<leadsto>[\<sigma>] ((sapply_constraint_system \<sigma> cs1) @ cs @ (sapply_constraint_system \<sigma> cs2))"

inductive rer_star :: "constraint_system \<Rightarrow>subst_msg \<Rightarrow> constraint_system \<Rightarrow> bool"
("_/ \<leadsto>\<^emph>[_]/ _ " [73,73,73]72) where
Refl: "cs \<leadsto>\<^emph>[Variable] cs"
| Trans: "\<lbrakk>cs \<leadsto>[\<sigma>] cs''; cs'' \<leadsto>\<^emph>[\<tau>] cs'\<rbrakk> \<Longrightarrow> cs \<leadsto>\<^emph>[\<tau> \<circ>\<^sub>s \<sigma>] cs'"


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
"red cs = {\<tau> \<circ>\<^sub>s \<sigma> | \<sigma> \<tau> cs'. simple_constraint_system cs' \<and> \<tau> \<in> sol cs' \<and> cs \<leadsto>\<^emph>[\<sigma>] cs'}"

subsection \<open>Assignment 8\<close>
(*Soundness, lemmas:*)

lemma lemma7: "\<lbrakk>c \<leadsto>\<^sub>1[\<sigma>] cs; \<tau> \<in> sol cs\<rbrakk> \<Longrightarrow>  \<tau> \<circ>\<^sub>s \<sigma> \<in> sol [c]"
  by(erule rer1.cases) (auto simp add:sol_def)

thm Context

lemma lemma8: 
  assumes 1: "cs \<leadsto>[\<sigma>] cs'" and 2:"\<tau> \<in> sol cs'" 
  shows "\<tau> \<circ>\<^sub>s \<sigma> \<in> sol cs"
proof -
  from 1 obtain c css cs1 cs2
    where 3: "c \<leadsto>\<^sub>1[\<sigma>] css"
      and 4: "cs = cs1@c#cs2"
      and 5: "cs' = (sapply_constraint_system \<sigma> cs1) @ css @ (sapply_constraint_system \<sigma> cs2)"
    by (rule rer.cases) auto
  from 2 5 have "\<tau> \<in> sol (sapply_constraint_system \<sigma> cs1)"
    and "\<tau> \<in> sol (css)"
    and "\<tau> \<in> sol (sapply_constraint_system \<sigma> cs2)"
    using sol_inter by auto
  hence 6: "\<tau> \<circ>\<^sub>s \<sigma> \<in> sol cs1" and 7: "\<tau> \<circ>\<^sub>s \<sigma> \<in> sol cs2" using sol_subs by auto
  from 3 \<open>\<tau> \<in> sol (css)\<close> have 8: "\<tau> \<circ>\<^sub>s \<sigma> \<in> sol [c]" using lemma7 by auto
  from 6 8 7 4 show ?thesis using  sol_inter_mult by auto
qed

lemma lemma9: 
  assumes "cs \<leadsto>\<^emph>[\<sigma>] cs'" 
    and "simple_constraint_system cs'" 
    and "\<tau> \<in> sol cs'" 
  shows "\<tau> \<circ>\<^sub>s \<sigma> \<in> sol cs"
  using assms
proof(induction cs \<sigma> cs' rule:rer_star.induct)
  case (Trans cs \<rho> cs' \<rho>' cs'')
  then have "\<tau> \<circ>\<^sub>s \<rho>' \<in> sol cs'" by auto
  with \<open>cs \<leadsto>[\<rho>] cs'\<close> have "(\<tau> \<circ>\<^sub>s \<rho>') \<circ>\<^sub>s \<rho> \<in> sol cs" 
    using lemma8  by auto
  then show ?case by (simp add: scomp_msg_assoc)
qed simp

theorem sound_constraint_solve: "red cs \<subseteq> sol cs"
  using lemma9 by (auto simp add: red_def)

end