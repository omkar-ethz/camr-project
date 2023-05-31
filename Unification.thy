theory Unification
  imports Main
begin

section \<open>Unification\<close>

subsection \<open>Assignment 1\<close>

datatype ('f,'v) "term" = Var 'v | Fun 'f "('f,'v) term list"

(*just some random terms to get a feel for the datatype*)
term "Var (1::nat)"
term "Fun a [Var (1::nat), (Fun a [Var (1::nat)])]"

value "\<Union> {{1::nat}, {2::nat}}"

fun fv :: "('f,'v) term \<Rightarrow> 'v set" where
"fv (Var x) = {x}"
| "fv (Fun f ts) = \<Union>(fv ` set(ts))"

value "fv (Fun a [Var (1::nat), (Fun b [Var (2::nat)])])"

type_synonym ('f,'v) subst = "'v \<Rightarrow> ('f,'v) term"

fun sapply :: "('f,'v) subst \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v) term" (infixr "\<cdot>" 67)
  where
"\<sigma> \<cdot> (Var x) = \<sigma> x"
| "\<sigma> \<cdot> Fun f ts = Fun f (map (sapply \<sigma>) ts)"

fun scomp :: "('f,'v) subst \<Rightarrow> ('f,'v) subst \<Rightarrow> ('f,'v) subst" (infixl "\<circ>\<^sub>s" 75)
  where 
"(\<sigma> \<circ>\<^sub>s \<tau>) x =  \<sigma> \<cdot> \<tau> x"

lemma fv_sapply: "fv (\<sigma> \<cdot> t) = (\<Union>x \<in> fv t. fv (\<sigma> x))"
  by(induction t rule:fv.induct) simp_all

lemma sapply_cong:
  assumes "\<And>x. x \<in> fv t \<Longrightarrow> \<sigma> x = \<tau> x"
  shows "\<sigma> \<cdot> t = \<tau> \<cdot> t"
  using assms by (induction t) auto

lemma scomp_sapply: "(\<sigma> \<circ>\<^sub>s \<tau> ) x = \<sigma> \<cdot> (\<tau> x)"
  by simp

lemma sapply_scomp_distrib: "(\<sigma> \<circ>\<^sub>s \<tau> ) \<cdot> t = \<sigma> \<cdot> (\<tau> \<cdot> t)"
  by (induction t) simp_all

lemma scomp_assoc: "(\<sigma> \<circ>\<^sub>s \<tau>) \<circ>\<^sub>s \<rho> =  \<sigma> \<circ>\<^sub>s (\<tau> \<circ>\<^sub>s \<rho>)"
  using sapply_scomp_distrib by fastforce

lemma scomp_Var [simp]: "\<sigma> \<circ>\<^sub>s Var = \<sigma>"
  by auto

lemma var_term: "Var \<cdot> t = t" 
  by (induction t) (simp_all add: list.map_ident_strong)

lemma Var_scomp [simp]: "Var \<circ>\<^sub>s \<sigma>= \<sigma>"
  by (auto simp add:var_term)

fun sdom :: "('f,'v) subst \<Rightarrow> 'v set" where
  "sdom \<sigma> = {x. (\<sigma> x \<noteq> Var x)}"

fun sran :: "('f,'v) subst \<Rightarrow> ('f,'v) term set" where
  "sran \<sigma> = {\<sigma> x |x. x \<in> sdom \<sigma>}"

fun svran :: "('f,'v) subst \<Rightarrow> 'v set" where
  "svran \<sigma> = (\<Union>t \<in> sran \<sigma>. fv t)"

lemma sdom_Var[simp]: "sdom Var = {}"
  by simp

lemma svran_Var[simp]: "svran Var = {}"
  by simp

lemma sdom_single_non_trivial[simp]: "t \<noteq> Var x \<Longrightarrow> sdom (Var(x:=t)) = {x}"
  by simp

lemma svran_single_non_trivial[simp]: "t \<noteq> Var x \<Longrightarrow> svran (Var(x:=t)) = fv t"
  by simp

lemma fv_apply_sdom_svran: "x \<in> fv (\<sigma> \<cdot> t) \<Longrightarrow> x \<in> (fv t - sdom \<sigma>) \<union> svran \<sigma>"
  apply(auto simp add: fv_sapply)
   apply force
  by (metis fv.simps(1) singletonD)

lemma sdom_scomp: "sdom (\<sigma> \<circ>\<^sub>s \<tau>) \<subseteq> sdom \<sigma> \<union> sdom \<tau>"
  by auto

lemma svran_scomp: "svran (\<sigma> \<circ>\<^sub>s \<tau>) \<subseteq> svran \<sigma> \<union> svran \<tau>"
  by(auto simp add:fv_sapply) force

subsection \<open>Assignment 2\<close>

type_synonym ('f,'v) equation = "('f,'v) term \<times> ('f,'v) term"

type_synonym ('f,'v) system = "('f,'v) equation list"

definition fv_eq :: "('f,'v) equation \<Rightarrow> 'v set" where
  "fv_eq x = fv (fst x) \<union> fv (snd x)"

definition sapply_eq :: "('f,'v) subst \<Rightarrow> ('f, 'v) equation \<Rightarrow> ('f,'v) equation"
  where
    "sapply_eq \<sigma> x = (sapply \<sigma> (fst x), sapply \<sigma> (snd x))"

definition fv_sys :: "('f,'v) system \<Rightarrow> 'v set" where
  "fv_sys x = Union (set (map fv_eq x))"

definition sapply_sys :: "('f,'v) subst \<Rightarrow> ('f,'v) system \<Rightarrow> ('f,'v) system"
  where
  "sapply_sys \<sigma> x = map (sapply_eq \<sigma>) x"

lemma fv_sapply_eq: "fv_eq (sapply_eq \<sigma> x) = (\<Union>x \<in> fv_eq x. fv (\<sigma> x))"
  by (simp add: fv_eq_def sapply_eq_def fv_sapply)

lemma fv_sapply_sys: "fv_sys (sapply_sys \<sigma> x) = (\<Union>x \<in> fv_sys x. fv (\<sigma> x))"
  by (simp add: fv_sys_def sapply_sys_def fv_sapply_eq)

lemma sapply_scomp_distrib_eq: "sapply_eq (\<sigma> \<circ>\<^sub>s \<tau> ) t = sapply_eq \<sigma> (sapply_eq \<tau>  t)"
  by (simp add: sapply_eq_def sapply_scomp_distrib)

lemma sapply_scomp_distrib_sys: "sapply_sys (\<sigma> \<circ>\<^sub>s \<tau> ) t = sapply_sys \<sigma> (sapply_sys \<tau>  t)"
  by (simp add: sapply_sys_def sapply_scomp_distrib_eq)

fun unifies :: "('f,'v) subst \<Rightarrow> ('f,'v) equation \<Rightarrow> bool" where
"unifies \<sigma> (t, u) = (\<sigma> \<cdot> t = \<sigma> \<cdot> u)"  (* chsp: if b then True else False = b *)

value "let \<sigma>=(\<lambda>x.(if x = ''b'' then Var ''a'' else Var x)) 
  in unifies \<sigma> (Fun f [Var ''a'', Var ''b''], Fun f [Var ''b'', Var ''a''])"

fun unifiess :: "('f,'v) subst \<Rightarrow> ('f,'v) system \<Rightarrow> bool" where
  "unifiess \<sigma> [] = True"
|  "unifiess \<sigma> (eq#eqs) = (unifies \<sigma> eq \<and> unifiess \<sigma> eqs)"

(*Some auxiliary lemmas to help with soundness proof*)
lemma unifies_hd: "unifiess \<sigma> (eq#eqs) \<Longrightarrow> unifies \<sigma> eq" by auto
lemma unifiess_tail: "unifiess \<sigma> (eq#eqs) \<Longrightarrow> unifiess \<sigma> eqs" by auto
lemma unifiess_append1: "unifiess \<sigma> (eq1@eq2) \<Longrightarrow> unifiess \<sigma> eq1" by(induction eq1) simp_all
lemma unifiess_append2: "unifiess \<sigma> (eq1@eq2) \<Longrightarrow> unifiess \<sigma> eq2" by(induction eq1) simp_all

lemma temp1: "unifiess \<sigma> (zip [] []) = True" by auto
lemma temp: "unifiess \<sigma> (zip (x#xs) (y#ys)) = (unifies \<sigma> (x,y) \<and> unifiess \<sigma> (zip xs ys))" by auto
lemma unif_alt[simp]: "unifiess \<sigma> xs = (\<forall>x\<in>set(xs). unifies \<sigma> x)" by (induction xs) simp_all

lemma unifies_Fun: "unifiess \<sigma> ((Fun f xs, Fun g ys)#eqs) \<Longrightarrow> f=g"
  by simp

lemma unifies_Fun_arg_len: "unifiess \<sigma> ((Fun f xs, Fun g ys)#eqs) \<Longrightarrow> length xs = length ys"
  apply (induction \<sigma> eqs rule: unifiess.induct)
   apply simp_all
  by (metis length_map)

lemma unifies_Fun_arg: "unifies \<sigma> (Fun f xs, Fun g ys) \<longleftrightarrow> unifiess \<sigma> (zip xs ys)"
  apply (induction \<sigma> "(zip xs ys)" rule: unifiess.induct)
   apply simp
  sorry

(* asserts that \<sigma> is more general than \<tau> *)
definition is_more_general :: "('f,'v) subst \<Rightarrow> ('f,'v) subst \<Rightarrow> bool" where
"is_more_general \<sigma> \<tau> = (\<exists>\<rho>. \<rho> \<circ>\<^sub>s \<sigma> = \<tau>)"

definition is_mgu :: "('f,'v) subst \<Rightarrow> ('f,'v) system \<Rightarrow> bool" where
  "is_mgu \<sigma> eqs = (unifiess \<sigma> eqs \<and> (\<nexists> \<tau>. unifiess \<tau> eqs \<and> is_more_general \<tau> \<sigma>))"

lemma unifies_sapply_eq: "unifies \<sigma> (sapply_eq \<tau> eq) \<longleftrightarrow> unifies (\<sigma> \<circ>\<^sub>s \<tau>) eq"
  apply(auto)
  subgoal apply(auto simp add:sapply_eq_def)
    by (metis sapply_scomp_distrib surjective_pairing unifies.simps)
  apply(auto simp add:sapply_eq_def)
  by (metis sapply_scomp_distrib surjective_pairing unifies.simps)

lemma unifies_sapply_sys: "unifiess \<sigma> (sapply_sys \<tau> sys) \<longleftrightarrow> unifiess (\<sigma> \<circ>\<^sub>s \<tau>) sys"
  unfolding sapply_sys_def apply simp
  using unifies_sapply_eq by fastforce


subsection \<open>Assignment 3\<close>

fun size_term :: "('f,'v) term \<Rightarrow> nat" where
"size_term (Var _)= 0"
| "size_term (Fun f ts) = 1 + sum_list (map size_term ts)"

fun size_term_sys :: "('f,'v) system \<Rightarrow> nat" where
"size_term_sys [] = 0"
| "size_term_sys ((t,u) # eqs) = size_term t + size_term_sys eqs"

(*some lemmas to help with termination proof:*)
lemma finite_fv [termination_simp]: "finite (fv x)" by (induction rule:fv.induct) simp_all 

lemma finite_fv_sys [termination_simp]: "finite (fv_sys eqs)"
  unfolding fv_sys_def fv_eq_def
  using finite_fv by auto

lemma card_fv_sys: "x \<notin> fv t \<Longrightarrow>
    card (fv_sys (sapply_sys (Var(x := t)) eqs))
    < card (fv_sys ((Var x, t) # eqs))"
  apply(auto simp only: fv_sapply_sys finite_fv_sys)
  using fv_sapply_sys finite_fv_sys
  sorry


(*
  chsp: in equation Fun: check that the xs and ys have the same length -- DONE \<checkmark>
*)
function (sequential) unify :: "('f,'v) system \<Rightarrow> ('f,'v) subst option" where
"unify [] = Some Var"
| Var: "unify ((Var x, t) # eqs) = (
  if x \<notin> fv t 
    then let ans = unify (sapply_sys (Var(x:=t)) eqs) in
      case ans of None \<Rightarrow> None
      | Some sub \<Rightarrow> Some (sub \<circ>\<^sub>s Var(x:=t))
  else if Var x = t
    then unify eqs
  else None
)"
| Swap: "unify ((u, Var x) # eqs) = unify ((Var x, u) # eqs)"
| Fun: "unify ((Fun f xs, Fun g ys) # eqs) = (if f=g  \<and> length xs = length ys then unify ((zip xs ys) @ eqs) else None)"
  by pat_completeness auto
termination 
  (* chsp: note that (\<lambda>sys. size_term_sys sys) will eta-reduce to size_term_sys  -- DONE \<checkmark>*)
  apply(relation "measures [(\<lambda>sys. card (fv_sys sys)), size_term_sys, size]")
      apply simp
     apply(simp add: card_fv_sys)
  thm card_mono psubset_card_mono
  sorry

value "unify [(Var x, Fun f []), (Fun g [Var x], Fun g [Fun f []])]"

(*Soundness:
(i) If unify returns a substitution, it is a unifier.
(ii) If unify returns a substitution \<sigma> and there is another unifier \<tau> , then
\<tau> = \<rho> \<circ>\<^sub>s \<sigma> for some \<rho>.*)

(*Auxiliary lemma for case Var of \<open>unify\<close>*)
lemma unify_case_Var: assumes 
1:"\<lbrakk>x \<notin> fv t; unify (sapply_sys (Var(x := t)) eqs) = Some \<sigma>\<rbrakk>
    \<Longrightarrow> unifiess \<sigma> (sapply_sys (Var(x := t)) eqs)"
    and 2: "\<lbrakk>\<not> x \<notin> fv t; Var x = t; unify eqs = Some \<sigma>\<rbrakk> \<Longrightarrow> unifiess \<sigma> eqs"
    and 3: "unify ((Var x, t) # eqs) = Some \<sigma>"
  shows "unifiess \<sigma> ((Var x, t) # eqs)"
proof(cases "x \<notin> fv t")
  case True (*case Unify of the \<open>unify\<close>, could not prove*)
  let ?\<sigma>' = "\<sigma> \<circ>\<^sub>s (Var(x := t))"
  have "Var(x := t) \<cdot> Var x = Var(x := t) \<cdot> t"
    by (metis True fun_upd_other fun_upd_same sapply.simps(1) sapply_cong var_term)
  hence "?\<sigma>' \<cdot> (Var x) = ?\<sigma>' \<cdot> t" by (simp add: sapply_scomp_distrib)
  with 3 have "unify (sapply_sys (Var(x := t)) eqs) = Some \<sigma>" sorry
  hence "unifiess \<sigma> (sapply_sys (Var(x := t)) eqs)"
    using "1" True by blast
  then have "unifiess ?\<sigma>' eqs" 
    using unifies_sapply_sys by blast
  then show ?thesis sorry
next
  case False (*case Simp of the \<open>unify\<close>*)
  from 2 have "unifiess \<sigma> eqs"
    by (metis "3" False Unification.Var option.discI)
  with 2 have \<open>Var x = t\<close> using "3" False by force 
  with \<open>unifiess \<sigma> eqs\<close> show ?thesis by auto
qed 


theorem unify_correct: "unify sys = (Some \<sigma>) \<Longrightarrow> unifiess \<sigma> sys"
proof(induction sys rule:unify.induct)
  case (2 x t eqs)
  thus ?case using unify_case_Var by fast
next
  case (4 f xs g ys eqs) (*case Fun of the \<open>unify\<close>*)
  from 4 have \<open>f=g\<close> by (metis Unification.Fun option.distinct(1))
  from 4 have \<open>length xs = length ys\<close> by (metis Unification.Fun option.distinct(1))
  from 4 have \<open>unify (zip xs ys @ eqs) = Some \<sigma>\<close> by (simp add: \<open>f = g\<close> \<open>length xs = length ys\<close>)
  with \<open>f = g\<close> \<open>length xs = length ys\<close> 4 have "unifiess \<sigma> (zip xs ys @ eqs)" by auto
  have "unifiess \<sigma> ((Fun f xs, Fun g ys) # eqs) = (unifies \<sigma> (Fun f xs, Fun g ys) \<and> unifiess \<sigma> eqs)" by simp
  from \<open>unifiess \<sigma> (zip xs ys @ eqs)\<close> have "unifiess \<sigma> (zip xs ys)" by (auto intro:unifiess_append1)
  from \<open>f = g\<close> \<open>length xs = length ys\<close> \<open>unifiess \<sigma> (zip xs ys)\<close> 
    have "unifies \<sigma> (Fun f xs, Fun g ys)" using unifies_Fun_arg by metis
  hence  11: "unifiess \<sigma> ((Fun f xs, Fun g ys) # eqs) = unifiess \<sigma> eqs" by simp
  from \<open>unifiess \<sigma> (zip xs ys @ eqs)\<close> have 22: "unifiess \<sigma> eqs" by (auto intro:unifiess_append2)
  from 11 22 show ?case by auto
qed auto (*Swap and base case go away by auto*)

lemma unify_mgu: "\<lbrakk>unify sys = (Some \<sigma>); unifiess \<tau> sys; \<tau> \<noteq> \<sigma>\<rbrakk> \<Longrightarrow> \<exists>\<rho>. \<tau> = \<rho> \<circ>\<^sub>s \<sigma>"
  sorry


lemma lemma2: "\<exists>\<tau>. unifiess \<tau> sys \<Longrightarrow> unify sys \<noteq> None"
proof(induction rule:unify.induct)
  case (2 x t eqs)
  then obtain \<tau> where "unifiess \<tau> ((Var x, t) # eqs)" by auto
  then show ?case sorry
next
  case (3 v va x eqs)
  then show ?case
    by (metis Unification.Swap unifies.simps unifiess.simps(2))
next
  case (4 f xs g ys eqs)
  from 4(2) have "f = g" by simp
  from 4 obtain \<tau> where "unifiess \<tau> ((Fun f xs, Fun g ys) # eqs)" by auto
  then have \<open>length xs = length ys\<close>  using unifies_Fun_arg_len by simp
  from \<open>f = g\<close> \<open>length xs = length ys\<close> 4(2) have "unify (zip xs ys @ eqs) \<noteq> None" 
    using 4(1) unifies_Fun_arg by fastforce
  then show ?case using unifies_Fun_arg by (simp add: \<open>f = g\<close> \<open>length xs = length ys\<close>)
qed simp

theorem unify_complete: "\<exists>\<tau>. unifiess \<tau> sys \<Longrightarrow> \<exists>\<sigma>. unify sys = Some \<sigma>"
  using lemma2  by auto


lemma lemma3:
  assumes "unify sys = Some \<sigma>"
  shows 1: "fv_sys (sapply_sys \<sigma> sys) \<subseteq> fv_sys sys \<and> sdom \<sigma> \<subseteq> fv_sys sys \<and> svran \<sigma> \<subseteq> fv_sys sys"
  using assms
proof(induction sys rule:unify.induct)
  case (2 x t eqs)
  then show ?case sorry
next
  case (4 f xs g ys eqs)
  from 4 have \<open>f=g\<close> by (metis Unification.Fun option.distinct(1))
  moreover from 4 have \<open>length xs = length ys\<close> by (metis Unification.Fun option.distinct(1))
  moreover from 4 have \<open>unify (zip xs ys @ eqs) = Some \<sigma>\<close> by (simp add: \<open>f = g\<close> \<open>length xs = length ys\<close>)
  ultimately have "fv_sys (sapply_sys \<sigma> (zip xs ys @ eqs)) \<subseteq> fv_sys (zip xs ys @ eqs) \<and>
        sdom \<sigma> \<subseteq> fv_sys (zip xs ys @ eqs) \<and> svran \<sigma> \<subseteq> fv_sys (zip xs ys @ eqs)" 
    using 4(1) by simp 
  then show ?case sorry

qed (auto simp add:fv_sys_def sapply_sys_def fv_eq_def sapply_eq_def)


subsection \<open>Assignment 4\<close>

fun wf_term :: "('f \<Rightarrow> nat) \<Rightarrow> ('f,'v) term \<Rightarrow> bool" where
"wf_term ar (Var _) = True"
| "wf_term ar (Fun f ts) =  ((ar f  = size ts) \<and> (\<forall>t\<in>set(ts). wf_term ar t))"

value "wf_term (\<lambda>a.2) (Fun a [Var (1::nat), (Fun b [Var (1::nat), Var c])])"

fun wf_subst :: "('f \<Rightarrow> nat) \<Rightarrow> ('f,'v) subst \<Rightarrow> bool " where
"wf_subst ar \<sigma>  = (\<forall>x. wf_term ar (\<sigma> x))"

fun wf_eq::"('f \<Rightarrow> nat) \<Rightarrow> ('f,'v) equation \<Rightarrow> bool" where
"wf_eq ar (u,t) = (wf_term ar u \<and> wf_term ar t)"

fun wf_eqs::"('f \<Rightarrow> nat) \<Rightarrow> ('f,'v) system \<Rightarrow> bool" where
"wf_eqs ar sys = (\<forall>eq\<in>set sys. wf_eq ar eq)"

lemma wf_subst_var[simp]:
  fixes x
  assumes "wf_subst arity \<sigma>"
  shows "wf_term arity (\<sigma> x)"
using assms by simp

lemma wf_term_sapply:
"\<lbrakk>wf_term arity t; wf_subst arity \<sigma>\<rbrakk> \<Longrightarrow> wf_term arity (\<sigma> \<cdot> t)"
  by(induction t) simp_all

lemma wf_subst_scomp:
"\<lbrakk>wf_subst arity \<sigma>; wf_subst arity \<tau>\<rbrakk> \<Longrightarrow> wf_subst arity (\<sigma> \<circ>\<^sub>s \<tau>)"
  using wf_term_sapply
  by (metis scomp.elims wf_subst.elims(1))

lemma wf_fun_eq: "wf_eq arity ((Fun f xs, Fun g ys)) \<Longrightarrow> wf_eqs arity (zip xs ys)"
  using set_zip_leftD set_zip_rightD by fastforce

(*some trivial lemmas to prove wf_fun_eqs*)
lemma wf_eq1: "wf_eqs arity (eq#eqs) \<Longrightarrow> wf_eq arity eq" by simp
lemma wf_eq2: "wf_eqs arity (eq#eqs) \<Longrightarrow> wf_eqs arity eqs" by simp

lemma wf_fun_eqs: "wf_eqs arity ((Fun f xs, Fun g ys)#eqs) \<Longrightarrow> wf_eqs arity ((zip xs ys)@eqs)"
  using wf_eq1 wf_eq2
  by (metis UnE set_append wf_eqs.elims(1) wf_fun_eq)

thm unify.induct

lemma temp_unproved_lemma: "\<lbrakk> x \<notin> fv t; unify ((Var x, t) # eqs) = Some \<sigma>\<rbrakk> 
          \<Longrightarrow> unify (sapply_sys (Var(x := t)) eqs) = Some \<sigma>"
proof(induction "((Var x, t) # eqs)" rule:unify.induct)
  case 2
  obtain \<sigma>' where 1: "unify ((Var x, t) # eqs) = Some (\<sigma>' \<circ>\<^sub>s Var(x:=t))"
    by (metis (no_types, lifting) "2.prems"(1) "2.prems"(2) Unification.Var option.case_eq_if option.distinct(1))
  have "Var(x := t) \<cdot> Var x = Var(x := t) \<cdot> t"
    by (metis 2(3) fun_upd_other fun_upd_same sapply.simps(1) sapply_cong var_term)
  (*hence "\<sigma>' \<cdot> (Var x) = \<sigma>' \<cdot> t" by (simp add: sapply_scomp_distrib)*)
  have "\<sigma>' \<circ>\<^sub>s Var(x:=t) = \<sigma>" using \<open>unify ((Var x, t) # eqs) = Some \<sigma>\<close> \<open>unify ((Var x, t) # eqs) = Some (\<sigma>' \<circ>\<^sub>s Var(x:=t))\<close> by simp
  from 1 \<open>unify ((Var x, t) # eqs) = Some \<sigma>\<close> have "unify (sapply_sys (Var(x := t)) eqs) = Some \<sigma>'" sorry
  thus ?thesis sorry
qed

lemma wf_subst_1: "\<lbrakk>x \<notin> fv t; wf_term ar t\<rbrakk> \<Longrightarrow> wf_subst ar (Var(x := t))" by simp

lemma wf_eqs_var_sapply: assumes "x \<notin> fv t" "wf_eqs arity ((Var x, t) # eqs)"
shows "wf_eqs arity (sapply_sys (Var(x := t)) eqs)"
proof -
  have "wf_eq arity (Var x,t)" using \<open>wf_eqs arity ((Var x, t) # eqs)\<close> by simp
  hence "wf_term arity t" by simp
  hence 1: "wf_subst arity (Var(x := t))" using wf_subst_1 by simp
  with assms(2) show ?thesis unfolding sapply_sys_def sapply_eq_def using  wf_term_sapply
    by fastforce
qed

lemma wf_subst_unify:
"\<lbrakk>unify eqs = Some \<sigma>; wf_eqs arity eqs\<rbrakk> \<Longrightarrow> wf_subst arity \<sigma>"
proof(induction eqs rule:unify.induct)
  case (2 x t eqs)
  thm 2
  then show ?case 
  proof(cases  "x \<notin> fv t") (*case Unify*)
    case True
    from 2(3) True have "unify (sapply_sys (Var(x := t)) eqs) = Some \<sigma>" 
      using temp_unproved_lemma by fast
    moreover from 2(4) True have "wf_eqs arity (sapply_sys (Var(x := t)) eqs)" 
      using wf_eqs_var_sapply by metis
    ultimately show ?thesis using 2(1) True by blast
  next (*case Simp*)
    case False
    from False 2(3) have "Var x = t" by fastforce
    moreover with False 2(3) have "unify eqs = Some \<sigma>" by auto
    moreover from 2(4) have "wf_eqs arity eqs" by simp
    ultimately show ?thesis using False 2(2) by auto
  qed
next
  case (4 f xs g ys eqs)
  from 4 have p1: \<open>f=g\<close> by (metis Unification.Fun option.distinct(1))
  from 4 have p2: \<open>length xs = length ys\<close> by (metis Unification.Fun option.distinct(1))
  from 4 have p3: \<open>unify (zip xs ys @ eqs) = Some \<sigma>\<close> by (simp add: \<open>f = g\<close> \<open>length xs = length ys\<close>)
  with p1 p2 4  show ?case using wf_fun_eqs by fast
qed auto

end
