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
"unifies \<sigma> (t, u) = (if \<sigma> \<cdot> t = \<sigma> \<cdot> u then True else False)"

value "let \<sigma>=(\<lambda>x.(if x = ''b'' then Var ''a'' else Var x)) 
  in unifies \<sigma> (Fun f [Var ''a'', Var ''b''], Fun f [Var ''b'', Var ''a''])"

fun unifiess :: "('f,'v) subst \<Rightarrow> ('f,'v) system \<Rightarrow> bool" where
  "unifiess \<sigma> eqs = fold (\<and>) (map (unifies \<sigma>) eqs) True"

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
(*sledgehammer finds a proof with smt, 
todo find a better proof as smt is not allowed (grading guidelines)*)
  oops


  subsection \<open>Assignment 3\<close>

function (sequential) unify :: "('f , 'v) system \<Rightarrow> ('f , 'v) subst option" where
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
| Fun: "unify ((Fun f xs, Fun g ys) # eqs) = (if f=g then unify ((zip xs ys) @ eqs) else None)"
  by pat_completeness auto
termination sorry


value "unify [(Var x, Fun f []), (Fun g [Var x], Fun g [Fun f []])]"


subsection \<open>Assignment 4\<close>

value "fold (+) ([1,2,3]) (0::nat)"

fun wf_term :: "('f \<Rightarrow> nat) \<Rightarrow> ('f,'v) term \<Rightarrow> bool" where
"wf_term ar t = (case t of Var _ \<Rightarrow> True | 
  Fun f ts \<Rightarrow> ar f  = size ts
  \<and> (fold (\<and>) (map (wf_term ar) ts) True))"

value "wf_term (\<lambda>a.2) (Fun a [Var (1::nat), (Fun b [Var (1::nat), Var c])])"

definition wf_subst :: "('f \<Rightarrow> nat) \<Rightarrow> ('f,'v) subst \<Rightarrow> bool " where
"wf_subst ar \<sigma>  = (\<forall>x. wf_term ar (\<sigma> x))"
(*"wf_subst ar \<sigma> = (False \<notin> wf_term ar ` sran \<sigma>)" *)
(*not executable as sran and sdom is not executable in general, 
only executable when 'v is a finite type which is the expected case*)

term "wf_subst (\<lambda>a.1) (\<lambda>x.(Var x))"

lemma [simp]:
  assumes "wf_subst ar \<sigma>"
  fixes x
  shows "wf_term ar (\<sigma> x)"
  using assms by (simp add:wf_subst_def)

lemma wf_term_sapply:
"\<lbrakk>wf_term arity t; wf_subst arity \<sigma>\<rbrakk> \<Longrightarrow> wf_term arity (\<sigma> \<cdot> t)"
  oops

lemma wf_subst_scomp:
"\<lbrakk>wf_subst arity \<sigma>; wf_subst arity \<tau>\<rbrakk> \<Longrightarrow> wf_subst arity (\<sigma> \<circ>\<^sub>s \<tau>)"
  oops


end