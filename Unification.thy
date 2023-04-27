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
| "fv (Fun f ts) = (\<Union>t\<in>set(ts). fv t)"

value "fv (Fun a [Var (1::nat), (Fun a [Var (2::nat)])])"

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
proof(cases t)
  case (Var x)
  then show ?thesis using assms by simp
next
  case (Fun f ts)
  then show ?thesis sorry
qed

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
  "sdom \<sigma> = \<Union>x. \<sigma> x \<noteq> x"

fun sran :: "('f,'v) subst \<Rightarrow> 'v set" where
  "sran \<sigma> = set (map \<sigma> (sdom \<sigma>))"

fun svran :: "('f,'v) subst \<Rightarrow> 'v set" where
  "svran \<sigma> = (\<Union>t \<in> sran \<sigma>. fv t)" 

lemma sdom_Var[simp]: "sdom Var = {}"
  oops

lemma svran_Var[simp]: "svran Var = {}"
  oops

lemma sdom_single_non_trivial[simp]: "t \<noteq> Var x \<Longrightarrow> sdom (Var (x:=t)) = {x}"
  oops

lemma svran_single_non_trivial[simp]: "t \<noteq> Var x \<Longrightarrow> svran (Var (x:=t)) = {x}"
  oops

lemma fv_apply_sdom_svran: "x \<in> (fv t - sdom \<sigma>) \<union> svran \<sigma>"
  oops

lemma sdom_scomp: "sdom (\<sigma> \<circ>\<^sub>s \<tau>) \<subseteq> sdom \<sigma> \<union> sdom \<tau>"
  oops

lemma svran_scomp: "svran (\<sigma> \<circ>\<^sub>s \<tau>) \<subseteq> svran \<sigma> \<union> svran \<tau>"
  oops

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

fun unifies :: "('f,'v) subst \<Rightarrow> ('f,'v) equation \<Rightarrow> bool"
  where
    "unifies \<sigma> (Var x, Var y) = (if \<sigma> x = \<sigma> y then True else False)"
  | "unifies \<sigma> (Var x, Fun f xs) = False"
  | "unifies \<sigma> (Fun f xs, Var y) = False"
  | "unifies \<sigma> (x, y) = all (map (unifies \<sigma>) (\<sigma> \<cdot> x, \<sigma> \<cdot> y))"

definition unifiess :: "('f,'v) subst \<Rightarrow> ('f,'v) system \<Rightarrow> bool" where
  "unifiess \<sigma> x = all (map (unifies \<sigma>) x)"

fun is_mgu :: "('f,'v) subst \<Rightarrow> ('f,'v) system \<Rightarrow> bool" where
  "is_mgu \<sigma> x = True"

lemma unifies_sapply_eq: "unifies \<sigma> (sapply_eq \<tau> eq) \<longleftrightarrow> unifies (\<sigma> \<circ>\<^sub>s \<tau>) eq"
  oops

lemma unifies_sapply_sys: "unifiess \<sigma> (sapply_sys \<tau> sys) \<longleftrightarrow> unifiess (\<sigma> \<circ>\<^sub>s \<tau>) sys"
  oops

end