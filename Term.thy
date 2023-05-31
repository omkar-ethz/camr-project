theory Term
  imports Unification
begin

subsection \<open>Assignment 5\<close>

datatype symbol = Const string | iota | Hash | Pair | Senc | Aenc | Sign

datatype msg = Const string
  | \<iota>
  | Variable string
  | Hash msg ("\<h>(_)")
  | Pair msg msg ("\<langle>_,_\<rangle>" [59,59]58)
  | Senc msg msg ("\<lbrace>_\<rbrace>\<^sub>_" [57,57]56)
  | Aenc msg msg ("{_}\<^sub>_" [57,57]56)
  | Sign msg msg ("[_]\<^sub>_" [57,57]56)

value "\<lbrace>\<langle>a,\<h>(b)\<rangle>\<rbrace>\<^sub>c = Senc (Pair a \<h> b) c"
                     
fun arity :: "symbol \<Rightarrow> nat" where
"arity (symbol.Const _)= 0"
| "arity iota = 0"
| "arity symbol.Hash = 1"
| "arity _ = 2"

fun embed :: "msg \<Rightarrow> (symbol, string) term " where
"embed (Variable v) = Var v"
| "embed (msg.Const c) = Fun (symbol.Const c) []"
| "embed (msg.\<iota>) = Fun (iota) []"
| "embed (msg.Hash t) = Fun symbol.Hash [embed t]"
| "embed (msg.Pair t u) = Fun symbol.Pair [embed t, embed u]"
| "embed (msg.Senc t u) = Fun symbol.Senc [embed t, embed u]"
| "embed (msg.Aenc t u) = Fun symbol.Aenc [embed t, embed u]"
| "embed (msg.Sign t u) = Fun symbol.Sign [embed t, embed u]"

value "embed ({(\<langle>Const ''a'', Variable ''b''\<rangle>)}\<^sub>\<iota>)"

fun msg_of_term :: "(symbol, string) term \<Rightarrow> msg" where
"msg_of_term (Var v) = Variable v"
|  "msg_of_term (Fun (symbol.Const c) []) = msg.Const c"
|  "msg_of_term (Fun (iota) []) = msg.\<iota>"
| "msg_of_term (Fun symbol.Hash [t]) = msg.Hash (msg_of_term t)"
| "msg_of_term (Fun symbol.Pair [t,u]) = msg.Pair (msg_of_term t) (msg_of_term u)"
| "msg_of_term (Fun symbol.Senc [t,u]) =  msg.Senc (msg_of_term t) (msg_of_term u)"
| "msg_of_term (Fun symbol.Aenc [t,u]) =  msg.Aenc (msg_of_term t) (msg_of_term u)"
| "msg_of_term (Fun symbol.Sign [t,u]) =  msg.Sign (msg_of_term t) (msg_of_term u)"

value "msg_of_term (Fun symbol.Aenc [Fun symbol.Pair [Fun (symbol.Const ''a'') [], Var ''b''], Fun iota []])"

lemma wf_term_embed [simp]: "wf_term arity (embed msg)"
  by(induction msg) simp_all

lemma msg_of_term_embed [simp]: "msg_of_term (embed msg) = msg"
  by(induction msg) simp_all

lemma embed_msg_of_term [simp]: "wf_term arity t \<Longrightarrow> embed (msg_of_term t) = t"
  apply(induction t rule:msg_of_term.induct)
                      apply(simp_all)
  using arity.elims numerals(2) by auto

lemma wf_subst_embed [simp]: "wf_subst arity (embed \<circ> \<sigma>)"
  using  wf_term_embed by fastforce

lemma msg_of_term_inject:
"\<lbrakk>wf_term arity t1; wf_term arity t2 \<rbrakk> 
  \<Longrightarrow> msg_of_term t1 = msg_of_term t2 \<longleftrightarrow> t1 = t2"
  using embed_msg_of_term by fastforce

lemma type_definition_msg: 
"type_definition embed msg_of_term {t. wf_term arity t}"
  apply (standard) 
  using wf_term_embed by auto

setup_lifting type_definition_msg

type_synonym equation_msg = "msg \<times> msg"
type_synonym system_msg = "equation_msg list"


lift_definition fv_msg::"msg \<Rightarrow> string set" is fv
  done

lift_definition fv_eq_msg::"equation_msg \<Rightarrow> string set" is fv_eq
  done

lift_definition fv_sys_msg::"system_msg \<Rightarrow> string set" is fv_sys
  done

type_synonym subst_msg = "string \<Rightarrow> msg"

lift_definition sdom_msg::"subst_msg \<Rightarrow> string set" is sdom
  done

lift_definition svran_msg::"subst_msg \<Rightarrow> string set" is svran
  done

lift_definition sapply_msg::"subst_msg \<Rightarrow> msg \<Rightarrow> msg" is sapply
  by (simp add: wf_term_sapply)

lift_definition scomp_msg::"subst_msg \<Rightarrow> subst_msg \<Rightarrow> subst_msg"(infix "\<circ>\<^sub>s" 74) is scomp
  by (simp add:  wf_term_sapply)

lemma [simp]: "\<tau> \<circ>\<^sub>s Variable = \<tau>" by (simp add: scomp_msg_def) auto


lemma Variable_term: "sapply_msg Variable t = t"
  by(simp add: sapply_msg_def map_fun_def comp_def var_term)

lemma [simp]: "Variable \<circ>\<^sub>s \<tau> = \<tau>" 
  by(auto simp add: scomp_msg_def map_fun_def comp_def var_term)

lemma scomp_msg_assoc: "scomp_msg (\<sigma> \<circ>\<^sub>s \<tau>) \<rho> =  \<sigma> \<circ>\<^sub>s (\<tau> \<circ>\<^sub>s \<rho>)"
  apply transfer
  using scomp_assoc by blast

fun embed_subst::"subst_msg \<Rightarrow> (symbol, string)subst" where
"embed_subst \<sigma> m = embed (\<sigma> m)"

fun subst_to_subst_msg::"(symbol, string) subst \<Rightarrow> subst_msg" where
"subst_to_subst_msg \<sigma> s =  msg_of_term (\<sigma> s)"


fun embed_eqn::"equation_msg \<Rightarrow> (symbol, string) equation" where
"embed_eqn (m1, m2) = (embed m1, embed m2)"

fun msg_eqn_of_eqn::"(symbol, string) equation \<Rightarrow> equation_msg" where
"msg_eqn_of_eqn (u,t) = (msg_of_term u, msg_of_term t)"

fun embed_sys::"system_msg \<Rightarrow> (symbol,string) system" where
"embed_sys sys = map embed_eqn sys"

fun msg_sys_of_sys::"(symbol,string) system \<Rightarrow> system_msg" where
"msg_sys_of_sys sys = map msg_eqn_of_eqn sys"

lift_definition sapply_eq_msg::"subst_msg \<Rightarrow> equation_msg \<Rightarrow> equation_msg" is sapply_eq
  by (simp add: pred_prod_beta sapply_eq_def  wf_term_sapply)

definition sapply_sys_msg::"subst_msg \<Rightarrow> system_msg \<Rightarrow> system_msg" where
"sapply_sys_msg \<sigma> sys = msg_sys_of_sys (sapply_sys (embed_subst \<sigma>) (embed_sys sys))"

lift_definition unifies_msg::"subst_msg \<Rightarrow> equation_msg \<Rightarrow> bool" is unifies
  done

lift_definition unifiess_msg::"subst_msg \<Rightarrow> system_msg \<Rightarrow> bool" is unifiess 
  done



fun unify_msg::"system_msg \<Rightarrow> subst_msg option" where
"unify_msg sys = (case (unify (embed_sys sys)) of Some \<sigma> \<Rightarrow> Some (subst_to_subst_msg \<sigma>) | None \<Rightarrow> None)"

lemma unify_msg_correct: 
  assumes "unify_msg sys = (Some \<sigma>)" 
  shows "unifiess_msg \<sigma> sys"
proof -
  from assms
  obtain \<tau> where "unify (embed_sys sys) = Some \<tau>" by fastforce
  hence "unifiess \<tau> (embed_sys sys)" using unify_correct by blast
  moreover from assms have "\<sigma> = subst_to_subst_msg \<tau>" using \<open>unify (embed_sys sys) = Some \<tau>\<close> by auto
  with assms show ?thesis
    sorry
qed


lemma lemma3_msg:
  assumes "unify_msg sys = Some \<sigma>"
  shows 1: "fv_sys_msg (sapply_sys_msg \<sigma> sys) \<subseteq> fv_sys_msg sys \<and> sdom_msg \<sigma> \<subseteq> fv_sys_msg sys \<and> svran_msg \<sigma> \<subseteq> fv_sys_msg sys"
  sorry

end