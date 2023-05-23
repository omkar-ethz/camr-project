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

lemma "{\<lbrace>m\<rbrace>\<^sub>k, {k}\<^sub>\<iota>} \<turnstile> (\<langle>m,([k]\<^sub>\<iota>)\<rangle>)" 
  oops

lemma deduce_weaken:
assumes "G \<turnstile> t " and "G \<subseteq> H "
shows "H \<turnstile> t "
  sorry
(*proof -
  obtain x where "x \<in> G" sorry
  with 2 have "x \<in> H" by auto
*)

lemma deduce_cut:
assumes "insert t H \<turnstile> u " and "H \<turnstile> t "
shows "H \<turnstile> u "
  sorry

end