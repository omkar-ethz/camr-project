theory Execute
  imports Deduction
begin


function (sequential) suc_rer1::"constraint \<Rightarrow> (constraint_system \<times> subst_msg)" where
"suc_rer1 (M | A \<Zrres> (Variable v)) =  (Nil, Variable)"

|CompHashF: "suc_rer1 (M | A \<Zrres> (\<h> t)) =  ([M | A \<Zrres> t], Variable)"
| CompPairF: "suc_rer1 (M | A \<Zrres> (\<langle>t1,t2\<rangle>)) = ([M | A \<Zrres> t1, M | A \<Zrres> t2], Variable)"
| CompSencF: "suc_rer1 (M | A \<Zrres> (\<lbrace>t\<rbrace>\<^sub>k)) =  ([M | A \<Zrres> t, M | A \<Zrres> k], Variable)"
| CompAencF: "suc_rer1 (M | A \<Zrres> ({t}\<^sub>k)) = ([M | A \<Zrres> t, M | A \<Zrres> k], Variable)"
| CompSignF: "suc_rer1 (M | A \<Zrres> ([t]\<^sub>\<iota>)) = ([M | A \<Zrres> t], Variable)"
| AnalysisNil: "suc_rer1 ([] | A \<Zrres> t) = (Nil, Variable)"
| AnalysisCons: "suc_rer1 ((m#M) | A \<Zrres> t) = 
    (case m of (\<langle>u,v\<rangle>) \<Rightarrow> ([(u#v#M) | ((\<langle>u,v\<rangle>)#A) \<Zrres> t] @ (fst (suc_rer1 (M | A \<Zrres> t))), (snd (suc_rer1 (M | A \<Zrres> t))))
    | (\<lbrace>u\<rbrace>\<^sub>k) \<Rightarrow> undefined
    | ({u}\<^sub>\<iota>) \<Rightarrow> undefined
    | ({u}\<^sub>x) \<Rightarrow> undefined
    )"
  by pat_completeness auto
termination sorry

(*| ProjF: "suc_rer1 ((M1@(\<langle>u,v\<rangle>)#M2) | A \<Zrres> t) = ([(u#v#M1@M2) | ((\<langle>u,v\<rangle>)#A) \<Zrres> t],Variable)"
| SdecF: "suc_rer1 ((M1@(\<lbrace>u\<rbrace>\<^sub>k)#M2) | A \<Zrres> t) = 
                ([(u#M1@M2) | ((\<lbrace>u\<rbrace>\<^sub>k)#A) \<Zrres> t, (M1@M2) | ((\<lbrace>u\<rbrace>\<^sub>k)#A) \<Zrres> k], Variable)"
| AdecF: "suc_rer1 ((M1@({u}\<^sub>\<iota>)#M2) | A \<Zrres> t) = ([(u#M1@M2) | (({u}\<^sub>\<iota>)#A) \<Zrres> t], Variable)"
*)

fun suc_rer::"constraint_system \<Rightarrow> (constraint_system \<times> subst_msg)" where
"suc_rer [] = undefined"
| "suc_rer (c#cs) = (fst (suc_rer1 c) @ (sapply_constraint_system (snd (suc_rer1 c)) cs), snd (suc_rer1 c))"

end