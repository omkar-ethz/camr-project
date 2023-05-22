theory Term
  imports Unification
begin

datatype msg = Const string
  | Variable string
  | Hash msg
  | Pair msg msg
  | Senc msg msg
  | Aenc msg msg
  | Sign msg msg

term "Var ''a''"
term "Fun (1::nat) [Var ''a'']"

datatype symbol = Const string | Hash | Pair | Senc | Aenc | Sign

term "msg.Hash a"
                     
fun arity :: "symbol \<Rightarrow> nat" where
"arity (Const _)= 0"
| "arity Hash = 1"
| "arity _ = 2"

fun embed :: "msg \<Rightarrow> (symbol, string) term " where
"embed (Variable v) = Var v"
| "embed (msg.Const c) = Fun (symbol.Const c) []"
| "embed (msg.Hash t) = Fun symbol.Hash [embed t]"
| "embed (msg.Pair t u) = Fun symbol.Pair [embed t, embed u]"
| "embed (msg.Senc t u) = Fun symbol.Senc [embed t, embed u]"
| "embed (msg.Aenc t u) = Fun symbol.Aenc [embed t, embed u]"
| "embed (msg.Sign t u) = Fun symbol.Sign [embed t, embed u]"

fun msg_of_term :: "(symbol, string) term \<Rightarrow> msg" where
"msg_of_term (Var v) = Variable v"
|  "msg_of_term (Fun (symbol.Const c) []) = msg.Const c"
| "msg_of_term (Fun symbol.Hash [t]) = msg.Hash (msg_of_term t)"
| "msg_of_term (Fun symbol.Pair [t,u]) = msg.Pair (msg_of_term t) (msg_of_term u)"
| "msg_of_term (Fun symbol.Senc [t,u]) =  msg.Senc (msg_of_term t) (msg_of_term u)"
| "msg_of_term (Fun symbol.Aenc [t,u]) =  msg.Aenc (msg_of_term t) (msg_of_term u)"
| "msg_of_term (Fun symbol.Sign [t,u]) =  msg.Sign (msg_of_term t) (msg_of_term u)"

lemma wf_term_embed [simp]: "wf_term arity (embed msg)"
  by(induction msg) simp_all

lemma msg_of_term_embed [simp]: "msg_of_term (embed msg) = msg"
  by(induction msg) simp_all

lemma embed_msg_of_term [simp]: "wf_term arity t \<Longrightarrow> embed (msg_of_term t) = t"
  apply(induction t rule:msg_of_term.induct)
                      apply(simp_all)
  using arity.elims numerals(2) by auto


 