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

end