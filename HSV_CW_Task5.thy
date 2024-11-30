section \<open> Task 5: Verifying a naive SAT solver. \<close>

text \<open> This function can be used with List.fold to simulate a do-until loop. \<close>
definition until :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a option \<Rightarrow> 'a option" 
  where
  "until p x z == if z = None then if p x then Some x else None else z" 

text \<open> Once the loop condition holds, the return value is fixed. \<close>
lemma until_some: "fold (until p) xs (Some z) = Some z"
  by (induct xs, auto simp add: until_def)

text \<open> If the loop returns None, the condition holds for no element of the input list. \<close>
lemma until_none: "fold (until p) xs None = None \<Longrightarrow> list_all (\<lambda>x. \<not> p x) xs"
proof (induct xs)
  case Nil
  thus ?case by simp
next
  case (Cons a xs)
  hence *: "fold (until p) xs (until p a None) = None" by simp
  {
    assume "p a"
    hence "until p a None = Some a" by (simp add: until_def)
    hence "fold (until p) xs (Some a) = None" using * by presburger
    hence False using until_some by (metis option.distinct(1))
  } 
  moreover {
    assume "\<not> p a"
    hence "until p a None = None" by (simp add: until_def)
    hence "fold (until p) xs None = None" using * by presburger
    hence "list_all (\<lambda>x. \<not> p x) xs" by (rule Cons.hyps)
    hence ?case by (simp add: `\<not> p a`)
  } 
  ultimately show ?case by blast
qed

text \<open> If the loop returns Some x, the condition holds for element x of the input list. \<close>
lemma until_none_some: "fold (until p) xs None = Some x \<Longrightarrow> p x \<and> List.member xs x"
proof (induct xs)
  case Nil
  thus ?case by simp
next
  case (Cons a xs)
  hence *: "fold (until p) xs (until p a None) = Some x" by simp
  {
    assume "p a"
    hence "until p a None = Some a" by (simp add: until_def) 
    hence "a = x" by (metis * option.inject until_some)
    hence "p x \<and> List.member (a # xs) x" using `p a` in_set_member by force
  } 
  moreover {
    assume "\<not> p a"
    hence "until p a None = None" by (simp add: until_def)
    hence "fold (until p) xs None = Some x" using * by presburger
    hence "p x \<and> List.member (a # xs) x" using Cons.hyps by (simp add: member_rec(1))
  } 
  ultimately show ?case by blast
qed

text \<open> We shall use strings to represent symbols. \<close>
type_synonym symbol = "string"

text \<open> A literal is either a variable or a negated symbol. \<close>
type_synonym literal = "symbol * bool"

text \<open> A valuation is a list of symbols and their truth values. \<close>
type_synonym valuation = "(symbol * bool) list"

text \<open> A clause is a disjunction of literals. \<close>
type_synonym clause = "literal list"

text \<open> A SAT query is a conjunction of clauses. \<close>
type_synonym query = "clause list"

text \<open> Given a valuation, evaluate a clause to its truth value. \<close>
definition evaluate_clause :: "valuation \<Rightarrow> clause \<Rightarrow> bool"
where 
  "evaluate_clause \<rho> c = list_ex (List.member \<rho>) c"

text \<open> Given a valuation, evaluate a query to its truth value. \<close>
definition evaluate :: "query \<Rightarrow> valuation \<Rightarrow> bool"
where 
  "evaluate q \<rho> = list_all (evaluate_clause \<rho>) q"

text \<open> Some sample queries and valuations. \<close>
(* q1 is (a \<or> b) \<and> (\<not>b \<or> c) *)
definition "q1 == [[(''a'', True), (''b'', True)], [(''b'', False), (''c'', True)]]"
(* q2 is (a \<or> b) \<and> (\<not>a \<or> \<not>b) *)
definition "q2 == [[(''a'', True), (''b'', True)], [(''a'', False)], [(''b'', False)]]"
(* q3 is (a \<or> \<not>b) *)
definition "q3 == [[(''a'', True), (''b'', False)]]"
(* q4 is (\<not>b \<or> a) *)
definition "q4 == [[(''b'', False), (''a'', True)]]"
definition "\<rho>1 == [(''a'', True), (''b'', True), (''c'', False)]"
definition "\<rho>2 == [(''a'', False), (''b'', True), (''c'', True)]"

value "evaluate q1 \<rho>1" 
value "evaluate q1 \<rho>2"

text \<open> Construct the list of all possible valuations over the given symbols. \<close>
fun mk_valuation_list :: "symbol list \<Rightarrow> valuation list"
where 
  "mk_valuation_list [] = [[]]"
| "mk_valuation_list (x # xs) = (
     let \<rho>s = mk_valuation_list xs in 
     map ((#) (x, True)) \<rho>s @ map ((#) (x, False)) \<rho>s)"

value "mk_valuation_list [''a'',''b'']"
value "mk_valuation_list [''a'',''b'',''c'']"

fun symbol_of_literal :: "literal \<Rightarrow> symbol"
where
  "symbol_of_literal (x, _) = x"

text \<open> Extract the list of symbols from the given clause. \<close>
definition symbol_list_clause :: "clause \<Rightarrow> symbol list"
where 
  "symbol_list_clause c == remdups (map symbol_of_literal c)"

text \<open> Extract the list of symbols from the given query. \<close>
definition symbol_list :: "query \<Rightarrow> symbol list"
where
  "symbol_list q == remdups (concat (map symbol_list_clause q))"

value "symbol_list q1"
value "symbol_list q2"

text \<open> A naive SAT solver. It works by constructing the list of all
  possible valuations over the symbols that appear in the query, and
  then iterating through that list until it finds the first valuation
  that makes the query true. If none of the valuations make the query
  true, it returns None. \<close>
definition naive_solve :: "query \<Rightarrow> valuation option"
where
  "naive_solve q == 
  let xs = symbol_list q in 
  let \<rho>s = mk_valuation_list xs in
  List.fold (until (evaluate q)) \<rho>s None"

value "naive_solve q1"
value "naive_solve q2"
value "naive_solve q3"
value "naive_solve q4"

text \<open> If the naive SAT solver returns a valuation, then that 
  valuation really does make the query true. \<close>
theorem naive_solve_correct_sat:
  assumes "naive_solve q = Some \<rho>"
  shows "evaluate q \<rho>"
  oops

text \<open> If the naive SAT solver returns no valuation, then none of the valuations 
  it tried make the query true. \<close>
theorem naive_solve_correct_unsat:
  assumes "naive_solve q = None"
  shows "\<forall>\<rho> \<in> set (mk_valuation_list (symbol_list q)). \<not> evaluate q \<rho>" 
  oops
