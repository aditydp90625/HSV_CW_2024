theory HSV_CW_Task5 imports Main begin

section ‹ Task 5: Verifying a naive SAT solver. ›

text ‹ This function can be used with List.fold to simulate a do-until loop. ›
definition until :: "('a ⇒ bool) ⇒ 'a ⇒ 'a option ⇒ 'a option" 
  where
  "until p x z ≡ if z = None then if p x then Some x else None else z" 

text ‹ Once the loop condition holds, the return value is fixed. ›
lemma until_some: "fold (until p) xs (Some z) = Some z"
  by (induct xs, auto simp add: until_def)

text ‹ If the loop returns None, the condition holds for no element of the input list. ›
lemma until_none: "fold (until p) xs None = None ⟹ list_all (λx. ¬ p x) xs"
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
    assume "¬ p a"
    hence "until p a None = None" by (simp add: until_def)
    hence "fold (until p) xs None = None" using * by presburger
    hence "list_all (λx. ¬ p x) xs" by (rule Cons.hyps)
    hence ?case by (simp add: `¬ p a`)
  } 
  ultimately show ?case by blast
qed

text ‹ If the loop returns Some x, the condition holds for element x of the input list. ›
lemma until_none_some: "fold (until p) xs None = Some x ⟹ p x ∧ List.member xs x"
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
    hence "p x ∧ List.member (a # xs) x" using `p a` in_set_member by force
  } 
  moreover {
    assume "¬ p a"
    hence "until p a None = None" by (simp add: until_def)
    hence "fold (until p) xs None = Some x" using * by presburger
    hence "p x ∧ List.member (a # xs) x" using Cons.hyps by (simp add: member_rec(1))
  } 
  ultimately show ?case by blast
qed

text ‹ We shall use strings to represent symbols. ›
type_synonym symbol = "string"

text ‹ A literal is either a variable or a negated symbol. ›
type_synonym literal = "symbol × bool"

text ‹ A valuation is a list of symbols and their truth values. ›
type_synonym valuation = "(symbol × bool) list"

text ‹ A clause is a disjunction of literals. ›
type_synonym clause = "literal list"

text ‹ A SAT query is a conjunction of clauses. ›
type_synonym query = "clause list"

text ‹ Given a valuation, evaluate a clause to its truth value. ›
definition evaluate_clause :: "valuation ⇒ clause ⇒ bool"
where 
  "evaluate_clause ρ c = list_ex (List.member ρ) c"

text ‹ Given a valuation, evaluate a query to its truth value. ›
definition evaluate :: "query ⇒ valuation ⇒ bool"
where 
  "evaluate q ρ = list_all (evaluate_clause ρ) q"

text ‹ Some sample queries and valuations. ›
(* q1 is (a ∨ b) ∧ (¬b ∨ c) *)
definition "q1 ≡ [[(''a'', True), (''b'', True)], [(''b'', False), (''c'', True)]]"
(* q2 is (a ∨ b) ∧ (¬a ∨ ¬b) *)
definition "q2 ≡ [[(''a'', True), (''b'', True)], [(''a'', False)], [(''b'', False)]]"
(* q3 is (a ∨ ¬b) *)
definition "q3 ≡ [[(''a'', True), (''b'', False)]]"
(* q4 is (¬b ∨ a) *)
definition "q4 ≡ [[(''b'', False), (''a'', True)]]"
definition "ρ1 ≡ [(''a'', True), (''b'', True), (''c'', False)]"
definition "ρ2 ≡ [(''a'', False), (''b'', True), (''c'', True)]"

value "evaluate q1 ρ1" 
value "evaluate q1 ρ2"

text ‹ Construct the list of all possible valuations over the given symbols. ›
fun mk_valuation_list :: "symbol list ⇒ valuation list"
where 
  "mk_valuation_list [] = [[]]"
| "mk_valuation_list (x # xs) = (
     let ρs = mk_valuation_list xs in 
     map ((#) (x, True)) ρs @ map ((#) (x, False)) ρs)"

value "mk_valuation_list [''a'',''b'']"
value "mk_valuation_list [''a'',''b'',''c'']"

fun symbol_of_literal :: "literal ⇒ symbol"
where
  "symbol_of_literal (x, _) = x"

text ‹ Extract the list of symbols from the given clause. ›
definition symbol_list_clause :: "clause ⇒ symbol list"
where 
  "symbol_list_clause c ≡ remdups (map symbol_of_literal c)"

text ‹ Extract the list of symbols from the given query. ›
definition symbol_list :: "query ⇒ symbol list"
where
  "symbol_list q ≡ remdups (concat (map symbol_list_clause q))"

value "symbol_list q1"
value "symbol_list q2"

text ‹ A naive SAT solver. It works by constructing the list of all
  possible valuations over the symbols that appear in the query, and
  then iterating through that list until it finds the first valuation
  that makes the query true. If none of the valuations make the query
  true, it returns None. ›
definition naive_solve :: "query ⇒ valuation option"
where
  "naive_solve q ≡ 
  let xs = symbol_list q in 
  let ρs = mk_valuation_list xs in
  List.fold (until (evaluate q)) ρs None"

value "naive_solve q1"
value "naive_solve q2"
value "naive_solve q3"
value "naive_solve q4"

text ‹ If the naive SAT solver returns a valuation, then that 
  valuation really does make the query true. ›
theorem naive_solve_correct_sat:
  assumes "naive_solve q = Some ρ"
  shows "evaluate q ρ" using until_none_some
    by (metis assms naive_solve_def)

text ‹ If the naive SAT solver returns no valuation, then none of the valuations 
  it tried make the query true. ›
theorem naive_solve_correct_unsat:
  assumes "naive_solve q = None"
  shows "∀ρ ∈ set (mk_valuation_list (symbol_list q)). ¬ evaluate q ρ"
proof -
  from assms have "List.fold (until (evaluate q)) (mk_valuation_list (symbol_list q)) None = None"
    by (simp add: naive_solve_def)
  
  (* Apply until_none lemma *)
  then have "∀ρ ∈ set (mk_valuation_list (symbol_list q)). ¬ evaluate q ρ" using until_none naive_solve_def 
    using split_list_first by fastforce
  
  thus ?thesis by simp
qed



end
