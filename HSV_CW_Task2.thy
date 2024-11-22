theory HSV_CW_Task2 imports Main begin

section \<open> Task 2: Converting numbers to lists of digits. \<close>

text \<open> Turns a natural number into a list of digits in reverse order. \<close>
fun digits10 :: "nat \<Rightarrow> nat list"
where
  "digits10 n = (if n < 10 then [n] else (n mod 10) # digits10 (n div 10))"

value "digits10 13"

text \<open> Every digit is less than 10 (helper lemma). \<close>
lemma digits10_all_below_10: 
  "\<forall>d \<in> set (digits10 n). d < 10"
proof (induction n rule: digits10.induct)
  case (1 n)
  show ?case
  proof (cases "n < 10")
    case True
    (* Base case: n < 10 *)
    then have "digits10 n = [n]" by simp
    hence "set (digits10 n) = {n}" by simp
    moreover from True have "n < 10" by simp
    ultimately show ?thesis by simp
  next
    case False
    (* Recursive case: n \<ge> 10 *)
    then have "digits10 n = (n mod 10) # digits10 (n div 10)" by simp
    hence "set (digits10 n) = {n mod 10} \<union> set (digits10 (n div 10))" by simp
    moreover have "n mod 10 < 10" by simp
    moreover have "\<forall>d \<in> set (digits10 (n div 10)). d < 10" using 1 by fastforce
    ultimately show ?thesis
      by (metis \<open>digits10 n = n mod 10 # digits10 (n div 10)\<close> set_ConsD) 
  qed
qed

text \<open> Every digit is less than 10. \<close>
corollary 
  "\<forall>d \<in> set (digits10 n). d < 10" using digits10_all_below_10 try
  by blast
end