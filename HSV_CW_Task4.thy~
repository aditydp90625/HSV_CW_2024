theory HSV_CW_Task4 imports Main begin
theory HSV_CW_Task3 imports Main begin

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



text \<open>Task 3: Converting to and from digit lists. \<close>

text \<open> Turns a natural number into a list of digits in reverse order. \<close>

text \<open>A function that converts a list of digits back into a natural number. \<close>
fun sum10 :: "nat list \<Rightarrow> nat"
where
  "sum10 [] = 0"
| "sum10 (d # ds) = d + 10 * sum10 ds"

value "sum10 [2,4]"


text \<open> Applying digits10 then sum10 gets you back to the same number. \<close>
theorem digits10_sum10_inverse: "sum10 (digits10 n) = n"
proof (induct n rule: digits10.induct)
  case (1 n)
  then show ?case  by (cases n, auto)
qed



theorem counterexample: "digits10 (sum10 [1,0]) \<noteq> [1,0]"
  by simp




section \<open> Task 4: A divisibility theorem. \<close>


theorem ABABAB_divisibility: "(sum10 [B,A,B,A,B,A]) mod 37 = 0"
proof
  have "(sum10 [B,A,B,A,B,A])mod 37 = (101010 * A + 10101 * B) mod 37" by simp
  hence "(sum10 [B,A,B,A,B,A])mod 37 = (101010 * A) mod 37 + (10101 * B) mod 37" by auto
  hence "(sum10 [B,A,B,A,B,A])mod 37 = 0" by auto
  then show  "\<forall>A B. (sum10 [B,A,B,A,B,A])mod 37 = 0"
qed


end