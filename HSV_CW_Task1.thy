theory HSV_CW_Task1 imports Main begin

section \<open> Task 1: Extending our circuit synthesiser with NAND gates. \<close>

text \<open> Datatype for representing simple circuits, extended with NAND gates. \<close>
datatype "circuit" = 
  NOT "circuit"
| AND "circuit" "circuit"
| OR "circuit" "circuit"
| NAND "circuit" "circuit"
| TRUE
| FALSE
| INPUT "int"

text \<open> Simulates a circuit given a valuation for each input wire. \<close>
fun simulate where
  "simulate (AND c1 c2) \<rho> = ((simulate c1 \<rho>) \<and> (simulate c2 \<rho>))"
| "simulate (OR c1 c2) \<rho> = ((simulate c1 \<rho>) \<or>
 (simulate c2 \<rho>))"
| "simulate (NAND c1 c2) \<rho> = (\<not> ((simulate c1 \<rho>) \<and> (simulate c2 \<rho>)))"
| "simulate (NOT c) \<rho> = (\<not> (simulate c \<rho>))"
| "simulate TRUE \<rho> = True"
| "simulate FALSE \<rho> = False"
| "simulate (INPUT i) \<rho> = \<rho> i"


text \<open> Equivalence between circuits. \<close>
fun circuits_equiv (infix "\<sim>" 50) where
  "c1 \<sim> c2 = (\<forall>
\<rho>. simulate c1 \<rho> = simulate c2 \<rho>)"


text \<open> A transformation that replaces AND/OR/NOT gates with NAND gates. \<close>
text \<open>Changing the definition of FALSE from NAND TRUE FALSE to just FALSE\<close>
fun intro_nand where
  "intro_nand (AND c1 c2) = 
         NAND (NAND (intro_nand c1) (intro_nand c2)) TRUE"
| "intro_nand (OR c1 c2) = 
         NAND (NAND (intro_nand c1) TRUE) (NAND (intro_nand c2) TRUE)"
| "intro_nand (NAND c1 c2) = (
         NAND (intro_nand c1) (intro_nand c2))"
| "intro_nand (NOT c) = NAND (intro_nand c) TRUE"
| "intro_nand TRUE = TRUE"
| "intro_nand FALSE = FALSE"
| "intro_nand (INPUT i) = INPUT i"


text \<open> The intro_nand transformation is sound. Note that there is a 
  (deliberate) bug in the definition above, which you will need to fix 
  before you can prove the theorem below.\<close>
definition Pnand where "Pnand c \<equiv> \<forall>\<rho>. simulate(intro_nand c) \<rho> = simulate c \<rho>"
thm Pnand_def

theorem intro_nand_is_sound: "Pnand c"
  using Pnand_def
 by(induct c, auto)


text \<open> The only_nands predicate holds if a circuit contains only NAND gates. \<close>
fun only_nands where
  "only_nands (NAND c1 c2) = (only_nands c1 \<and> only_nands c2)"
| "only_nands (INPUT _) = True"
| "only_nands TRUE = True"
| "only_nands FALSE = True"
| "only_nands _ = False"

text \<open> The output of the intro_nand transformation is a circuit that only
  contains NAND gates. Note that there is a (deliberate) bug in the
  definition above, which you will need to fix before you can prove the
  theorem below. \<close>

theorem intro_nand_only_produces_nands: "only_nands (intro_nand c)"
  by(induct c, auto)
 

