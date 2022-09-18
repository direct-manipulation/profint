theory Profint
  imports Main
begin

(* These are the transport theorems *)

theorem go_left_and: "(a --> b) --> (a & c --> b & c)"
  by blast
theorem go_right_and: "(a --> b) --> (c & a --> c & b)"
  by blast
theorem go_left_or: "(a --> b) --> (a | c --> b | c)"
  by blast
theorem go_right_or: "(a --> b) --> (c | a --> c | b)"
  by blast
theorem go_left_imp: "(b --> a) --> ((a --> c) --> (b --> c))"
  by blast
theorem go_right_imp: "(a --> b) --> ((c --> a) --> (c --> b))"
  by blast
theorem go_down_all: "(ALL x. p x --> q x) --> (ALL x. p x) --> (ALL x. q x)"
  by blast
theorem go_down_ex: "(ALL x. p x --> q x) --> (EX x. p x) --> (EX x. q x)"
  by blast
theorem init: "True --> (a --> a)"
  by blast

(* These are the rule names *)

theorem goal_ts_and_l: "((a --> b) & c) --> (a --> (b & c))"
  by blast
theorem goal_ts_and_r: "(c & (a --> b)) --> (a --> (c & b))"
  by blast
theorem goal_and_ts_l: "(a --> b) --> (a & c --> b)"
  by blast
theorem goal_and_ts_r: "(a --> b) --> (c & a --> b)"
  by blast
theorem goal_ts_or_l: "(a --> b) --> (a --> b | c)"
  by blast
theorem goal_ts_or_r: "(a --> b) --> (a --> c | b)"
  by blast
theorem goal_or_ts: "((a --> c) & (b --> c)) --> (a | b --> c)"
  by blast
theorem goal_ts_imp_l: "(a & b --> c) --> (a --> b --> c)"
  by blast
theorem goal_ts_imp_r: "(c --> a --> b) --> (a --> c --> b)"
  by blast
theorem goal_imp_ts: "(c & (a --> b)) --> ((c --> a) --> b)"
  by blast
theorem goal_ts_all: "(ALL x. (a --> p x)) --> (a --> (ALL x. p x))"
  by blast
theorem goal_all_ts: "(EX x. (p x --> b)) --> (ALL x. p x) --> b"
  by blast
theorem goal_ts_ex: "(EX x. (a --> p x)) --> (a --> (EX x. p x))"
  by blast
theorem goal_ex_ts: "(ALL x. (p x --> a)) --> (EX x. p x) --> a"
  by blast

theorem asms_and_l_l: "(a & (b & c)) --> (a & b)"
  by blast
theorem asms_and_l_r: "(a & (c & b)) --> (a & b)"
  by blast
theorem asms_and_r_l: "((a & c) & b) --> (a & b)"
  by blast
theorem asms_and_r_r: "((c & a) & b) --> (a & b)"
  by blast
theorem asms_or_l_l: "(a & (b | c)) --> ((a & b) | c)"
  by blast
theorem asms_or_l_r: "(a & (c | b)) --> (c | (a & b))"
  by blast
theorem asms_or_r_l: "((a | c) & b) --> ((a & b) | c)"
  by blast
theorem asms_or_r_r: "((c | a) & b) --> (c | (a & b))"
  by blast
theorem asms_imp_l_l: "(a & (b --> c)) --> ((a --> b) --> c)"
  by blast
theorem asms_imp_l_r: "(a & (c --> b)) --> (c --> (a & b))"
  by blast
theorem asms_imp_r_l: "((a --> c) & b) --> ((b --> a) --> c)"
  by blast
theorem asms_imp_r_r: "((c --> a) & b) --> (c --> (a & b))"
  by blast
theorem asms_all_l: "(a & (ALL x. p x)) --> (ALL x. (a & p x))"
  by blast
theorem asms_all_r: "((ALL x. p x) & a) --> (ALL x. (p x & a))"
  by blast
theorem asms_ex_l: "(a & (EX x. p x)) --> (EX x. (a & p x))"
  by blast
theorem asms_ex_r: "((EX x. p x) & a) --> (EX x. (p x & a))"
  by blast

theorem contract: "(a --> a --> b) --> (a --> b)"
  by blast
theorem weaken: "b --> (a --> b)"
  by blast
theorem inst_r: "!! t. p t --> (EX x. p x)"
  by blast
theorem inst_l: "!! t. (ALL x. p x) --> p t"
  by blast
theorem rewrite_rtl: "!! s t. p s --> s = t --> p t"
  by blast
theorem rewrite_ltr: "!! s t. p t --> s = t --> p s"
  by blast

theorem simp_goal_and_top: "a --> (a & True)"
  by blast
theorem simp_goal_top_and: "a --> (True & a)"
  by blast
theorem simp_asms_and_top: "(a & True) --> a"
  by blast
theorem simp_asms_top_and: "(True & a) --> a"
  by blast

theorem simp_goal_or_top: "True --> (a | True)"
  by blast
theorem simp_goal_top_or: "True --> (True | a)"
  by blast
theorem simp_asms_or_top: "(a | True) --> True"
  by blast
theorem simp_asms_top_or: "(True | a) --> True"
  by blast

theorem simp_goal_imp_top: "True --> (a --> True)"
  by blast
theorem simp_goal_top_imp: "a --> (True --> a)"
  by blast
theorem simp_asms_imp_top: "(a --> True) --> True"
  by blast
theorem simp_asms_top_imp: "(True --> a) --> a"
  by blast

theorem simp_goal_and_bot: "False --> (a & False)"
  by blast
theorem simp_goal_bot_and: "False --> (False & a)"
  by blast
theorem simp_asms_and_bot: "(a & False) --> False"
  by blast
theorem simp_asms_bot_and: "(False & a) --> False"
  by blast

theorem simp_goal_or_bot: "a --> (a | False)"
  by blast
theorem simp_goal_bot_or: "a --> (False | a)"
  by blast
theorem simp_asms_or_bot: "(a | False) --> a"
  by blast
theorem simp_asms_bot_or: "(False | a) --> a"
  by blast

theorem simp_goal_bot_imp: "True --> (False --> a)"
  by blast
theorem simp_asms_bot_imp: "(False --> a) --> True"
  by blast

theorem simp_goal_all_top: "True --> (ALL _. True)"
  by blast
theorem simp_asms_all_top: "(ALL _. True) --> True"
  by blast
theorem simp_goal_ex_bot: "False --> (EX _. False)"
  by blast
theorem simp_asms_ex_bot: "(EX _. False) --> False"
  by blast

end