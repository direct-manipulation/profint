theory Profint
  imports Main
begin

(* These are the transport theorems *)

theorem go_left_and: "(a \<longrightarrow> b) \<longrightarrow> (a \<and> c \<longrightarrow> b \<and> c)"
  by blast
theorem go_right_and: "(a \<longrightarrow> b) \<longrightarrow> (c \<and> a \<longrightarrow> c \<and> b)"
  by blast
theorem go_left_or: "(a \<longrightarrow> b) \<longrightarrow> (a \<or> c \<longrightarrow> b \<or> c)"
  by blast
theorem go_right_or: "(a \<longrightarrow> b) \<longrightarrow> (c \<or> a \<longrightarrow> c \<or> b)"
  by blast
theorem go_left_imp: "(b \<longrightarrow> a) \<longrightarrow> ((a \<longrightarrow> c) \<longrightarrow> (b \<longrightarrow> c))"
  by blast
theorem go_right_imp: "(a \<longrightarrow> b) \<longrightarrow> ((c \<longrightarrow> a) \<longrightarrow> (c \<longrightarrow> b))"
  by blast
theorem go_down_all: "(\<forall> x. p x \<longrightarrow> q x) \<longrightarrow> (\<forall> x. p x) \<longrightarrow> (\<forall> x. q x)"
  by blast
theorem go_down_ex: "(\<forall> x. p x \<longrightarrow> q x) \<longrightarrow> (\<exists> x. p x) \<longrightarrow> (\<exists> x. q x)"
  by blast
theorem init: "True \<longrightarrow> (a \<longrightarrow> a)"
  by blast

(* These are the rule names *)

theorem goal_ts_and_l: "((a \<longrightarrow> b) \<and> c) \<longrightarrow> (a \<longrightarrow> (b \<and> c))"
  by blast
theorem goal_ts_and_r: "(c \<and> (a \<longrightarrow> b)) \<longrightarrow> (a \<longrightarrow> (c \<and> b))"
  by blast
theorem goal_and_ts_l: "(a \<longrightarrow> b) \<longrightarrow> (a \<and> c \<longrightarrow> b)"
  by blast
theorem goal_and_ts_r: "(a \<longrightarrow> b) \<longrightarrow> (c \<and> a \<longrightarrow> b)"
  by blast
theorem goal_ts_or_l: "(a \<longrightarrow> b) \<longrightarrow> (a \<longrightarrow> b \<or> c)"
  by blast
theorem goal_ts_or_r: "(a \<longrightarrow> b) \<longrightarrow> (a \<longrightarrow> c \<or> b)"
  by blast
theorem goal_or_ts: "((a \<longrightarrow> c) \<and> (b \<longrightarrow> c)) \<longrightarrow> (a \<or> b \<longrightarrow> c)"
  by blast
theorem goal_ts_imp_l: "(a \<and> b \<longrightarrow> c) \<longrightarrow> (a \<longrightarrow> b \<longrightarrow> c)"
  by blast
theorem goal_ts_imp_r: "(c \<longrightarrow> a \<longrightarrow> b) \<longrightarrow> (a \<longrightarrow> c \<longrightarrow> b)"
  by blast
theorem goal_imp_ts: "(c \<and> (a \<longrightarrow> b)) \<longrightarrow> ((c \<longrightarrow> a) \<longrightarrow> b)"
  by blast
theorem goal_ts_all: "(\<forall> x. (a \<longrightarrow> p x)) \<longrightarrow> (a \<longrightarrow> (\<forall> x. p x))"
  by blast
theorem goal_all_ts: "(\<exists> x. (p x \<longrightarrow> b)) \<longrightarrow> (\<forall> x. p x) \<longrightarrow> b"
  by blast
theorem goal_ts_ex: "(\<exists> x. (a \<longrightarrow> p x)) \<longrightarrow> (a \<longrightarrow> (\<exists> x. p x))"
  by blast
theorem goal_ex_ts: "(\<forall> x. (p x \<longrightarrow> a)) \<longrightarrow> (\<exists> x. p x) \<longrightarrow> a"
  by blast

theorem asms_and_l_l: "(a \<and> (b \<and> c)) \<longrightarrow> (a \<and> b)"
  by blast
theorem asms_and_l_r: "(a \<and> (c \<and> b)) \<longrightarrow> (a \<and> b)"
  by blast
theorem asms_and_r_l: "((a \<and> c) \<and> b) \<longrightarrow> (a \<and> b)"
  by blast
theorem asms_and_r_r: "((c \<and> a) \<and> b) \<longrightarrow> (a \<and> b)"
  by blast
theorem asms_or_l_l: "(a \<and> (b \<or> c)) \<longrightarrow> ((a \<and> b) \<or> c)"
  by blast
theorem asms_or_l_r: "(a \<and> (c \<or> b)) \<longrightarrow> (c \<or> (a \<and> b))"
  by blast
theorem asms_or_r_l: "((a \<or> c) \<and> b) \<longrightarrow> ((a \<and> b) \<or> c)"
  by blast
theorem asms_or_r_r: "((c \<or> a) \<and> b) \<longrightarrow> (c \<or> (a \<and> b))"
  by blast
theorem asms_imp_l_l: "(a \<and> (b \<longrightarrow> c)) \<longrightarrow> ((a \<longrightarrow> b) \<longrightarrow> c)"
  by blast
theorem asms_imp_l_r: "(a \<and> (c \<longrightarrow> b)) \<longrightarrow> (c \<longrightarrow> (a \<and> b))"
  by blast
theorem asms_imp_r_l: "((a \<longrightarrow> c) \<and> b) \<longrightarrow> ((b \<longrightarrow> a) \<longrightarrow> c)"
  by blast
theorem asms_imp_r_r: "((c \<longrightarrow> a) \<and> b) \<longrightarrow> (c \<longrightarrow> (a \<and> b))"
  by blast
theorem asms_all_l: "(a \<and> (\<forall> x. p x)) \<longrightarrow> (\<forall> x. (a \<and> p x))"
  by blast
theorem asms_all_r: "((\<forall> x. p x) \<and> a) \<longrightarrow> (\<forall> x. (p x \<and> a))"
  by blast
theorem asms_ex_l: "(a \<and> (\<exists> x. p x)) \<longrightarrow> (\<exists> x. (a \<and> p x))"
  by blast
theorem asms_ex_r: "((\<exists> x. p x) \<and> a) \<longrightarrow> (\<exists> x. (p x \<and> a))"
  by blast

theorem contract: "(a \<longrightarrow> a \<longrightarrow> b) \<longrightarrow> (a \<longrightarrow> b)"
  by blast
theorem weaken: "b \<longrightarrow> (a \<longrightarrow> b)"
  by blast
theorem inst_r: "\<And> t. p t \<longrightarrow> (\<exists> x. p x)"
  by blast
theorem inst_l: "\<And> t. (\<forall> x. p x) \<longrightarrow> p t"
  by blast
theorem rewrite_rtl: "\<And> s t. p s \<longrightarrow> s = t \<longrightarrow> p t"
  by blast
theorem rewrite_ltr: "\<And> s t. p t \<longrightarrow> s = t \<longrightarrow> p s"
  by blast
theorem repeat: "a \<longrightarrow> a"
  by blast

theorem simp_goal_and_top: "a \<longrightarrow> (a \<and> True)"
  by blast
theorem simp_goal_top_and: "a \<longrightarrow> (True \<and> a)"
  by blast
theorem simp_asms_and_top: "(a \<and> True) \<longrightarrow> a"
  by blast
theorem simp_asms_top_and: "(True \<and> a) \<longrightarrow> a"
  by blast

theorem simp_goal_or_top: "True \<longrightarrow> (a \<or> True)"
  by blast
theorem simp_goal_top_or: "True \<longrightarrow> (True \<or> a)"
  by blast
theorem simp_asms_or_top: "(a \<or> True) \<longrightarrow> True"
  by blast
theorem simp_asms_top_or: "(True \<or> a) \<longrightarrow> True"
  by blast

theorem simp_goal_imp_top: "True \<longrightarrow> (a \<longrightarrow> True)"
  by blast
theorem simp_goal_top_imp: "a \<longrightarrow> (True \<longrightarrow> a)"
  by blast
theorem simp_asms_imp_top: "(a \<longrightarrow> True) \<longrightarrow> True"
  by blast
theorem simp_asms_top_imp: "(True \<longrightarrow> a) \<longrightarrow> a"
  by blast

theorem simp_goal_and_bot: "False \<longrightarrow> (a \<and> False)"
  by blast
theorem simp_goal_bot_and: "False \<longrightarrow> (False \<and> a)"
  by blast
theorem simp_asms_and_bot: "(a \<and> False) \<longrightarrow> False"
  by blast
theorem simp_asms_bot_and: "(False \<and> a) \<longrightarrow> False"
  by blast

theorem simp_goal_or_bot: "a \<longrightarrow> (a \<or> False)"
  by blast
theorem simp_goal_bot_or: "a \<longrightarrow> (False \<or> a)"
  by blast
theorem simp_asms_or_bot: "(a \<or> False) \<longrightarrow> a"
  by blast
theorem simp_asms_bot_or: "(False \<or> a) \<longrightarrow> a"
  by blast

theorem simp_goal_bot_imp: "True \<longrightarrow> (False \<longrightarrow> a)"
  by blast
theorem simp_asms_bot_imp: "(False \<longrightarrow> a) \<longrightarrow> True"
  by blast

theorem simp_goal_all_top: "True \<longrightarrow> (\<forall> _. True)"
  by blast
theorem simp_asms_all_top: "(\<forall> _. True) \<longrightarrow> True"
  by blast
theorem simp_goal_ex_bot: "False \<longrightarrow> (\<exists> _. False)"
  by blast
theorem simp_asms_ex_bot: "(\<exists> _. False) \<longrightarrow> False"
  by blast

end