theory Test
  imports Profint
begin

lemma ex1: 
  assumes prem: "True"
  shows "a \<longrightarrow> b \<longrightarrow> b \<and> a"
proof -
  have l0: "True" by (rule prem)
  have l1: "b \<longrightarrow> b"
    by (rule impE[OF init l0])
  have l2: "b \<longrightarrow> b \<and> True"
    by (rule impE[OF impE[OF go_right_imp simp_goal_and_top] l1])
  have l3: "b \<longrightarrow> b \<and> (a \<longrightarrow> a)"
    by (rule impE[OF impE[OF go_right_imp impE[OF go_right_and init]] l2])
  have l4: "b \<longrightarrow> a \<longrightarrow> b \<and> a"
    by (rule impE[OF impE[OF go_right_imp goal_ts_and_r] l3])
  have l5: "a \<longrightarrow> b \<longrightarrow> b \<and> a"
    by (rule impE[OF goal_ts_imp_r l4])
  thus ?thesis.
qed

lemma ex_s:
  assumes prem: "True"
  shows "(a \<longrightarrow> b \<longrightarrow> c) \<longrightarrow> (a \<longrightarrow> b) \<longrightarrow> a \<longrightarrow> c"
proof -
  have l0: "True"
    by (rule prem)
  have l1: "c \<longrightarrow> c"
    by (rule impE[OF init l0])
  have l2: "(True \<longrightarrow> c) \<longrightarrow> c"
    by (rule impE[OF impE[OF go_left_imp simp_asms_top_imp] l1])
  have l3: "((b \<longrightarrow> b) \<longrightarrow> c) \<longrightarrow> c"
    by (rule impE[OF impE[OF go_left_imp impE[OF go_left_imp init]] l2])
  have l4: "b \<and> (b \<longrightarrow> c) \<longrightarrow> c"
    by (rule impE[OF impE[OF go_left_imp asms_imp_l_l] l3])
  have l5: "b \<longrightarrow> (b \<longrightarrow> c) \<longrightarrow> c"
    by (rule impE[OF goal_ts_imp_l l4])
  have l6: "b \<longrightarrow> (True \<longrightarrow> b \<longrightarrow> c) \<longrightarrow> c"
    by (rule impE[OF impE[OF go_right_imp impE[OF go_left_imp simp_asms_top_imp]] l5])
  have l7: "b \<longrightarrow> ((a \<longrightarrow> a) \<longrightarrow> b \<longrightarrow> c) \<longrightarrow> c"
    by (rule impE[OF impE[OF go_right_imp impE[OF go_left_imp impE[OF go_left_imp init]]] l6])
  have l8: "b \<longrightarrow> (a \<longrightarrow> b \<longrightarrow> c) \<and> a \<longrightarrow> c"
    by (rule impE[OF impE[OF go_right_imp impE[OF go_left_imp asms_imp_r_l]] l7])
  have l9: "b \<longrightarrow> (a \<longrightarrow> b \<longrightarrow> c) \<longrightarrow> a \<longrightarrow> c"
    by (rule impE[OF impE[OF go_right_imp goal_ts_imp_l] l8])
  have l10: "(a \<longrightarrow> b \<longrightarrow> c) \<longrightarrow> b \<longrightarrow> a \<longrightarrow> c"
    by (rule impE[OF goal_ts_imp_r l9])
  have l11: "(a \<longrightarrow> b \<longrightarrow> c) \<longrightarrow> (True \<longrightarrow> b) \<longrightarrow> a \<longrightarrow> c"
    by (rule impE[OF impE[OF go_right_imp impE[OF go_left_imp simp_asms_top_imp]] l10])
  have l12: "(a \<longrightarrow> b \<longrightarrow> c) \<longrightarrow> ((a \<longrightarrow> a) \<longrightarrow> b) \<longrightarrow> a \<longrightarrow> c"
    by (rule impE[OF impE[OF go_right_imp impE[OF go_left_imp impE[OF go_left_imp init]]] l11])
  have l13: "(a \<longrightarrow> b \<longrightarrow> c) \<longrightarrow> (a \<longrightarrow> b) \<and> a \<longrightarrow> a \<longrightarrow> c"
    by (rule impE[OF impE[OF go_right_imp impE[OF go_left_imp asms_imp_r_l]] l12])
  have l14: "(a \<longrightarrow> b \<longrightarrow> c) \<longrightarrow> (a \<longrightarrow> b) \<longrightarrow> a \<longrightarrow> a \<longrightarrow> c"
    by (rule impE[OF impE[OF go_right_imp goal_ts_imp_l] l13])
  have l15: "(a \<longrightarrow> b \<longrightarrow> c) \<longrightarrow> (a \<longrightarrow> b) \<longrightarrow> a \<longrightarrow> c"
    by (rule impE[OF impE[OF go_right_imp impE[OF go_right_imp contract]] l14])
  thus ?thesis.
qed

lemma ex_ss:
  assumes prem: "True"
  shows "(a \<Longrightarrow> b \<Longrightarrow> c) \<Longrightarrow> (a \<Longrightarrow> b) \<Longrightarrow> a \<Longrightarrow> c"
proof (atomize (full))
  have l0: "True"
    by (rule prem)
  have l1: "c \<longrightarrow> c"
    by (rule impE[OF init l0])
  have l2: "(True \<longrightarrow> c) \<longrightarrow> c"
    by (rule impE[OF impE[OF go_left_imp simp_asms_top_imp] l1])
  have l3: "((b \<longrightarrow> b) \<longrightarrow> c) \<longrightarrow> c"
    by (rule impE[OF impE[OF go_left_imp impE[OF go_left_imp init]] l2])
  have l4: "b \<and> (b \<longrightarrow> c) \<longrightarrow> c"
    by (rule impE[OF impE[OF go_left_imp asms_imp_l_l] l3])
  have l5: "b \<longrightarrow> (b \<longrightarrow> c) \<longrightarrow> c"
    by (rule impE[OF goal_ts_imp_l l4])
  have l6: "b \<longrightarrow> (True \<longrightarrow> b \<longrightarrow> c) \<longrightarrow> c"
    by (rule impE[OF impE[OF go_right_imp impE[OF go_left_imp simp_asms_top_imp]] l5])
  have l7: "b \<longrightarrow> ((a \<longrightarrow> a) \<longrightarrow> b \<longrightarrow> c) \<longrightarrow> c"
    by (rule impE[OF impE[OF go_right_imp impE[OF go_left_imp impE[OF go_left_imp init]]] l6])
  have l8: "b \<longrightarrow> (a \<longrightarrow> b \<longrightarrow> c) \<and> a \<longrightarrow> c"
    by (rule impE[OF impE[OF go_right_imp impE[OF go_left_imp asms_imp_r_l]] l7])
  have l9: "b \<longrightarrow> (a \<longrightarrow> b \<longrightarrow> c) \<longrightarrow> a \<longrightarrow> c"
    by (rule impE[OF impE[OF go_right_imp goal_ts_imp_l] l8])
  have l10: "(a \<longrightarrow> b \<longrightarrow> c) \<longrightarrow> b \<longrightarrow> a \<longrightarrow> c"
    by (rule impE[OF goal_ts_imp_r l9])
  have l11: "(a \<longrightarrow> b \<longrightarrow> c) \<longrightarrow> (True \<longrightarrow> b) \<longrightarrow> a \<longrightarrow> c"
    by (rule impE[OF impE[OF go_right_imp impE[OF go_left_imp simp_asms_top_imp]] l10])
  have l12: "(a \<longrightarrow> b \<longrightarrow> c) \<longrightarrow> ((a \<longrightarrow> a) \<longrightarrow> b) \<longrightarrow> a \<longrightarrow> c"
    by (rule impE[OF impE[OF go_right_imp impE[OF go_left_imp impE[OF go_left_imp init]]] l11])
  have l13: "(a \<longrightarrow> b \<longrightarrow> c) \<longrightarrow> (a \<longrightarrow> b) \<and> a \<longrightarrow> a \<longrightarrow> c"
    by (rule impE[OF impE[OF go_right_imp impE[OF go_left_imp asms_imp_r_l]] l12])
  have l14: "(a \<longrightarrow> b \<longrightarrow> c) \<longrightarrow> (a \<longrightarrow> b) \<longrightarrow> a \<longrightarrow> a \<longrightarrow> c"
    by (rule impE[OF impE[OF go_right_imp goal_ts_imp_l] l13])
  have l15: "(a \<longrightarrow> b \<longrightarrow> c) \<longrightarrow> (a \<longrightarrow> b) \<longrightarrow> a \<longrightarrow> c"
    by (rule impE[OF impE[OF go_right_imp impE[OF go_right_imp contract]] l14])
  show "(a \<longrightarrow> b \<longrightarrow> c) \<longrightarrow> (a \<longrightarrow> b) \<longrightarrow> a \<longrightarrow> c" by (rule l15)
qed

lemma oof2:
  fixes a :: "bool"
  fixes b :: "bool"
  fixes c :: "bool"
  fixes f :: "'i \<Rightarrow> 'i"
  fixes g :: "'i \<Rightarrow> 'i \<Rightarrow> 'i"
  fixes j :: "'i"
  fixes k :: "'i"
  fixes p :: "'i \<Rightarrow> bool"
  fixes q :: "'i \<Rightarrow> bool"
  fixes r :: "'i \<Rightarrow> 'i \<Rightarrow> bool"
  assumes prem: "True"
  shows "(\<exists> x :: 'i. p x \<and> (p x \<longrightarrow> False)) \<longrightarrow> False"
proof -
  have l0: "True" by (rule prem)
  have l1: "False \<longrightarrow> False"
    by (rule impE[OF simp_goal_bot_imp l0])
  have l2: "(\<exists> x :: 'i. False) \<longrightarrow> False"
    by (rule impE[OF impE[OF go_left_imp simp_asms_ex_bot] l1])
  have l3: "(\<exists> x :: 'i. True \<longrightarrow> False) \<longrightarrow> False"
    by (rule impE[OF impE[OF go_left_imp impE[OF go_down_ex allI[of "\<lambda>x. (True \<longrightarrow> False) \<longrightarrow> False", OF simp_asms_top_imp]]] l2])
  have l4: "(\<exists> x :: 'i. (p x \<longrightarrow> p x) \<longrightarrow> False) \<longrightarrow> False"
  proof -
    have i1: "\<forall> x :: 'i. ((p x \<longrightarrow> p x) \<longrightarrow> False) \<longrightarrow> (True \<longrightarrow> False)"
    proof (rule allI)
      fix x
      show "((p x \<longrightarrow> p x) \<longrightarrow> False) \<longrightarrow> (True \<longrightarrow> False)"
        by (rule impE[OF go_left_imp init])
    qed
    show ?thesis
      by (rule impE[OF impE[OF go_left_imp impE[OF go_down_ex i1]] l3])
  qed
  have l5: "(\<exists> x :: 'i. p x \<and> (p x \<longrightarrow> False)) \<longrightarrow> False"
    by (rule impE[OF impE[OF go_left_imp impE[OF go_down_ex allI[OF asms_imp_l_l]]] l4])
  show "(\<exists> x :: 'i. p x \<and> (p x \<longrightarrow> False)) \<longrightarrow> False" by (rule l5)
qed

print_statement oof2


end