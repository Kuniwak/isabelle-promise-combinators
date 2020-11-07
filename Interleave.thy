theory Interleave imports "HOL-Library.Multiset" begin


inductive
  interleave :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  interleave_Nil_NilI[intro]:   "interleave [] [] []" |
  interleave_Cons_FreeI[intro]: "\<lbrakk> interleave xs ys zs \<rbrakk> \<Longrightarrow> interleave (x#xs) ys (x#zs)" |
  interleave_Free_ConsI[intro]: "\<lbrakk> interleave xs ys zs \<rbrakk> \<Longrightarrow> interleave xs (y#ys) (y#zs)"


inductive_cases interleave_Free_Free_NilE: "interleave xs ys []"
inductive_cases interleave_Free_Free_ConsE: "interleave xs ys (z#zs)"
inductive_cases interleave_Nil_Nil_FreeE: "interleave [] [] zs"
inductive_cases interleave_Nil_Free_FreeE: "interleave [] ys zs"
inductive_cases interleave_Free_Nil_FreeE: "interleave xs [] zs"
inductive_cases interleave_Cons_Free_FreeE: "interleave (x#xs) ys zs"
inductive_cases interleave_Free_Cons_FreeE: "interleave xs (y#ys) zs"
inductive_cases interleave_Free_Cons_ConsE: "interleave xs (y#ys) (z#zs)"
inductive_cases interleave_Cons_Cons_FreeE: "interleave (x#xs) (y#ys) zs"
inductive_cases interleave_Cons_Cons_ConsE: "interleave (x#xs) (y#ys) (z#zs)"




theorem interleave_left_neutral: "interleave [] ys ys"
  apply(induct_tac ys)
  apply(auto)
  done


theorem interleave_flip[rule_format]: "\<forall>xs ys. interleave xs ys zs \<longleftrightarrow> interleave ys xs zs"
  apply(induct_tac zs)
  apply(auto elim!: interleave_Free_Free_NilE interleave_Free_Free_ConsE)
  done


theorem interleave_right_neutral: "interleave xs [] xs"
  apply(subst interleave_flip)
  apply(rule interleave_left_neutral)
  done


theorem interleave_count: "\<forall>xs ys. interleave xs ys zs \<longrightarrow> mset xs + mset ys = mset zs"
  apply(induct_tac zs)
  apply(auto elim: interleave_Free_Free_NilE interleave_Free_Free_ConsE)
  done


theorem interleave_ex_concat: "\<forall>ys. interleave xs ys (xs@ys)"
  apply(induct_tac xs)
  apply(auto intro: interleave_left_neutral)
  done


lemma list_double_induct[rule_format]: "P [] [] \<longrightarrow> (\<forall>x xs ys. P xs ys \<longrightarrow> P (x#xs) ys) \<longrightarrow> (\<forall>y xs ys. P xs ys \<longrightarrow> P xs (y#ys)) \<longrightarrow> P xs ys"
  apply(induct_tac xs)
  apply(induct_tac ys)
  apply(auto)
  done


lemma "\<forall>xs ys. interleave xs ys zs \<longrightarrow> interleave (map f ys) (map f xs) (map f zs)"
  apply(induct_tac zs)
  apply(force elim: interleave_Free_Free_NilE)
  apply(clarsimp)
  apply(erule interleave_Free_Free_ConsE)
  apply(auto)
  done


lemma "\<lbrakk>
  (z1 = x1 \<and> z2 = x2 \<and> z3 = y1 \<and> z4 = y2) \<or>
  (z1 = x1 \<and> z2 = y1 \<and> z3 = x2 \<and> z4 = y2) \<or>
  (z1 = x1 \<and> z2 = y1 \<and> z3 = y2 \<and> z4 = x2) \<or>
  (z1 = y1 \<and> z2 = x1 \<and> z3 = y2 \<and> z4 = x2) \<or>
  (z1 = y1 \<and> z2 = x1 \<and> z3 = x2 \<and> z4 = y2) \<or>
  (z1 = y1 \<and> z2 = y2 \<and> z3 = x1 \<and> z4 = x2) \<rbrakk> \<Longrightarrow> interleave [x1, x2] [y1, y2] [z1, z2, z3, z4]"
  apply(auto)
  apply(rule)+
  done


lemma "interleave [x1, x2] [y1, y2] [z1, z2, z3, z4] \<Longrightarrow>
  (z1 = x1 \<and> z2 = x2 \<and> z3 = y1 \<and> z4 = y2) \<or>
  (z1 = x1 \<and> z2 = y1 \<and> z3 = x2 \<and> z4 = y2) \<or>
  (z1 = x1 \<and> z2 = y1 \<and> z3 = y2 \<and> z4 = x2) \<or>
  (z1 = y1 \<and> z2 = x1 \<and> z3 = y2 \<and> z4 = x2) \<or>
  (z1 = y1 \<and> z2 = x1 \<and> z3 = x2 \<and> z4 = y2) \<or>
  (z1 = y1 \<and> z2 = y2 \<and> z3 = x1 \<and> z4 = x2)"
  apply(erule interleave_Cons_Cons_ConsE)
  apply(erule interleave_Cons_Cons_ConsE)
  apply(erule interleave_Nil_Free_FreeE)
  apply(force)
  apply(erule interleave_Nil_Free_FreeE)
  apply(force)
  apply(force)
  apply(erule interleave_Cons_Cons_ConsE)
  apply(erule interleave_Nil_Free_FreeE)
  apply(force)
  apply(simp)
  apply(erule interleave_Free_Nil_FreeE)
  apply(force)
  apply(simp)
  apply(erule interleave_Cons_Cons_ConsE)
  apply(simp)
  apply(erule interleave_Cons_Cons_ConsE)
  apply(simp)
  apply(erule interleave_Nil_Free_FreeE)
  apply(force)
  apply(simp)
  apply(erule interleave_Free_Nil_FreeE)
  apply(force)
  apply(simp)
  apply(erule interleave_Free_Nil_FreeE)
  apply(force)
  apply(simp)
  apply(elim conjE)
  apply(erule interleave_Free_Nil_FreeE)
  apply(force)
  apply(simp)
  done


lemma [rule_format]: "interleave [x1, x2] [y1] [x1, x2, y1]"
  apply(rule)+
  done


lemma "\<lbrakk> x2 \<noteq> y1; x1 \<noteq> y1 \<rbrakk> \<Longrightarrow> \<not>interleave [y1, x2] [x1] [x1, x2, y1]"
  apply(auto)
  by (metis distinct_length_2_or_more distinct_singleton interleave_Free_Free_ConsE list.inject)

end