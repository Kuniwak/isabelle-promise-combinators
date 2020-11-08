theory Interleave imports "HOL-Library.Multiset" SelfInv begin


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


lemma interleave_Free_Free_Nil: "interleave xs ys [] \<longleftrightarrow> xs = [] \<and> ys = []"
  apply(auto elim: interleave_Free_Free_NilE)
  done


theorem interleave_left_neutralI[rule_format]: "\<forall>zs. ys = zs \<longrightarrow> interleave [] ys zs"
  apply(induct_tac ys)
  apply(auto)
  done


theorem interleave_left_neutralD[rule_format]: "\<forall>ys. interleave [] ys zs \<longrightarrow> ys = zs"
  apply(induct zs)
  apply(auto elim: interleave_Free_Free_NilE)
  apply(erule interleave.cases)
  apply(auto)
  done


theorem interleave_left_neutral: "interleave [] ys zs \<longleftrightarrow> ys = zs"
  apply(rule iffI)
  apply(erule interleave_left_neutralD)
  apply(erule interleave_left_neutralI)
  done


theorem interleave_flip[rule_format]: "\<forall>xs ys. interleave xs ys zs \<longleftrightarrow> interleave ys xs zs"
  apply(induct_tac zs)
  apply(auto elim!: interleave_Free_Free_NilE interleave_Free_Free_ConsE)
  done


theorem interleave_right_neutral: "interleave xs [] zs \<longleftrightarrow> xs = zs"
  apply(subst interleave_flip)
  apply(rule interleave_left_neutral)
  done


theorem interleave_count[rule_format]: "\<forall>xs ys. interleave xs ys zs \<longrightarrow> mset xs + mset ys = mset zs"
  apply(induct_tac zs)
  apply(auto elim: interleave_Free_Free_NilE interleave_Free_Free_ConsE)
  done


theorem interleave_ex_concat: "\<forall>ys. interleave xs ys (xs@ys)"
  apply(induct_tac xs)
  apply(auto intro: interleave_left_neutralI)
  done


lemma list_double_induct[rule_format]: "P [] [] \<longrightarrow> (\<forall>x xs ys. P xs ys \<longrightarrow> P (x#xs) ys) \<longrightarrow> (\<forall>y xs ys. P xs ys \<longrightarrow> P xs (y#ys)) \<longrightarrow> P xs ys"
  apply(induct_tac xs)
  apply(induct_tac ys)
  apply(auto)
  done


lemma list_double_rev_induct[rule_format]: "P [] [] \<longrightarrow> (\<forall>x xs ys. P xs ys \<longrightarrow> P (xs@[x]) ys) \<longrightarrow> (\<forall>y xs ys. P xs ys \<longrightarrow> P xs (ys@[y])) \<longrightarrow> P xs ys"
  apply(rule_tac xs=xs in rev_induct)
  apply(rule_tac xs=ys in rev_induct)
  apply(auto)
  done


lemma interleave_Nil_Free_Free_rev: "interleave [] ys zs \<longleftrightarrow> interleave [] (rev ys) (rev zs)"
  apply(subst (1 2) interleave_left_neutral)
  apply(force)
  done


lemma interleave_Free_Nil_Free_rev: "interleave xs [] zs \<longleftrightarrow> interleave (rev xs) [] (rev zs)"
  apply(subst (1 2) interleave_flip)
  apply(rule interleave_Nil_Free_Free_rev)
  done


lemma interleave_append_Free_appendI[rule_format]: "\<forall>xs ys z x. interleave xs ys zs \<longrightarrow> x = z \<longrightarrow> interleave (xs@[x]) ys (zs@[z])"
  apply(induct zs)
  apply(force simp: interleave_Free_Free_Nil)
  apply(clarsimp)
  apply(erule interleave_Free_Free_ConsE)
  apply(auto)
  done


lemma interleave_Free_append_appendI[rule_format]: "interleave xs ys zs \<longrightarrow> y = z \<longrightarrow> interleave xs (ys@[y]) (zs@[z])"
  apply(subst (1 2) interleave_flip)
  apply(force elim: interleave_append_Free_appendI)
  done


lemma interleave_revI[rule_format]: "\<forall>xs ys. interleave xs ys zs \<longrightarrow> interleave (rev xs) (rev ys) (rev zs)"
  apply(induct zs)
  apply(force elim: interleave_Free_Free_NilE)
  apply(clarsimp)
  apply(erule interleave_Free_Free_ConsE)
  apply(simp add: interleave_append_Free_appendI)
  apply(simp add: interleave_Free_append_appendI)
  done


lemma interleave_revD[rule_format]: "interleave (rev xs) (rev ys) (rev zs) \<longrightarrow> interleave xs ys zs"
  apply(subgoal_tac "\<exists>xs' ys' zs'. rev xs = xs' \<and> rev ys = ys' \<and> rev zs = zs' \<and> xs = rev xs' \<and> ys = rev ys' \<and> zs = rev zs'")
  apply(elim exE)
  apply(elim conjE)
  apply(erule ssubst)+
  apply(rule impI)
  apply(erule interleave_revI)
  apply(auto)
  done


lemma interleave_rev: "interleave (rev xs) (rev ys) (rev zs) \<longleftrightarrow> interleave xs ys zs"
  apply(rule iffI)
  apply(erule interleave_revD)
  apply(erule interleave_revI)
  done


lemma interleave_mapI[rule_format]: "\<forall>xs ys. interleave xs ys zs \<longrightarrow> interleave (map f ys) (map f xs) (map f zs)"
  apply(induct_tac zs)
  apply(force elim: interleave_Free_Free_NilE)
  apply(clarsimp)
  apply(erule interleave_Free_Free_ConsE)
  apply(auto)
  done


lemma interleave_single_single: "interleave [x] [y] zs \<longleftrightarrow> zs = [x, y] \<or> zs = [y, x]"
  apply(rule iffI)
  apply(erule interleave.cases)
  apply(auto simp: interleave_left_neutral interleave_right_neutral)
  done
end