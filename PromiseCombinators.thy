theory PromiseCombinators imports Main Interleave SelfInv begin


datatype expr =
  Num nat |
  Tuple expr expr |
  Pending expr expr |
  Resolve expr |
  Reject expr |
  All2 expr |
  Race2 expr


datatype event =
  EventResolve expr |
  EventReject expr |
  EventAll2 |
  EventRace2L |
  EventRace2R



text "Unfailable world"
inductive
  UF_small_step :: "expr \<times> event list \<Rightarrow> expr \<times> event list \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
  UF_NumNumI[intro]:         "(Num n, ev) \<Rightarrow> (Num n, ev)" |
  UF_PendingResolveI[intro]: "(Pending a b, ev) \<Rightarrow> (Resolve a, ev@[EventResolve x])" |
  UF_All2ResolveI[intro]:    "\<lbrakk> (All2 (Tuple a b), ev) \<Rightarrow> (All2 (Tuple (Resolve a') (Resolve b')), ev') \<rbrakk> \<Longrightarrow> (All2 (Tuple a b), ev) \<Rightarrow> (Resolve (Tuple a' b'), ev'@[EventAll2])" |
  UF_Race2ResolveI1[intro]:  "\<lbrakk> (Race2 (Tuple a b), ev) \<Rightarrow> (Race2 (Tuple (Resolve a') _), ev') \<rbrakk> \<Longrightarrow> (Race2 (Tuple a b), ev) \<Rightarrow> (Resolve a', ev'@[EventRace2L])" |
  UF_Race2ResolveI2[intro]:  "\<lbrakk> (Race2 (Tuple a b), ev) \<Rightarrow> (Race2 (Tuple _ (Resolve b')), ev') \<rbrakk> \<Longrightarrow> (Race2 (Tuple a b), ev) \<Rightarrow> (Resolve b', ev'@[EventRace2R])" |

  UF_TupleTupleI[intro]:     "\<lbrakk> (a, ev) \<Rightarrow> (a', evA'); (b, ev) \<Rightarrow> (b', evB'); interleave evA' evB' ev' \<rbrakk> \<Longrightarrow> (Tuple a b, ev) \<Rightarrow> (Tuple a' b', ev')" |
  UF_PendingPendingI[intro]: "\<lbrakk> (a, ev) \<Rightarrow> (a', evA'); (b, ev) \<Rightarrow> (b', evB'); interleave evA' evB' ev' \<rbrakk> \<Longrightarrow> (Pending a b, ev) \<Rightarrow> (Pending a' b', ev')" |
  UF_ResolveResolveI[intro]: "\<lbrakk> (x, ev) \<Rightarrow> (x', ev') \<rbrakk> \<Longrightarrow> (Resolve x, ev) \<Rightarrow> (Resolve x', ev')" |
  UF_All2All2I[intro]:       "\<lbrakk> (Tuple a b, ev) \<Rightarrow> (Tuple a' b', ev') \<rbrakk> \<Longrightarrow> (All2 (Tuple a b), ev) \<Rightarrow> (All2 (Tuple a' b'), ev')" |
  UF_Race2Race2I[intro]:     "\<lbrakk> (Tuple a b, ev) \<Rightarrow> (Tuple a' b', ev') \<rbrakk> \<Longrightarrow> (Race2 (Tuple a b), ev) \<Rightarrow> (Race2 (Tuple a' b'), ev')"


lemma "(Tuple (Num 0) (Num 1), []) \<Rightarrow> (Tuple (Num 0) (Num 1), [])"
  apply(subst (2) append.right_neutral[symmetric])
  apply(rule UF_TupleTupleI)
  apply(rule UF_NumNumI)
  apply(rule UF_NumNumI)
  apply(force)
  done


lemma "(Pending (Num 0) (Num 1), []) \<Rightarrow> (Resolve (Num 0), [EventResolve (Num 0)])"
  apply(subst (2) append.left_neutral[symmetric])
  apply(rule UF_PendingResolveI)
  done


lemma "(Race2 (Tuple (Pending (Num 0) (Num 1)) (Pending (Num 2) (Num 3))), []) \<Rightarrow> (Resolve (Num 0), [EventResolve (Num 0)]@[EventRace2L])"
  apply(rule UF_Race2ResolveI1)
  apply(rule UF_Race2Race2I)
  apply(subst (2) append.right_neutral[symmetric])
  apply(rule UF_TupleTupleI)
  apply(rule UF_PendingResolveI)
  apply(rule UF_PendingPendingI)
  apply(rule UF_NumNumI)
  apply(rule UF_NumNumI)
  apply(rule interleave_Nil_NilI)
  apply(simp)
  apply(rule interleave_Cons_FreeI)
  apply(rule interleave_Nil_NilI)
  done


lemma "(Race2 (Tuple (Pending (Num 0) (Num 1)) (Pending (Num 2) (Num 3))), []) \<Rightarrow> (Resolve (Num 2), [EventResolve (Num 2)]@[EventRace2R])"
  apply(rule UF_Race2ResolveI2)
  apply(rule UF_Race2Race2I)
  apply(subst (2) append.right_neutral[symmetric])
  apply(rule_tac ev="[]" in UF_TupleTupleI)
  apply(rule UF_PendingPendingI)
  apply(rule UF_NumNumI)
  apply(rule UF_NumNumI)
  apply(rule interleave_Nil_NilI)
  apply(rule UF_PendingResolveI)
  apply(simp)
  apply(rule interleave_Free_ConsI)
  apply(rule interleave_Nil_NilI)
  done


lemma "(All2 (Tuple (Pending (Num 0) (Num 1)) (Pending (Num 2) (Num 3))), []) \<Rightarrow> (Resolve (Tuple (Num 0) (Num 2)), [EventResolve (Num 0)]@[EventResolve (Num 2)]@[EventAll2])"
  apply(subst append_assoc[symmetric])
  apply(rule UF_All2ResolveI)
  apply(rule UF_All2All2I)
  apply(rule_tac ev="[]" in UF_TupleTupleI)
  apply(rule UF_PendingResolveI)
  apply(rule UF_PendingResolveI)
  apply(clarsimp)
  apply(auto)
  done


lemma "(All2 (Tuple (Pending (Num 0) (Num 1)) (Pending (Num 2) (Num 3))), []) \<Rightarrow> (Resolve (Tuple (Num 0) (Num 2)), [EventResolve (Num 2)]@[EventResolve (Num 0)]@[EventAll2])"
  apply(subst append_assoc[symmetric])
  apply(rule UF_All2ResolveI)
  apply(rule UF_All2All2I)
  apply(rule_tac ev="[]" in UF_TupleTupleI)
  apply(rule UF_PendingResolveI)
  apply(rule UF_PendingResolveI)
  apply(auto)
  done


fun flip :: "expr \<Rightarrow> expr" where
  "flip (All2 a) = All2 (flip a)" |
  "flip (Race2 a) = Race2 (flip a)" |
  "flip (Tuple a b) = Tuple (flip b) (flip a)" |
  "flip (Pending a b) = Pending (flip a) (flip b)" |
  "flip (Resolve a) = Resolve (flip a)" |
  "flip (Reject a) = Reject (flip a)" |
  "flip (Num n) = Num n"


theorem flip_self_inv: "self_inv flip"
  apply(unfold self_inv_def)
  apply(clarify)
  apply(rule expr.induct)
  apply(auto)
  done


fun flip_ev1 :: "event \<Rightarrow> event" where
  "flip_ev1 EventRace2L = EventRace2R" |
  "flip_ev1 EventRace2R = EventRace2L" |
  "flip_ev1 x = x"


theorem flip_ev1_self_inv: "self_inv flip_ev1"
  apply(unfold self_inv_def)
  apply(clarify)
  apply(case_tac "x")
  apply(auto)
  done


definition flip_ev :: "event list \<Rightarrow> event list" where
  "flip_ev \<equiv> map flip_ev1"


theorem flip_ev_self_inv: "self_inv flip_ev"
  apply(unfold flip_ev_def)
  apply(rule map_self_inv)
  apply(rule flip_ev1_self_inv)
  done


theorem UF_flip[rule_format]: "x \<Rightarrow> x' \<longrightarrow> (\<forall>e ev e' ev'. x = (e, ev) \<and> x' = (e', ev') \<longrightarrow> (flip e, flip_ev ev) \<Rightarrow> (flip e', flip_ev ev'))"
  apply(rule impI)
  apply(erule UF_small_step.induct)
  apply(auto simp: flip_ev_def)
  apply(force intro: interleave_mapI)
  apply(rule UF_PendingPendingI)
  apply(assumption)
  apply(assumption)
  apply(rule interleave_mapI)
  apply(subst interleave_flip)
  apply(assumption)
  done


theorem UF_arbitrariness: "\<exists>x0 x1 ev1 x2 ev2. (x0, []) \<Rightarrow> (x1, ev1) \<and> (x0, []) \<Rightarrow> (x2, ev2) \<and> x1 \<noteq> x2"
  apply(rule_tac x="Race2 (Tuple (Resolve (Num 1)) (Resolve (Num 2)))" in exI)
  apply(rule_tac x="Resolve (Num 1)" in exI)
  apply(rule_tac x="[EventRace2L]" in exI)
  apply(rule_tac x="Resolve (Num 2)" in exI)
  apply(rule_tac x="[EventRace2R]" in exI)
  apply(intro conjI)
  apply(subst (2) append.left_neutral[symmetric])
  apply(rule)+
  apply(subst (2) append.left_neutral[symmetric])
  apply(rule)+
  apply(simp)
  done


definition Tuple3 :: "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" where
  "Tuple3 a b c \<equiv> Tuple a (Tuple b c)"


definition All3 :: "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" where
  "All3 a b c \<equiv> All2 (Tuple a (All2 (Tuple b c)))"


theorem "\<exists>ev. (All3 (Pending (Num 3) (Num 0)) (Pending (Num 2) (Num 0)) (Pending (Num 1) (Num 0)), []) \<Rightarrow> (Resolve (Tuple3 (Num 3) (Num 2) (Num 1)), ev)"
  apply(rule_tac x="[EventResolve (Num 3)]@[EventResolve (Num 2)]@[EventResolve (Num 1)]@[EventAll2]@[EventAll2]" in exI)
  apply(unfold All3_def Tuple3_def)
  apply(subst append_assoc[symmetric])+
  apply(rule)+
  apply(force)
  apply(simp)
  apply(rule)+
  done
end