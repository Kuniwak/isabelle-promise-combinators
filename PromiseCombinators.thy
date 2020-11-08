theory PromiseCombinators imports Main Interleave SelfInv begin


datatype expr =
  Num nat |
  Tuple expr expr |
  Pending expr expr |
  PendingForever |
  Resolve expr |
  Reject expr |
  All2 expr |
  Race2 expr


datatype event =
  EventResolve expr |
  EventReject expr


text "Unfailable world"
inductive
  UF_small_step :: "expr \<times> event list \<Rightarrow> expr \<times> event list \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
  UF_NumNumI[intro]:                "(Num n, ev) \<Rightarrow> (Num n, ev)" |
  UF_PendingResolveI[intro]:        "(Pending a b, ev) \<Rightarrow> (Resolve a, ev@[EventResolve a])" |
  UF_PendingPendingForeverI[intro]: "(Pending a b, ev) \<Rightarrow> (PendingForever, ev)" |
  UF_PendingForeverPendingForeverI[intro]: "(PendingForever, ev) \<Rightarrow> (PendingForever, ev)" |
  UF_All2ResolveI[intro]:           "\<lbrakk> (All2 (Tuple a b), ev) \<Rightarrow> (All2 (Tuple (Resolve a') (Resolve b')), ev') \<rbrakk> \<Longrightarrow> (All2 (Tuple a b), ev) \<Rightarrow> (Resolve (Tuple a' b'), ev')" |
  UF_Race2ResolveI1[intro]:         "\<lbrakk> (Race2 (Tuple a b), ev) \<Rightarrow> (Race2 (Tuple (Resolve a') b'), ev') \<rbrakk> \<Longrightarrow> (Race2 (Tuple a b), ev) \<Rightarrow> (Resolve a', ev')" |
  UF_Race2ResolveI2[intro]:         "\<lbrakk> (Race2 (Tuple a b), ev) \<Rightarrow> (Race2 (Tuple a' (Resolve b')), ev') \<rbrakk> \<Longrightarrow> (Race2 (Tuple a b), ev) \<Rightarrow> (Resolve b', ev')" |

  UF_TupleTupleI[intro]:            "\<lbrakk> (a, ev) \<Rightarrow> (a', evA'); (b, ev) \<Rightarrow> (b', evB'); interleave evA' evB' ev' \<rbrakk> \<Longrightarrow> (Tuple a b, ev) \<Rightarrow> (Tuple a' b', ev')" |
  UF_PendingPendingI[intro]:        "\<lbrakk> (a, ev) \<Rightarrow> (a', evA'); (b, ev) \<Rightarrow> (b', evB'); interleave evA' evB' ev' \<rbrakk> \<Longrightarrow> (Pending a b, ev) \<Rightarrow> (Pending a' b', ev')" |
  UF_ResolveResolveI[intro]:        "\<lbrakk> (x, ev) \<Rightarrow> (x', ev') \<rbrakk> \<Longrightarrow> (Resolve x, ev) \<Rightarrow> (Resolve x', ev')" |
  UF_All2All2I[intro]:              "\<lbrakk> (Tuple a b, ev) \<Rightarrow> (Tuple a' b', ev') \<rbrakk> \<Longrightarrow> (All2 (Tuple a b), ev) \<Rightarrow> (All2 (Tuple a' b'), ev')" |
  UF_Race2Race2I[intro]:            "\<lbrakk> (Tuple a b, ev) \<Rightarrow> (Tuple a' b', ev') \<rbrakk> \<Longrightarrow> (Race2 (Tuple a b), ev) \<Rightarrow> (Race2 (Tuple a' b'), ev')"


inductive_cases UF_All2_ResolveE: "(All2 (Tuple a b), ev) \<Rightarrow> (Resolve (Tuple a' b'), ev')"
inductive_cases UF_All2_All2E: "(All2 (Tuple a b), ev) \<Rightarrow> (All2 (Tuple a' b'), ev')"
inductive_cases UF_Tuple_TupleE: "(Tuple a b, ev) \<Rightarrow> (Tuple a' b', ev')"
inductive_cases UF_Pending_ResolveE: "(Pending a b, ev) \<Rightarrow> (Resolve a', ev')"
inductive_cases UF_Race2_ResolveE: "(Race2 (Tuple a b), ev) \<Rightarrow> (Resolve a', ev')"
inductive_cases UF_Race2_Race2E: "(Race2 (Tuple a b), ev) \<Rightarrow> (Race2 (Tuple a' b'), ev')"
inductive_cases UF_PendingForever_FreeE: "(PendingForever, ev) \<Rightarrow> (x', ev')"


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


lemma "(Race2 (Tuple (Pending (Num 0) (Num 1)) (Pending (Num 2) (Num 3))), []) \<Rightarrow> (Resolve (Num 0), [EventResolve (Num 0)])"
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


lemma "(Race2 (Tuple (Pending (Num 0) (Num 1)) (Pending (Num 2) (Num 3))), []) \<Rightarrow> (Resolve (Num 2), [EventResolve (Num 2)])"
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


lemma "(All2 (Tuple (Pending (Num 0) (Num 1)) (Pending (Num 2) (Num 3))), []) \<Rightarrow> (Resolve (Tuple (Num 0) (Num 2)), [EventResolve (Num 0)]@[EventResolve (Num 2)])"
  apply(rule UF_All2ResolveI)
  apply(rule UF_All2All2I)
  apply(rule_tac ev="[]" in UF_TupleTupleI)
  apply(rule UF_PendingResolveI)
  apply(rule UF_PendingResolveI)
  apply(clarsimp)
  apply(auto)
  done


lemma "(All2 (Tuple (Pending (Num 0) (Num 1)) (Pending (Num 2) (Num 3))), []) \<Rightarrow> (Resolve (Tuple (Num 0) (Num 2)), [EventResolve (Num 2)]@[EventResolve (Num 0)])"
  apply(rule UF_All2ResolveI)
  apply(rule UF_All2All2I)
  apply(rule_tac ev="[]" in UF_TupleTupleI)
  apply(rule UF_PendingResolveI)
  apply(rule UF_PendingResolveI)
  apply(auto)
  done


fun
  flip :: "expr \<Rightarrow> expr"
where
  "flip (All2 a) = All2 (flip a)" |
  "flip (Race2 a) = Race2 (flip a)" |
  "flip (Tuple a b) = Tuple (flip b) (flip a)" |
  "flip (Pending a b) = Pending (flip a) (flip b)" |
  "flip (Resolve a) = Resolve (flip a)" |
  "flip (Reject a) = Reject (flip a)" |
  "flip (Num n) = Num n" |
  "flip PendingForever = PendingForever"


theorem flip_self_inv: "self_inv flip"
  apply(unfold self_inv_def)
  apply(clarify)
  apply(rule expr.induct)
  apply(auto)
  done


lemma flip_flip_ident: "flip (flip x) = x"
  apply(rule self_inv_self_inv_iff)
  apply(rule flip_self_inv)
  done


fun
  flip_ev1 :: "event \<Rightarrow> event"
where
  "flip_ev1 (EventResolve a) = EventResolve (flip a)" |
  "flip_ev1 (EventReject b) = EventReject (flip b)"


theorem flip_ev1_self_inv: "self_inv flip_ev1"
  apply(unfold self_inv_def)
  apply(clarify)
  apply(case_tac "x")
  apply(auto simp: self_inv_self_inv_iff flip_self_inv)
  done


definition
  flip_ev :: "event list \<Rightarrow> event list"
where
  "flip_ev \<equiv> map flip_ev1"


theorem flip_ev_self_inv: "self_inv flip_ev"
  apply(unfold flip_ev_def)
  apply(rule map_self_inv)
  apply(rule flip_ev1_self_inv)
  done


lemma flip_ev_Nil: "flip_ev [] = []"
  apply(unfold flip_ev_def)
  apply(auto)
  done


lemma flip_ev_flip_ev_ident: "flip_ev (flip_ev x) = x"
  apply(rule self_inv_self_inv_iff)
  apply(rule flip_ev_self_inv)
  done


lemma UF_flipI[rule_format]: "x \<Rightarrow> x' \<longrightarrow> (\<forall>e ev e' ev'. x = (e, ev) \<and> x' = (e', ev') \<longrightarrow> (flip e, flip_ev ev) \<Rightarrow> (flip e', flip_ev ev'))"
  apply(rule impI)
  apply(erule UF_small_step.induct)
  apply(auto simp: flip_ev_def)
  apply(rule UF_TupleTupleI)
  apply(auto intro: interleave_mapI)
  apply(rule UF_PendingPendingI)
  apply(auto intro: interleave_mapI simp add: interleave_flip)
  done


lemma UF_flipD[rule_format]: "(flip x, flip_ev ev) \<Rightarrow> (flip x', flip_ev ev') \<longrightarrow> (x, ev) \<Rightarrow> (x', ev')"
  apply(subgoal_tac "\<exists>y y' eev eev'. flip x = y \<and> flip x' = y' \<and> flip_ev ev = eev \<and> flip_ev ev' = eev' \<and> x = flip y \<and> x' = flip y' \<and> ev = flip_ev eev \<and> ev' = flip_ev eev'")
  apply(elim exE conjE)
  apply(erule ssubst)+
  apply(rule impI)
  apply(erule UF_flipI)
  apply(auto simp add: flip_self_inv flip_ev_self_inv self_inv_self_inv_iff)
  done


theorem UF_flip: "(flip x, flip_ev ev) \<Rightarrow> (flip x', flip_ev ev') \<longleftrightarrow> (x, ev) \<Rightarrow> (x', ev')"
  apply(rule iffI)
  apply(erule UF_flipD)
  apply(erule UF_flipI)
  apply(simp)
  done


theorem UF_arbitrariness: "\<exists>x0 x1 ev1 x2 ev2. (x0, []) \<Rightarrow> (x1, ev1) \<and> (x0, []) \<Rightarrow> (x2, ev2) \<and> x1 \<noteq> x2"
  apply(rule_tac x="Race2 (Tuple (Resolve (Num 1)) (Resolve (Num 2)))" in exI)
  apply(rule_tac x="Resolve (Num 1)" in exI)
  apply(rule_tac x="[]" in exI)
  apply(rule_tac x="Resolve (Num 2)" in exI)
  apply(rule_tac x="[]" in exI)
  apply(intro conjI)
  apply(subst (2) append.left_neutral[symmetric])
  apply(rule UF_Race2ResolveI1)
  apply(force)
  apply(subst (2) append.left_neutral[symmetric])
  apply(rule)+
  apply(auto)
  done


definition
  Tuple3 :: "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "Tuple3 a b c \<equiv> Tuple a (Tuple b c)"


definition
  All3 :: "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
where
  "All3 a b c \<equiv> All2 (Tuple a (All2 (Tuple b c)))"


theorem "\<exists>ev. (All3 (Pending (Num 3) (Num 0)) (Pending (Num 2) (Num 0)) (Pending (Num 1) (Num 0)), []) \<Rightarrow> (Resolve (Tuple3 (Num 3) (Num 2) (Num 1)), ev)"
  apply(rule_tac x="[EventResolve (Num 3)]@[EventResolve (Num 2)]@[EventResolve (Num 1)]" in exI)
  apply(unfold All3_def Tuple3_def)
  apply(subst append_assoc[symmetric])+
  apply(rule)+
  apply(force)
  apply(simp)
  apply(rule)+
  done


definition
  events :: "expr \<Rightarrow> expr \<Rightarrow> event list set"
where
  "events x x' \<equiv> { ev | ev. (x, []) \<Rightarrow> (x', ev) }"


lemma flip_Nil_flip_Free: "(flip x, []) \<Rightarrow> (flip x', ev) \<longleftrightarrow> (x, []) \<Rightarrow> (x', flip_ev ev)"
  apply(subgoal_tac "\<exists>ev'. ev = flip_ev ev' \<and> ev' = flip_ev ev \<and> [] = flip_ev []")
  apply(elim exE conjE)
  apply(erule ssubst)+
  apply(subst UF_flip)
  apply(subst flip_ev_flip_ev_ident)
  apply(subst flip_ev_Nil)
  apply(rule refl)
  apply(rule_tac x="flip_ev ev" in exI)
  apply(force simp add: flip_ev_flip_ev_ident flip_ev_Nil)
  done


lemma events_flip_flip1[rule_format]: "\<lbrakk> fev = flip_ev ` events (flip x) (flip x') \<rbrakk> \<Longrightarrow> fev \<subseteq> events x x'"
  apply(erule ssubst)
  apply(unfold events_def)
  apply(subst flip_Nil_flip_Free)
  apply(auto simp add: image_def)
  done


lemma events_flip_flip2[rule_format]: "\<lbrakk> fev = flip_ev ` events (flip x) (flip x') \<rbrakk> \<Longrightarrow> events x x' \<subseteq> fev"
  apply(subgoal_tac "\<exists>y y'. x = flip y \<and> x' = flip y'")
  apply(elim exE conjE)
  apply(erule ssubst)+
  apply(simp only: flip_flip_ident)
  apply(rule_tac x="flip_ev ` events (flip y) (flip y')" in self_inv_image_subsetI)
  apply(rule flip_ev_self_inv)
  apply(rule events_flip_flip1)
  apply(rule refl)
  apply(force simp add: flip_ev_flip_ev_ident)
  apply(rule_tac x="flip x" in exI)
  apply(rule_tac x="flip x'" in exI)
  apply(force simp add: flip_flip_ident)
  done


lemma events_flip_flip: "flip_ev ` events (flip x) (flip x') = events x x'"
  apply(rule equalityI)
  apply(rule events_flip_flip1)
  apply(rule refl)
  apply(rule events_flip_flip2)
  apply(rule refl)
  done


fun
  to_appended_all :: "'a list \<Rightarrow> 'a list"
where
  "to_appended_all [] = []" |
  "to_appended_all [x] = [x]" |
  "to_appended_all (x1#x2#xs) = ([x1]@[x2])@(to_appended_all xs)"


definition
  appended_all :: "'a list \<Rightarrow> 'a list"
where
  "appended_all \<equiv> to_appended_all"


lemma appended_all_map: "appended_all (map f x) = map f (appended_all x)"
  apply(rule_tac P="\<lambda>x. appended_all (map f x) = map f (appended_all x)" in to_appended_all.induct)
  apply(unfold appended_all_def flip_ev_def)
  apply(auto)
  done


theorem All2_events: "
  events
    (All2 (Tuple (Pending (Num 1) (Num 0)) (Pending (Num 2) (Num 0))))
    (Resolve (Tuple (Num 1) (Num 2)))
  = {
    appended_all [EventResolve (Num 1), EventResolve (Num 2)],
    appended_all [EventResolve (Num 2), EventResolve (Num 1)]
  }"
  apply(unfold events_def)
  apply(intro equalityI subsetI)
  apply(clarsimp)
  apply(elim UF_All2_ResolveE UF_All2_All2E UF_Tuple_TupleE UF_Pending_ResolveE)
  apply(auto simp add: interleave_single_single)
  apply(unfold appended_all_def to_appended_all.simps)
  apply(force)
  apply(force)
  apply(rule)+
  apply(simp add: interleave_single_single)
  apply(rule)+
  apply(simp add: interleave_single_single)
  done


theorem Race2L_events: "
  events
    (Race2 (Tuple (Pending (Num 1) (Num 0)) PendingForever))
    (Resolve (Num 1))
  = { appended_all [EventResolve (Num 1)] }"
  apply(unfold events_def)
  apply(intro equalityI subsetI)
  apply(clarsimp)
  apply(elim UF_Race2_ResolveE UF_Race2_Race2E UF_Tuple_TupleE UF_PendingForever_FreeE)
  apply(clarsimp simp add: interleave_right_neutral)
  apply(elim UF_Pending_ResolveE)
  apply(force simp: appended_all_def)
  apply(force)
  apply(simp)
  apply(clarify)
  apply(unfold appended_all_def to_appended_all.simps append.right_neutral)
  apply(rule UF_Race2ResolveI1)
  apply(rule)+
  apply(simp add: interleave_right_neutral)
  done
 

theorem Race2R_events: "
  events
    (Race2 (Tuple PendingForever (Pending (Num 1) (Num 0))))
    (Resolve (Num 1))
  = { appended_all [EventResolve (Num 1)] }"
  apply(subst events_flip_flip[symmetric])
  apply(subst self_inv_flip [where f="image flip_ev"])
  apply(rule image_self_inv)
  apply(rule flip_ev_self_inv)
  apply(simp del: One_nat_def add: flip_ev_def appended_all_map[symmetric])
  apply(rule Race2L_events)
  done


theorem "(
  (Race2 (Tuple
    (All2 (Tuple (Pending (Num 1) (Num 0)) (Pending (Num 1) (Num 0))))
    (All2 (Tuple (Pending (Num 1) (Num 0)) PendingForever))
  )), []) \<Rightarrow>
  (Resolve (Tuple (Num 1) (Num 1)), [EventResolve (Num 1)]@[EventResolve (Num 1)])
"
  apply(rule UF_Race2ResolveI1)
  apply(rule)+
  apply(simp add: interleave_single_single)
  apply(rule)+
  apply(simp add: interleave_right_neutral)
  done


theorem "(
  (Race2 (Tuple
    (All2 (Tuple (Pending (Num 1) (Num 0)) (Pending (Num 1) (Num 0))))
    (All2 (Tuple (Pending (Num 1) (Num 0)) (Pending (Num 2) (Num 0))))
  )), []) \<Rightarrow>
  (Resolve (Tuple (Num 1) (Num 2)), [EventResolve (Num 1)]@[EventResolve (Num 2)])
"
  apply(rule UF_Race2ResolveI2)
  apply(rule)+
  apply(simp add: interleave_left_neutral)
  apply(rule interleave_Cons_FreeI)
  apply(rule interleave_Free_ConsI)
  apply(rule interleave_Nil_NilI)
  apply(auto)
  done
end