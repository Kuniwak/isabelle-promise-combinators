theory SelfInv imports Main begin


definition self_inv :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "self_inv f \<equiv> \<forall>x. f (f x) = x"


lemma self_inv_self_inv_iff: "self_inv f \<Longrightarrow> f (f x) = x"
  apply(unfold self_inv_def)
  apply(force)
  done


lemma self_inv_bij: "self_inv f \<Longrightarrow> bij f"
  apply(unfold self_inv_def)
  apply(unfold bij_def)
  apply(rule conjI)
  apply(metis inj_def)
  apply(metis surj_def)
  done


lemma self_inv_flip: "\<lbrakk> self_inv f \<rbrakk> \<Longrightarrow> f y = x \<longleftrightarrow> y = f x"
  apply(frule self_inv_bij)
  apply(drule bij_is_inj)
  apply(unfold inj_def)
  apply(drule_tac x="y" in spec)
  apply(drule_tac x="f x" in spec)
  apply(unfold self_inv_def)
  apply(force)
  done


lemma ex_self_invI: "\<lbrakk> self_inv f; \<exists>y. Q y \<rbrakk> \<Longrightarrow> \<exists>x. Q (f x)"
  apply(drule self_inv_bij)
  apply(drule bij_is_surj)
  apply(unfold surj_def)
  apply(clarify)
  apply(drule_tac x=y in spec)
  apply(elim exE)
  apply(rule_tac x=x in exI)
  apply(simp)
  done


lemma lt_length_append_iff[rule_format]: "i < length xs \<longrightarrow> P ((xs@ys)!i) = P (xs!i)"
  apply(induct ys)
  apply(force)
  apply(simp add: nth_append)
  done


lemma map_self_inv: "self_inv f \<Longrightarrow> self_inv (map f)"
  apply(unfold self_inv_def)
  apply(auto iff:lt_length_append_iff)
  done
end