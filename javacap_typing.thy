theory javacap_typing
imports
  Main
  javacap_syntax
  javacap_auxiliary
begin   

(* \<T> is a tuple of the type and label. This is convenient as they are often used together. *)
type_synonym \<T> = "\<tau> \<times> label"

(* local environment *)
type_synonym lenv = "(var \<rightharpoonup> \<T>)"

(* synonym to provide additional meaning to capability sets passed around *)
type_synonym require_caps = "iname set" (* method requires clause *)
type_synonym parent_caps = "iname set" (* label of parent object *)

(* Method environment. Used as part of the context in which to type-check statements.
   The first component is the class name in which the method is declared.
   The second component is the labelled return type of the method.
   The third component is the requires clause of the method.
   *)
record msenv =
  mscname :: "cname"
  msreturn :: "\<T>"
  msreq :: "require_caps"

(* "(cname \<times> (\<T> \<times> require_caps))"

abbreviation msreq :: "msenv \<Rightarrow> require_caps"
  where "msreq \<equiv> snd"

abbreviation msreturn :: "msenv \<Rightarrow> \<T>"
  where "msreturn \<equiv> fst"*)

definition intersect_label :: "\<T> \<Rightarrow> parent_caps \<Rightarrow> \<T>"
  where "intersect_label \<equiv> (\<lambda>(t,\<gamma>) \<gamma>'. (t,\<gamma> \<inter> \<gamma>'))"

lemma intersect_label_type:
  shows "ttype (intersect_label T \<gamma>) = ttype T"
  unfolding intersect_label_def by (simp add: case_prod_beta') 

lemma intersect_label_label:
  shows "tlabel (intersect_label T \<gamma>) = (tlabel T) \<inter> \<gamma>"
  unfolding intersect_label_def by (simp add: case_prod_beta') 

lemma intersect_label_vary:
  assumes "T' = intersect_label T \<gamma>0"
  assumes "\<gamma> = (\<gamma>0 \<inter> \<gamma>1)"
  shows "(intersect_label T \<gamma>) = (intersect_label T' \<gamma>1)"
  using assms unfolding intersect_label_def by (simp add: case_prod_beta' inf_assoc) 

abbreviation var_type :: "lenv \<Rightarrow> var \<Rightarrow> \<T> option" ("_\<lbrakk>_\<rbrakk>\<^sub>v" 50)
  where "var_type \<equiv> id"

(* Subtyping relation *)
inductive subtype :: "prog \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> bool" ("_ \<turnstile> _ <: _")  (* \<Gamma> \<turnstile> t1 <: t2, i.e. t1 implements t2 *)
  for P :: "prog"
  where subtype_self:   "P \<turnstile> t <: t" |
        subtype_cextend: "\<lbrakk>t1 \<noteq> Object; (class P t1) = Some c1; (cextends c1 = t2)\<rbrakk> \<Longrightarrow> P \<turnstile> (ClassT t1) <: (ClassT t2)" |
        subtype_cimpl:   "\<lbrakk>(class P t1) = Some c1; (t2 \<in> set (cimpl c1))\<rbrakk> \<Longrightarrow> P \<turnstile> (ClassT t1) <: (IfaceT t2)" |
        subtype_iextend:  "\<lbrakk>(interface P t1) = Some i1; (t2 \<in> set (iextends i1))\<rbrakk> \<Longrightarrow> P \<turnstile> (IfaceT t1) <: (IfaceT t2)" |
        subtype_trans: "\<lbrakk>P \<turnstile> t1 <: t2 ; P \<turnstile> t2 <: t3\<rbrakk> \<Longrightarrow> P \<turnstile> t1 <: t3"

(* Lemmas for subtyping relation *)
lemma subtype_derived_class: (* Classes can only derive classes. *)
  assumes ct1_extends_t0: "(P \<turnstile> ct1 <: (ClassT t0))"
  shows "\<exists>t1. ct1 = (ClassT t1)"
proof -
  have "(P \<turnstile> ct1 <: (ClassT t0))" using ct1_extends_t0 by simp
  then show ?thesis proof (induction "ct1" "(ClassT t0)" arbitrary: t0)
    case (subtype_self)
    then show ?case by simp
  next
    case (subtype_cextend t1 c1 t2)
    then show ?case by simp
  next
    case (subtype_trans t1 t2)
    then show ?case by blast
  qed
qed

lemma subtype_int_parity:
  shows "P \<turnstile> t1 <: t0 \<Longrightarrow> (t1 = ValT t) = (t0 = ValT t)"
proof (induction "t1" "t0" rule:subtype.induct)
  case subtype_self
  then show ?case by simp
next
  case (subtype_cextend t1 c1 t2)
  then show ?case by simp
next
  case (subtype_cimpl t1 c1 t2)
  then show ?case by simp
next
  case subtype_iextend
  then show ?case by simp
next
  case (subtype_trans t1 t2 t3)
  then show ?case by simp
qed


lemma subtype_exists:
  shows "P \<turnstile> t1 <: t0 \<Longrightarrow> is_type P t0 \<Longrightarrow> is_type P t1"
proof (induction "t1" "t0"  rule:subtype.induct)
  case subtype_self
  then show ?case by auto
next
  case (subtype_cextend t1 c1 t2)
  then show ?case using is_class_def by simp
next
  case (subtype_cimpl t1 c1 t2)
  then show ?case using is_class_def by simp
next
  case subtype_iextend
  then show ?case using is_interface_def by simp
next
  case (subtype_trans t1 t2 t3)
  then show ?case using subtype_derived_class by blast
qed

lemma subclass_subtype:
  shows "(c,s)\<in>(subclass P) \<Longrightarrow> P \<turnstile> (ClassT c) <: (ClassT s)"
proof (induction rule:rtrancl_induct)
  case base
  then show ?case using subtype_self by simp
next
  case (step y z)
  moreover have "P \<turnstile> (ClassT y) <: (ClassT z)" 
    using step subtype_cextend unfolding direct_subclass_def by blast
  ultimately show ?case using subtype_trans by metis
qed

end