theory javacap_static
imports
  Main
  javacap_syntax
  javacap_auxiliary
  javacap_typing
begin

(* Static typing rules*)


(* Helper for defining when a method call is valid *)
definition wf_method_call ::  "prog \<Rightarrow> lenv \<Rightarrow> mdecl \<Rightarrow> var list \<Rightarrow> parent_caps \<Rightarrow> \<T> \<Rightarrow> bool"
  where "wf_method_call P \<Gamma> decl args \<gamma> Treturn \<equiv> 
          (* check number of args *)
          (length (mpar decl) = length args) \<and>
          (* check each arg *)
          (\<forall>i\<in>{0..<(length args)}.
              let Targdecl = ((msig (mpar decl)) ! i) in
                 (\<Gamma>\<lbrakk>args!i\<rbrakk>\<^sub>v = Some (intersect_label Targdecl \<gamma>))) \<and>
          (* check return type *)
          (Treturn = intersect_label (mret decl) \<gamma>)"

definition wf_fieldi_access :: "prog \<Rightarrow> lenv \<Rightarrow> var \<Rightarrow> fname \<Rightarrow> \<T> \<Rightarrow> bool"
  where "wf_fieldi_access P \<Gamma> x f T \<equiv> (\<exists>c \<gamma>x fdecl. (\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some ((ClassT c),\<gamma>x)) \<and> field P c f = Some fdecl \<and>
                                                     \<not>fstatic fdecl \<and>
                                                     T = intersect_label (ftype fdecl) \<gamma>x)"

definition wf_fields_access :: "prog \<Rightarrow> msenv \<Rightarrow> cname \<Rightarrow> fname \<Rightarrow> \<T> \<Rightarrow> bool"
  where "wf_fields_access P M c f T \<equiv> (\<exists>fdecl. is_class P c \<and> field P c f = Some fdecl \<and> fstatic fdecl \<and> 
                                         (T = (ftype fdecl) \<and> (tlabel (ftype fdecl)) \<subseteq> (msreq M)))"

(* Well-formed expressions *)
inductive wf_expr :: "prog \<Rightarrow> msenv \<Rightarrow> lenv \<Rightarrow> exp \<Rightarrow> \<T> \<Rightarrow> bool" ("_ _ _ \<turnstile> _ : _" 50) 
  for P :: "prog" and M :: "msenv"

(* datatype exp =
      ref "var" 
    | new "cname" 
    | calli "var" "mname" "var list" (* instance method call *)
    | calls "cname" "mname" "label" "var list" (* static method call *)
    | cast "\<tau>" "exp" 
    | const "k"
    | fieldacci "var" "fname"  (* instance field access *)
    | fieldaccs "cname" "fname" (* static field access *)
    | wrap "iname" "exp" *)
  where wf_expr_ref: "\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some \<T> \<Longrightarrow> P M \<Gamma> \<turnstile> (ref x) : \<T>"

      | wf_expr_new: "\<lbrakk> class P cname = Some c; (creq c) \<subseteq> (msreq M); (creq c) \<subseteq> \<gamma>;
                        \<gamma> \<inter> the (grant P (mscname M)) \<subseteq> the (grant P cname) \<rbrakk>
                      \<Longrightarrow> P M \<Gamma> \<turnstile> (new \<gamma> cname) : ((ClassT cname), \<gamma>)"
        (* i.e. if t' implements t, a t' can be implicitly converted to a t. *)
      | wf_expr_calli: "\<lbrakk>\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some (t0,\<gamma>0); methoddecl P t0 mname = Some decl; 
                        is_type P t0; (\<forall>t. t0 \<noteq> (ValT t)); \<not>mstatic decl; (* added all three *)
                        wf_method_call P \<Gamma> decl args \<gamma>0 Tr \<rbrakk> \<Longrightarrow> 
                        P M \<Gamma> \<turnstile> (calli x mname args) : Tr"
      | wf_expr_calls: "\<lbrakk>is_class P c; cmethod P c mname = Some (d,meth); mstatic (mdecl meth);
                         wf_method_call P \<Gamma> (mdecl meth) args lbl Tr; (mreq meth) \<subseteq> (msreq M);
                        (mreq meth) \<subseteq> lbl;
                        lbl \<inter> the (grant P (mscname M)) \<subseteq> the (grant P c) \<rbrakk> \<Longrightarrow>
                        P M \<Gamma> \<turnstile> (calls c mname lbl args) : Tr"
        (* Assumption not used: P \<turnstile> t <: t'  *)(* i.e. if t implements t', 
          then it is possible (but definitely not certain) the cast from t' down to t will be 
          possible at runtime. *)
      | wf_expr_cast: "\<lbrakk> P M \<Gamma> \<turnstile> e : (t',l);
                        \<not>is_cap_type P t'; \<not>is_cap_type P t \<rbrakk> \<Longrightarrow> P M \<Gamma> \<turnstile> (cast t e) : (t,l)"
      | wf_expr_const: "\<lbrakk> case k of null \<Rightarrow> (\<forall>vt. t \<noteq> (ValT vt)) | num n \<Rightarrow> (t = ValT IntT) \<rbrakk> 
                            \<Longrightarrow> P M \<Gamma> \<turnstile> (const k) : (t,l)"
      | wf_expr_fieldacci: "\<lbrakk> wf_fieldi_access P \<Gamma> x f T \<rbrakk> \<Longrightarrow> P M \<Gamma> \<turnstile> (fieldacci x f) : T" 
      | wf_expr_fieldaccs: "\<lbrakk> wf_fields_access P M c f T \<rbrakk> \<Longrightarrow> P M \<Gamma> \<turnstile> (fieldaccs c f) : T" 
      | wf_expr_sub: "\<lbrakk> P M \<Gamma> \<turnstile> e : (t',l); P \<turnstile> t' <: t;
                         \<not>is_cap_type P t'; (* technically not necessary, but makes our lives simpler *)
                         \<not>is_cap_type P t \<rbrakk> \<Longrightarrow> P M \<Gamma> \<turnstile> e : (t,l)"
      | wf_expr_wrap: "\<lbrakk>  P M \<Gamma> \<turnstile> e : (t',l); P \<turnstile> t' <: (IfaceT cbname);
                           is_cap P cbname; 
                          (* requires clause only needed if wrapping object as capability for the first time
                             to ensure the containing context is allowed to contain that capability.
                             subsequent wrapping only attentuates access. *)
                          \<not>is_cap_type P t' \<longrightarrow> (superinterface_set P cbname) \<subseteq> (msreq M) \<inter> l 
                        \<rbrakk> \<Longrightarrow> P M \<Gamma> \<turnstile> (wrap cbname e) : ((IfaceT cbname),l \<inter> (cap_label P cbname))"

(*
lemma wf_stmt_call_intro:
  assumes "P M \<Gamma> \<turnstile> (call x mname args) \<bullet>"
  shows "\<exists>t0 decl. (\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some t0) \<and> (methoddecl (eprog \<Gamma>) t0 mname = Some decl) \<and> is_type (eprog \<Gamma>) t0 \<and>
           (\<forall>t. t0 \<noteq> (ValT t)) \<and> length (mpar decl) = length args \<and>
           (\<forall>(argtype,actualarg)\<in>(set (zip (msig (mpar decl)) args)). (\<Gamma>\<lbrakk>actualarg\<rbrakk>\<^sub>v = Some argtype))"
  using assms wf_stmt.simps[where ?a2.0 = "call x mname args"] by auto
*)

(* Well-formed statements *)
inductive wf_stmt :: "prog \<Rightarrow> msenv \<Rightarrow> lenv \<Rightarrow> stmt \<Rightarrow> bool" ("_ _ _ \<turnstile> _ \<bullet>" 50)
  for P :: "prog" and M :: "msenv"
(* datatype stmt =
      assign "var" "exp" 
    | assignfi "var" "fname" "exp" 
    | assignfs "cname" "fname" "exp" 
    | expr "exp"
    | ifelse "var" "stmt" "stmt" 
    | letin "\<T>" "var" "exp" "stmt"
    | return "exp"
    | seq "stmt" "stmt" 
    | throw "exp"
    | trycatch "stmt" "(\<tau> \<times> var \<times> stmt) list" *)
  where wf_stmt_assign: "\<lbrakk>\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some T; P M \<Gamma> \<turnstile> e : T\<rbrakk> \<Longrightarrow> (P M \<Gamma> \<turnstile> (assign x e) \<bullet>)"
(* Update -- allow y to be a supertype of the LHS *)
      | wf_stmt_assignfi: "\<lbrakk> wf_fieldi_access P \<Gamma> x f T; P M \<Gamma> \<turnstile> e : T \<rbrakk>  
                           \<Longrightarrow> P M \<Gamma> \<turnstile> (assignfi x f e) \<bullet>"
      | wf_stmt_assignfs: "\<lbrakk> wf_fields_access P M c f T; P M \<Gamma> \<turnstile> e : T \<rbrakk> 
                            \<Longrightarrow> P M \<Gamma> \<turnstile> (assignfs c f e) \<bullet>"
      | wf_stmt_expr: "\<lbrakk> P M \<Gamma> \<turnstile> e : T \<rbrakk> \<Longrightarrow> P M \<Gamma> \<turnstile> (expr e) \<bullet>"
      | wf_stmt_ifelse: "\<lbrakk>\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some ((ValT IntT),l); P M \<Gamma> \<turnstile> s1 \<bullet>; P M \<Gamma> \<turnstile> s2 \<bullet>\<rbrakk> \<Longrightarrow> P M \<Gamma> \<turnstile> (ifelse x s1 s2) \<bullet>"
      | wf_stmt_letin: "\<lbrakk> P M \<Gamma>(x := None) \<turnstile> e : \<T>; P M \<Gamma>(x\<mapsto>\<T>) \<turnstile> s \<bullet> \<rbrakk>
                           \<Longrightarrow> P M \<Gamma> \<turnstile> (letin \<T> x e s) \<bullet>"
      | wf_stmt_return: "\<lbrakk> P M \<Gamma> \<turnstile> e : (msreturn M)  \<rbrakk>
                            \<Longrightarrow> P M \<Gamma> \<turnstile> (return e) \<bullet>" (* currently assume runtime check will take care of type-safety *)
      | wf_stmt_seq: "\<lbrakk> P M \<Gamma> \<turnstile> s1 \<bullet>; P M \<Gamma> \<turnstile> s2 \<bullet> \<rbrakk> \<Longrightarrow> P M \<Gamma> \<turnstile> seq s1 s2 \<bullet>"
      (* objects thrown shall have no capabilities *)
      | wf_stmt_throw: "\<lbrakk> P M \<Gamma> \<turnstile> e : (ClassT Object,{}) \<rbrakk> \<Longrightarrow> P M \<Gamma> \<turnstile> (throw e) \<bullet>" (* should check exceptions extend throwable? or not? *)
      | wf_stmt_trycatch: "\<lbrakk> P M \<Gamma> \<turnstile> s \<bullet>; (\<forall>(t,x,s')\<in>(set handlers). (P M \<Gamma>(x\<mapsto>(t,{})) \<turnstile> s' \<bullet>) \<and> \<not>is_cap_type P t) \<rbrakk>
                             \<Longrightarrow> P M \<Gamma> \<turnstile> (trycatch s handlers) \<bullet>"


(* Show extending \<Gamma> only ever maintains type-correctness,
   i.e. expression-type correctness is monotonic over \<Gamma> *)
lemma wf_expr_mono_lenv:
  shows "P M \<Gamma> \<turnstile> e : \<T> \<Longrightarrow> P M (\<Gamma>' ++ \<Gamma>) \<turnstile> e : \<T>"
proof (induction rule:wf_expr.induct)
  case (wf_expr_ref \<Gamma> x \<T>)
  then show ?case using wf_expr.wf_expr_ref by simp
next
  case (wf_expr_new cname c \<gamma> \<Gamma>)
  then show ?case using wf_expr.wf_expr_new by simp
next
  case (wf_expr_calli \<Gamma> x t0 \<gamma>0 mname decl args Tr)
  then show ?case using wf_expr.wf_expr_calli unfolding wf_method_call_def by simp
next
case (wf_expr_calls c mname decl \<Gamma> args l' Tr)
  then show ?case using wf_expr.wf_expr_calls unfolding wf_method_call_def by simp
next
  case (wf_expr_cast \<Gamma> e t' l t)
  then show ?case using wf_expr.wf_expr_cast by simp
next
  case (wf_expr_const k t \<Gamma> l)
  then show ?case using wf_expr.wf_expr_const by simp
next
  case (wf_expr_fieldacci \<Gamma> x f T)
  then show ?case using wf_expr.wf_expr_fieldacci unfolding wf_fieldi_access_def
    by (metis (mono_tags, hide_lams) id_apply map_add_find_right)
next
  case (wf_expr_fieldaccs c f T \<Gamma>)
  then show ?case using wf_expr.wf_expr_fieldaccs by simp
next
  case (wf_expr_sub \<Gamma> e t' l t)
  then show ?case using wf_expr.wf_expr_sub by simp
next
  case (wf_expr_wrap \<Gamma> e t' l cbname)
  then show ?case using wf_expr.wf_expr_wrap by simp
qed

(* Defines the allowed type-to-type subsumption *)
definition subsumption :: "prog \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> bool"
  where "subsumption P origt subt \<equiv> if (is_cap_type P subt) then subt = origt else ((P \<turnstile> origt <: subt))"
(* equiv: if (is_cap_type P origt) then subt = origt else ((P \<turnstile> origt <: subt) \<and> \<not>(is_cap_type P subt))
   under well-formed programs *)

lemma subsumption_self:
  shows "subsumption P t t"
  unfolding subsumption_def using subtype_self by auto

lemma subsumption_extend:
  assumes "subsumption P t2 t1"
  assumes "P \<turnstile> t1 <: t"
  assumes "\<not>is_cap_type P t1"
  assumes "\<not>is_cap_type P t" (* If we knew the program was well-formed, this could have been inferred. *)
  shows "subsumption P t2 t"
  using assms subtype_trans unfolding subsumption_def by metis

lemma wf_expr_ref_intro:
  shows "P M \<Gamma> \<turnstile> ref x : (t,\<gamma>) \<Longrightarrow> \<exists>T'. (\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some T') \<and> subsumption P (ttype T') t \<and> (\<gamma> = tlabel T')"
proof (induction "ref x" "(t,\<gamma>)" arbitrary:t rule:wf_expr.induct)
  case (wf_expr_ref \<Gamma> \<T>)
  then show ?case using subsumption_self by simp
next
  case (wf_expr_sub \<Gamma> t' t)
  then show ?case using subsumption_extend by blast
qed

lemma wf_expr_new_intro:
  shows "P M \<Gamma> \<turnstile> (new l cname) : (t, \<gamma>) \<Longrightarrow>
              \<exists>c. \<gamma> = l \<and> class P cname = Some c
                     \<and> (creq c) \<subseteq> (msreq M) \<and> (creq c) \<subseteq> \<gamma>
                     \<and> \<gamma> \<inter> the (grant P (mscname M)) \<subseteq> the (grant P cname)
                     \<and> (subsumption P (ClassT cname) t)"
proof (induction "new l cname" "(t, \<gamma>)" arbitrary: t rule:wf_expr.induct)
  case (wf_expr_new c \<Gamma>)
  then show ?case using subsumption_self by blast
next
  case (wf_expr_sub \<Gamma> t')
  then show ?case using subsumption_extend by blast
qed

lemma wf_expr_calli_intro:
  shows "P M \<Gamma> \<turnstile> (calli x mname args) : (t, \<gamma>) \<Longrightarrow>
            \<exists>t0 \<gamma>0 decl t'. (\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some (t0,\<gamma>0)) \<and> methoddecl P t0 mname = Some decl \<and>
                        is_type P t0 \<and> (\<forall>t. t0 \<noteq> (ValT t)) \<and> \<not>mstatic decl \<and> (* added all three *)
                        wf_method_call P \<Gamma> decl args \<gamma>0 (t',\<gamma>) \<and> (subsumption P t' t)"
proof (induction "calli x mname args" "(t,\<gamma>)" arbitrary:t rule:wf_expr.induct)
  case (wf_expr_calli \<Gamma> t0 \<gamma>0 decl)
  then show ?case using subsumption_self by blast
next
  case (wf_expr_sub \<Gamma> t' t)
  then show ?case using subsumption_extend by blast
qed

lemma wf_expr_calls_intro:
  shows "P M \<Gamma> \<turnstile> (calls c mname lbl args) : (t, \<gamma>) \<Longrightarrow>
            \<exists>meth t' d. is_class P c \<and> cmethod P c mname = Some (d,meth) \<and> mstatic (mdecl meth) \<and>
                        wf_method_call P \<Gamma> (mdecl meth) args lbl (t',\<gamma>) \<and> (mreq meth) \<subseteq> (msreq M) \<and>
                        lbl \<inter> the (grant P (mscname M)) \<subseteq> the (grant P c)
                      \<and> (mreq meth) \<subseteq> lbl \<and> (subsumption P t' t)"
proof (induction "calls c mname lbl args" "(t,\<gamma>)" arbitrary:t rule:wf_expr.induct)
  case (wf_expr_calls d meth \<Gamma>)
  then show ?case using subsumption_self by blast
next
  case (wf_expr_sub \<Gamma> t' t)
  then show ?case using subsumption_extend by blast
qed

lemma wf_expr_cast_intro:
  shows "P M \<Gamma> \<turnstile> (cast tcast e) : (t,\<gamma>) \<Longrightarrow> 
            \<exists>t'. (P M \<Gamma> \<turnstile> e : (t',\<gamma>)) \<and> \<not>is_cap_type P t' \<and> \<not>is_cap_type P tcast \<and> (subsumption P tcast t)"
proof (induction "cast tcast e" "(t,\<gamma>)" arbitrary:t rule:wf_expr.induct)
  case (wf_expr_cast \<Gamma> t')
  then show ?case using subsumption_self by blast
next
  case (wf_expr_sub \<Gamma> t' t)
  then show ?case using subsumption_extend by blast
qed

lemma wf_expr_const_intro:
  shows "P M \<Gamma> \<turnstile> (const k) : (t,\<gamma>) \<Longrightarrow> 
            \<exists>t'. (case k of null \<Rightarrow> (\<forall>vt. t' \<noteq> (ValT vt)) | num n \<Rightarrow> (t' = ValT IntT)) \<and> (subsumption P t' t)"
proof (induction "const k" "(t,\<gamma>)" arbitrary:t rule:wf_expr.induct)
  case (wf_expr_const t \<Gamma>)
  then show ?case using subsumption_self by blast
next
  case (wf_expr_sub \<Gamma> t' t)
  then show ?case using subsumption_extend by blast
qed

lemma wf_expr_fieldacci_intro:
  shows "P M \<Gamma> \<turnstile> (fieldacci x f) : (t,\<gamma>) \<Longrightarrow> 
            \<exists>t'. (wf_fieldi_access P \<Gamma> x f (t', \<gamma>)) \<and> (subsumption P t' t)"
proof (induction "fieldacci x f" "(t,\<gamma>)" arbitrary:t rule:wf_expr.induct)
  case (wf_expr_fieldacci \<Gamma>)
  then show ?case using subsumption_self by blast
next
  case (wf_expr_sub \<Gamma> t' t)
  then show ?case using subsumption_extend by blast
qed

lemma wf_expr_fieldaccs_intro:
  shows "P M \<Gamma> \<turnstile> (fieldaccs c f) : (t,\<gamma>) \<Longrightarrow> 
            \<exists>t'. (wf_fields_access P M c f (t', \<gamma>)) \<and> (subsumption P t' t)"
proof (induction "fieldaccs c f" "(t,\<gamma>)" arbitrary:t rule:wf_expr.induct)
  case (wf_expr_fieldaccs \<Gamma>)
  then show ?case using subsumption_self by blast
next
  case (wf_expr_sub \<Gamma> t' t)
  then show ?case using subsumption_extend by blast
qed

lemma wf_expr_wrap_intro:
  shows "P M \<Gamma> \<turnstile> (wrap cbname e) : (t,\<gamma>) \<Longrightarrow> 
            \<exists>t' l.  (P M \<Gamma> \<turnstile> e : (t',l)) \<and> (P \<turnstile> t' <: (IfaceT cbname)) \<and>
                   is_cap P cbname \<and> (\<not>is_cap_type P t' \<longrightarrow> (superinterface_set P cbname) \<subseteq> (msreq M) \<inter> l) \<and>
                         (IfaceT cbname) = t \<and> l \<inter> (cap_label P cbname) = \<gamma>"
proof (induction "wrap cbname e" "(t,\<gamma>)" arbitrary:t  rule:wf_expr.induct)
  case (wf_expr_sub \<Gamma> t' t)
  then have "is_cap_type P t'" by auto
  then show ?case using wf_expr_sub by simp (* by contradiction: subsumption of capabilities not possible. *)
next
  case (wf_expr_wrap \<Gamma> t' l)
  then show ?case using subsumption_self by blast
qed

(* Lemmas for inferring premesis of a conclusion. *)
lemma wf_stmt_assign_intro:
  assumes "P M \<Gamma> \<turnstile> (assign x e) \<bullet>"
  shows "\<exists>t. (\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some t) \<and> (P M \<Gamma> \<turnstile> e : t)"
  using assms wf_stmt.simps[where ?a2.0 = "assign x e"] by simp

lemma wf_stmt_assignfi_intro:
  assumes "P M \<Gamma> \<turnstile> (assignfi x f e) \<bullet>"
  shows "\<exists>T. wf_fieldi_access P \<Gamma> x f T \<and> (P M \<Gamma> \<turnstile> e : T)"
  using assms wf_stmt.simps[where ?a2.0 = "assignfi x f e"] by auto

lemma wf_stmt_assignfs_intro:
  assumes "P M \<Gamma> \<turnstile> (assignfs c f e) \<bullet>"
  shows "\<exists>T. wf_fields_access P M c f T \<and> (P M \<Gamma> \<turnstile> e : T)"
  using assms wf_stmt.simps[where ?a2.0 = "assignfs c f e"] by auto

lemma wf_stmt_expr_intro:
  assumes "P M \<Gamma> \<turnstile> (expr e) \<bullet>"
  shows "\<exists>T. (P M \<Gamma> \<turnstile> e : T)"
  using assms wf_stmt.simps[where ?a2.0 = "expr e"] by auto

lemma wf_stmt_ifelse_intro:
  assumes "P M \<Gamma> \<turnstile> (ifelse x s1 s2) \<bullet>"
  shows "\<exists>l. (\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some ((ValT IntT),l)) \<and> (P M \<Gamma> \<turnstile> s1 \<bullet>) \<and> (P M \<Gamma> \<turnstile> s2 \<bullet>)"
  using assms wf_stmt.simps[where ?a2.0 = "ifelse x s1 s2"] by auto

lemma wf_stmt_letin_intro:
  assumes "P M \<Gamma> \<turnstile> (letin \<T> x e s) \<bullet>"
  shows "(P M \<Gamma>(x := None) \<turnstile> e : \<T>) \<and> (P M \<Gamma>(x\<mapsto>\<T>) \<turnstile> s \<bullet>)"
  using assms wf_stmt.simps[where ?a2.0 = "letin \<T> x e s"] by auto

lemma wf_stmt_return_intro:
  assumes "P M \<Gamma> \<turnstile> (return e) \<bullet>"
  shows "P M \<Gamma> \<turnstile> e : (msreturn M)"
  using assms wf_stmt.simps[where ?a2.0 = "return e"] by auto

lemma wf_stmt_seq_intro:
  assumes "P M \<Gamma> \<turnstile> seq s1 s2 \<bullet>"
  shows "(P M \<Gamma> \<turnstile> s1 \<bullet>) \<and> (P M \<Gamma> \<turnstile> s2 \<bullet>)"
  using assms wf_stmt.simps[where ?a2.0 = "seq s1 s2"] by auto

lemma wf_stmt_throw_intro:
  assumes "P M \<Gamma> \<turnstile> throw e \<bullet>"
  shows "(P M \<Gamma> \<turnstile> e : (ClassT Object,{}))"
  using assms wf_stmt.simps[where ?a2.0 = "throw e"] by auto

lemma wf_stmt_trycatch_intro:
  assumes "P M \<Gamma> \<turnstile> (trycatch s handlers) \<bullet>"
  shows "(P M \<Gamma> \<turnstile> s \<bullet>) \<and> (\<forall>(t,x,s')\<in>(set handlers). (P M \<Gamma>(x\<mapsto>(t,{})) \<turnstile> s' \<bullet>) \<and> \<not>is_cap_type P t)"
  using assms wf_stmt.simps[where ?a2.0 = "trycatch s handlers"] by auto

definition unique_keys :: "('a \<times> 'b) list => bool" where
  "unique_keys \<equiv> distinct \<circ> map fst"

definition wf_label :: "prog \<Rightarrow> label \<Rightarrow> bool"
  where "wf_label p l \<equiv> (\<forall>cb\<in>l. is_interface p cb)" (* and is cap? *)

definition wf_lbltype :: "prog \<Rightarrow> \<T> \<Rightarrow> bool"
  where "wf_lbltype p \<T> \<equiv> is_type p (ttype \<T>) \<and> wf_label p (tlabel \<T>)"

(* Well-formed field declaration *)
definition wf_fdecl :: "prog \<Rightarrow> fdecl \<Rightarrow> bool"
  where "wf_fdecl p fdecl \<equiv> wf_lbltype p (ftype fdecl)"

(* Well-formed method signature *)
definition wf_mdecl :: "prog \<Rightarrow> mdecl \<Rightarrow> bool"
  where "wf_mdecl p m \<equiv> (unique_keys (mpar m)) 
                           \<and> (\<forall>(var,t)\<in>(set (mpar m)). wf_lbltype p t)
                           \<and> wf_lbltype p (mret m)"

(* Definition for the environment against which to type check method bodies *)
(* environment for static method call *)
definition call_lenvs :: "prog \<Rightarrow> mdecl \<Rightarrow> lenv"
  where "call_lenvs p m \<equiv> (map_of (mpar m))"

(* environment for instance method call *)
definition call_lenvi :: "prog \<Rightarrow> cname \<Rightarrow> mdecl \<Rightarrow> lenv"
  where "call_lenvi p c m \<equiv> (call_lenvs p m)(This\<mapsto>(ClassT c, UNIV))"

(* Creates the method environment in which a method is checked *)
definition call_menv :: "cname \<Rightarrow> method \<Rightarrow> msenv"
  where "call_menv cname m \<equiv> \<lparr>mscname = cname, msreturn = mret (mdecl m), msreq = mreq m\<rparr>"

(* Well-formed method *)
definition wf_method :: "prog \<Rightarrow> cdecl \<Rightarrow> method \<Rightarrow> bool"
  where "wf_method p \<equiv> (\<lambda>(cname,c) m. wf_mdecl p (mdecl m)
  \<and> (case mstmt m of None \<Rightarrow> False 
        | Some stmt \<Rightarrow> (mstatic (mdecl m) \<longrightarrow> (p (call_menv cname m) (call_lenvs p (mdecl m)) \<turnstile> stmt \<bullet>)) \<and>
                      (\<not>mstatic (mdecl m) \<longrightarrow> (p (call_menv cname m) (call_lenvi p cname (mdecl m)) \<turnstile> stmt \<bullet>) 
                                                \<and> (mreq m) \<subseteq> (creq c)))
                     \<and> wf_label p (mreq m))"

(* Definition for when two method declarations are compatible *)
definition mdecl_compatible :: "mdecl \<Rightarrow> mdecl \<Rightarrow> bool"
  where "mdecl_compatible m1 m2 \<equiv> (msig (mpar m1) = msig (mpar m2)) \<and> (mstatic m1 = mstatic m2) \<and> (mret m1 = mret m2)"

definition wf_cdecl_extension :: "prog \<Rightarrow> cdecl \<Rightarrow> cname \<Rightarrow> bool"
  where "wf_cdecl_extension p \<equiv> (\<lambda>(cname,c) super. 
          ((\<exists>scl. class p super = Some scl \<and> (creq scl \<subseteq> creq c)) \<and> 
           the (grant p cname) \<subseteq> the (grant p super) \<and> 
          ((super, cname) \<notin> (subclass p)) \<and>
          (\<forall>(mname,meth)\<in>(set (cmethods c)).  \<forall>supermeth d. cmethod p super mname = Some (d,supermeth)
                                                            \<longrightarrow> mdecl_compatible (mdecl supermeth) (mdecl meth)) \<and>
          (\<forall>(fname,ft)\<in>(set (cfields c)). field p super fname = None)))"

definition wf_cdecl_implementation :: "prog \<Rightarrow> cdecl \<Rightarrow> iname \<Rightarrow> bool"
  where "wf_cdecl_implementation p \<equiv> (\<lambda>(cname,c) ifname. 
          is_interface p ifname \<and> (\<forall>mname\<in>dom(imethoddecl p ifname). \<exists>decl. cmethoddecl p cname mname = Some decl \<and>
                                      mdecl_compatible (the (imethoddecl p ifname mname)) decl))"

(* Well-formed class declaration *)
definition wf_cdecl :: "prog \<Rightarrow> cdecl \<Rightarrow> bool" 
  where "wf_cdecl p \<equiv> (\<lambda>(cname,c).     
         (cname \<noteq> Object \<longrightarrow> wf_cdecl_extension p (cname,c) (cextends c)) (* Object can extend object. *)
        \<and> distinct (cimpl c) \<and> (\<forall>cb\<in>set (cimpl c). wf_cdecl_implementation p (cname,c) cb)
        \<and> unique_keys (cmethods c) \<and> (\<forall>(mname,meth)\<in>(set (cmethods c)). wf_method p (cname,c) meth)
        \<and> unique_keys (cfields c)  \<and> (\<forall>(fname,fdecl)\<in>(set (cfields c)). wf_fdecl p fdecl))"

definition wf_ifdecl_extension :: "prog \<Rightarrow> ifdecl \<Rightarrow> iname \<Rightarrow> bool"
  where "wf_ifdecl_extension p \<equiv> (\<lambda>(ifname,i) ifname'. 
               (* Capabilities may only extend other capabilities *)
               (\<exists>i'. interface p ifname' = Some i' \<and> (icap i \<longrightarrow> icap i')) \<and>
                ((ifname', ifname) \<notin> (subinterface p)) \<and> 
              (* We need not only check all of the methods explicitly declared in this interface have
                 the same signature as their superinterfaces, we must ensure that the methods inherited
                 from the superinterfaces do not conflict. *)
                (\<forall>mname\<in>dom(imethoddecl p ifname'). (* implied: imethoddecl p ifname mname \<noteq> None \<and> *)
                         mdecl_compatible (the (imethoddecl p ifname' mname)) (the (imethoddecl p ifname mname))))"

(* Well-formed interface declaration *)
definition wf_ifdecl :: "prog \<Rightarrow> ifdecl \<Rightarrow> bool"
  where "wf_ifdecl p \<equiv> (\<lambda>(ifname,cb). 
                          distinct (iextends cb) \<and> (\<forall>ifname'\<in>set (iextends cb). wf_ifdecl_extension p (ifname,cb) ifname')
                      \<and> unique_keys (imethods cb) \<and> (\<forall>(mname,mdecl)\<in>(set (imethods cb)). wf_mdecl p mdecl)
                    )"

(* Well-formed program part *)
definition wf_prog :: "prog \<Rightarrow> bool"
  where "wf_prog p \<equiv> unique_keys (pinterfaces p) \<and> (\<forall>cb\<in>set (pinterfaces p). wf_ifdecl p cb) \<and>
                     unique_keys (pclasses p) \<and> (\<forall>c\<in>set (pclasses p). wf_cdecl p c) \<and>
                     is_class p (pentryclass p) \<and> 
                     (\<exists>d m. cmethod p (pentryclass p) (pentrymethod p) = Some (d,m) \<and> mstatic (mdecl m))" (* todo: allow entry point to have a 'requires' clause... *)

(* Lemmas for making inferences using wf_prog p. *)
lemma prog_wf_cdecl:
  assumes prog_wf: "wf_prog p"
  assumes class_exist: "class p cname = Some cl"
  shows "wf_cdecl p (cname,cl)"
  using assms unfolding wf_prog_def class_def by (simp add: map_of_SomeD)

lemma prog_wf_cdecl_extension:
  assumes prog_wf: "wf_prog p"
  assumes class_exist: "class p cname = Some cl"
  assumes class_not_object: "cname \<noteq> Object"
  assumes class_extend: "cextends cl = cext"
  shows "wf_cdecl_extension p (cname,cl) cext"
proof -
  have "wf_cdecl p (cname,cl)" using assms prog_wf_cdecl by simp
  then show ?thesis unfolding wf_cdecl_def using class_extend class_not_object by simp
qed

lemma prog_wf_cdecl_implementation:
  assumes prog_wf: "wf_prog p"
  assumes class_exist: "class p cname = Some cl"
  assumes class_impl: "cb \<in> set (cimpl cl)"
  shows "wf_cdecl_implementation p (cname,cl) cb"
proof -
  have "wf_cdecl p (cname,cl)" using assms prog_wf_cdecl by simp
  then show ?thesis unfolding wf_cdecl_def using class_impl by simp
qed

lemma prog_wf_ifdecl:
  assumes prog_wf: "wf_prog p"
  assumes class_exist: "interface p ifname = Some cb"
  shows "wf_ifdecl p (ifname,cb)"
  using assms unfolding wf_prog_def interface_def by (simp add: map_of_SomeD)

lemma prog_wf_ifdecl_implementation:
  assumes prog_wf: "wf_prog p"
  assumes class_exist: "interface p ifname = Some cb"
  assumes class_extend: "cb' \<in> set (iextends cb)"
  shows "wf_ifdecl_extension p (ifname,cb) cb'"
proof -
  have "wf_ifdecl p (ifname,cb)" using assms prog_wf_ifdecl by simp
  then show ?thesis unfolding wf_ifdecl_def using class_extend by simp
qed

(* Lemmas for reasoning about subtyping relationships, including field and method inheritance. *)
lemma direct_subclass_irrefl_trancl:
  assumes prog_wf: "wf_prog p"
  assumes "(c,s) \<in> (direct_subclass p)"
  shows "(s,c) \<notin> (direct_subclass p)\<^sup>*" 
proof -
  obtain cl where a1: "class p c = Some cl \<and> cextends cl = s \<and> c \<noteq> Object"
    using assms unfolding direct_subclass_def by blast
  then have "wf_cdecl p (c,cl)" using prog_wf_cdecl prog_wf by simp
  then show ?thesis using a1 unfolding wf_cdecl_def wf_cdecl_extension_def by simp
qed

lemma direct_subinterface_irrefl_trancl:
  assumes prog_wf: "wf_prog p"
  assumes "(c,s) \<in> (direct_subinterface p)"
  shows "(s,c) \<notin> (direct_subinterface p)\<^sup>*"
proof -
  obtain cb where a1: "interface p c = Some cb \<and> s \<in> set (iextends cb)"
    using assms unfolding direct_subinterface_def by blast
  then have "wf_ifdecl p (c,cb)" using prog_wf_ifdecl prog_wf by simp
  then show ?thesis using a1 unfolding wf_ifdecl_def wf_ifdecl_extension_def by simp
qed

lemma wf_direct_subclass:
  assumes prog_wf: "wf_prog p"
  shows "wf ((direct_subclass p)\<inverse>)"
proof -       
  define A where "A \<equiv> {c. is_class p c}"
  define B where "B \<equiv> (\<lambda>c. {s.  cextends (the (class p c)) = s \<and> c \<noteq> Object })"
  have "direct_subclass p = Sigma A B"
    unfolding Sigma_def direct_subclass_def is_class_def A_def B_def by auto
  moreover have "finite A"
    unfolding is_class_def class_def A_def by (metis dom_def finite_dom_map_of) 
  moreover have "\<forall>a. finite (B a)"
    unfolding B_def using not_finite_existsD by fastforce
  ultimately have "finite (direct_subclass p)"
    using finite_SigmaI by simp
  moreover have "acyclic (direct_subclass p)"
    unfolding acyclic_def by (meson direct_subclass_irrefl_trancl prog_wf tranclD2)
  ultimately show ?thesis 
  (* We can actually show both wf ((direct_subclass p)\<inverse>) and wf (direct_subclass p) *)
    using finite_acyclic_wf finite_converse acyclic_converse by metis
qed

lemma wf_direct_subinterface:
  assumes prog_wf: "wf_prog p"
  shows "wf ((direct_subinterface p)\<inverse>)"
proof -
  define A where "A \<equiv> {c. is_interface p c}"
  define B where "B \<equiv> (\<lambda>c. {s. s \<in> set (iextends (the (interface p c))) })"
  have "direct_subinterface p = Sigma A B"
    unfolding Sigma_def direct_subinterface_def is_interface_def A_def B_def by auto
  moreover have "finite A"
    unfolding is_interface_def interface_def A_def by (metis dom_def finite_dom_map_of)
  moreover have "\<forall>a. finite (B a)"
    unfolding B_def using not_finite_existsD by fastforce
  ultimately have "finite (direct_subinterface p)"
    using finite_SigmaI by simp
  moreover have "acyclic (direct_subinterface p)"
    unfolding acyclic_def by (meson direct_subinterface_irrefl_trancl prog_wf tranclD2)
  ultimately show ?thesis
    using finite_acyclic_wf finite_converse acyclic_converse by metis
qed

lemma field_subclass:
  assumes wf: "wf_prog P"
  shows "(t1, t0) \<in> (direct_subclass P)\<^sup>* \<Longrightarrow> field P t0 f = Some t \<Longrightarrow> field P t1 f = Some t"
proof (induction rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case a1: (step y z)
  then obtain yCl where a2: "y \<noteq> Object \<and> class P y = Some yCl \<and> cextends yCl = z" 
    using direct_subclass_def by auto
  assume a3: "field P z f = Some t"
  have "wf ((direct_subclass P)\<inverse>)" 
    using wf_direct_subclass wf by simp
  then have "field P y f = ((field P z) ++ map_of (cfields yCl)) f"
    using wf field_unfold a2 by simp
  also have "... = Some t"
  (* was this field defined in y, the subclass of z?*)
  proof (cases "f \<in> dom(map_of (cfields yCl))")
    (* prove that field redefinition was not possible, due to constraints in wf_prog *)
    case b1: True
    have "wf_cdecl_extension P (y, yCl) z" 
      using a2 wf prog_wf_cdecl_extension by simp
    then have "\<forall>(fname,ft)\<in>(set (cfields yCl)). field P z fname = None" 
      unfolding wf_cdecl_extension_def by blast
    then have "field P z f = None" 
      using b1 unfolding dom_def using map_of_SomeD by fastforce
    then show ?thesis using a3 by simp 
  next
    case False
    then show ?thesis using a3 unfolding dom_def
      by (simp add: map_add_Some_iff)
  qed
  finally have "field P y f = Some t" by simp
  then show ?thesis using a1 by simp
qed

lemma field_subtype:
  assumes wf: "wf_prog P"
  assumes subtype: "P \<turnstile> (ClassT t1) <: (ClassT t0)"
  assumes superfield: "field P t0 fname = Some f"
  shows "field P t1 fname = Some f"
proof -
  have "P \<turnstile> (ClassT t1) <: (ClassT t0)" using subtype by simp
  then have "wf_prog P \<Longrightarrow> field P t0 fname = Some f \<Longrightarrow> field P t1 fname = Some f"
  proof (induction "ClassT t1" "ClassT t0" arbitrary: t0 t1)
    case (subtype_self)
    then show ?case by simp
  next
    case (subtype_cextend c1)
    then show ?case using field_subclass unfolding direct_subclass_def by blast
  next
    case (subtype_trans t2)
    then show ?case using subtype_derived_class by blast
  qed
  then show ?thesis using wf superfield by simp
qed

lemma mdecl_compatible_reflexive:
  shows "mdecl_compatible md md"
  using mdecl_compatible_def by simp

lemma cmethod_subclass:
  assumes wf: "wf_prog P"
  shows "(c, s) \<in> (subclass P) \<Longrightarrow> cmethoddecl P s m = Some md \<Longrightarrow> (\<exists>md'. cmethoddecl P c m = Some md' \<and> mdecl_compatible md md')"
proof (induction s arbitrary: md rule: rtrancl_induct)
  case base
  then show ?case 
    using mdecl_compatible_reflexive by simp
next
  case a1: (step c s) (* c: class name, s: superclass name *)
  then obtain cCl where a2: "c \<noteq> Object \<and> class P c = Some cCl \<and> cextends cCl = s" 
    using direct_subclass_def by auto
  have "cmethoddecl P s m = Some md" using a1 by simp
  then obtain sCl meth where a4: "cmethod P s m = Some (sCl,meth) \<and> (mdecl meth) = md" 
    unfolding cmethoddecl_def by (metis (mono_tags) case_prod_conv map_comp_Some_iff old.prod.exhaust option.sel) 
  
  have "wf ((direct_subclass P)\<inverse>)" 
    using wf_direct_subclass wf by simp
  then have "cmethod P c m = ((cmethod P s) ++ cdeclmethods (c,cCl)) m" 
    using wf cmethod_unfold a2 by simp
  moreover have "\<exists>c' meth'. ((cmethod P s) ++ cdeclmethods (c,cCl)) m = Some (c',meth') \<and> mdecl_compatible md (mdecl meth')"
  proof (cases "m \<in> dom(cdeclmethods (c,cCl))")  (* was this method defined in y, the subclass of z?*)
    case b1: True
    then obtain c' meth' where b2: "cdeclmethods (c,cCl) m = Some (c',meth')"
      unfolding dom_def using b1 map_of_SomeD by fastforce 
    (* Show the method defined in y-class is the one that is returned by (cmethod P y m).*)
    then have b3: "((cmethod P s) ++ cdeclmethods (c,cCl)) m = Some (c',meth')"
      unfolding map_add_def by simp
    have b4: "(map_of (cmethods cCl)) m = Some meth'" using b2 unfolding cdeclmethods_def
      by (simp add: map_comp_Some_iff)

    (* Show that the signature of this method is the same as the method in z, because of
       class-extension constraints. *)
    have "wf_cdecl_extension P (c,cCl) s" using a2 wf prog_wf_cdecl_extension by simp
    then have "(\<forall>(mname,meth)\<in>(set (cmethods cCl)).  \<forall>supermeth d. cmethod P s mname = Some (d,supermeth)
                                                            \<longrightarrow> mdecl_compatible (mdecl supermeth) (mdecl meth))"
      unfolding wf_cdecl_extension_def by blast
    moreover have "(m,meth')\<in>(set (cmethods cCl))" 
      using b4 map_of_SomeD by fastforce    
    ultimately have "mdecl_compatible md (mdecl meth')"
      using a4 by blast
    then show ?thesis using b3 by simp
  next
    (* the field came from class z *)
    case False    
    then show ?thesis using a4 unfolding dom_def
      by (simp add: False map_add_dom_app_simps mdecl_compatible_def)
  qed
  ultimately have "\<exists>c' meth'. cmethod P c m = Some (c',meth') \<and> mdecl_compatible md (mdecl meth')" 
    by simp
  then have "\<exists>md'. cmethoddecl P c m = Some md' \<and> mdecl_compatible md md'"
    using cmethoddecl_def by auto
  then show ?case using a1
    using mdecl_compatible_def by fastforce 
qed

lemma imethoddecl_subinterface:
  assumes wf: "wf_prog P"
  shows "(c, s) \<in> (direct_subinterface P)\<^sup>* \<Longrightarrow> imethoddecl P s m = Some md \<Longrightarrow> \<exists>md'. imethoddecl P c m = Some md' \<and> mdecl_compatible md md'"
proof (induction arbitrary: md rule: rtrancl_induct)
  case base
  then show ?case
    using mdecl_compatible_reflexive by simp
next
  case a1: (step c s)
  then obtain cCb where a2: "interface P c = Some cCb \<and> s \<in> set (iextends cCb)" 
    using direct_subinterface_def by blast
  (* Show method signatures in c and s must be compatible. *)
  then have "wf_ifdecl_extension P (c, cCb) s" using wf prog_wf_ifdecl_implementation by simp
  then have a3: "mdecl_compatible md (the (imethoddecl P c m))"
    unfolding wf_ifdecl_extension_def using a1 by force

  (* Prove m \<in> dom(imethoddecl P c) given m \<in> dom(imethoddecl P s) and c extends z. *)
  have "m \<in> dom(imethoddecl P s) \<and> (imethoddecl P s) \<in> set (map (\<lambda>super. imethoddecl P super) (iextends cCb))"
    using a1 a2 by auto
  then have "m \<in> dom(map_adds (map (\<lambda>super. imethoddecl P super) (iextends cCb)))"
    using map_adds_domain by metis
  moreover have "imethoddecl P c = (map_adds (map (\<lambda>super. imethoddecl P super) (iextends cCb)) ++ map_of (imethods cCb))"
    using imethoddecl_unfold wf_direct_subinterface a1 a2 wf by simp
  ultimately have a4: "m \<in> dom(imethoddecl P c)" by simp

  show ?case using a1 a3 a4
    by (simp add: domD mdecl_compatible_def) 
qed

lemma cmethod_subinterface:
  assumes wf: "wf_prog P"
  assumes "class P c = Some cl"
  assumes "s \<in> set (cimpl cl)"
  shows "imethoddecl P s m = Some md \<Longrightarrow> \<exists>md'. cmethoddecl P c m = Some md' \<and> mdecl_compatible md md'"
proof -
  assume a1: "imethoddecl P s m = Some md"
  have "wf_cdecl_implementation P (c,cl) s" using wf assms prog_wf_cdecl_implementation by simp
  then have "(\<forall>mname\<in>dom (imethoddecl P s). \<exists>decl. cmethoddecl P c mname = Some decl \<and> mdecl_compatible (the (imethoddecl P s mname)) decl)"
    unfolding wf_cdecl_implementation_def by simp
  then have "\<exists>md'. cmethoddecl P c m = Some md' \<and> mdecl_compatible md md'"
    using a1 by fastforce
  then show ?thesis .
qed

lemma methoddecl_subtype:
  assumes wf: "wf_prog P"
  assumes subtype: "P \<turnstile> c <: s"
  assumes supersig: "methoddecl P s mname = Some md"
  shows "\<exists>md'. methoddecl P c mname = Some md' \<and> mdecl_compatible md md'"
proof -
  have "P \<turnstile> c <: s" using subtype by simp
  then have "wf_prog P \<Longrightarrow> methoddecl P s mname = Some md \<Longrightarrow> \<exists>md'. methoddecl P c mname = Some md' \<and> mdecl_compatible md md'"
  proof (induction c s arbitrary: md)
    case (subtype_self t)
    then show ?case using mdecl_compatible_reflexive by simp
  next
    case a1: (subtype_cextend c cCl s)
    then have "(c,s) \<in> (subclass P)" unfolding direct_subclass_def by auto
    then show ?case using a1 cmethod_subclass methoddecl_def by simp
  next
    case (subtype_cimpl c cCl cb)
    then show ?case using cmethod_subinterface methoddecl_def by simp
  next
    case a1: (subtype_iextend c cCb s)
    then have "(c,s) \<in> (subinterface P)" unfolding direct_subinterface_def by auto
    then show ?case using a1 imethoddecl_subinterface methoddecl_def by simp 
  next
    case (subtype_trans t1 t2 t3)
    then show ?case using mdecl_compatible_def by fastforce
  qed
  then show ?thesis using wf supersig by simp
qed

lemma direct_subclass_maintains_exists:
  assumes "wf_prog p"
  assumes "(c,d)\<in>(direct_subclass p)"
  assumes "is_class p c"
  shows "is_class p d"
proof -
  obtain cCl where "class p c = Some cCl \<and> cextends cCl = d \<and> c \<noteq> Object"
    using assms unfolding direct_subclass_def by blast
  then have  "wf_cdecl_extension p (c,cCl) d" using prog_wf_cdecl_extension assms by simp
  then have "is_class p d" using is_class_def unfolding wf_cdecl_extension_def by blast
  then show ?thesis .
qed

lemma class_extends_exists:
  assumes "wf_prog p"
  assumes "is_class p c"
  assumes "(c,d)\<in>(subclass p)"
  shows "is_class p d"
  using direct_subclass_maintains_exists 
proof -
  have "(c,d)\<in>(direct_subclass p)\<^sup>*" using assms by simp
  then have "wf_prog p \<Longrightarrow> is_class p c \<Longrightarrow> is_class p d"
  proof (induction rule:rtrancl_induct)
    case base
    then show ?case by simp
  next
    case (step y z)
    then show ?case using direct_subclass_maintains_exists by simp
  qed
  then show ?thesis using assms by simp
qed

lemma class_extends_object:
  assumes "wf_prog p"
  assumes "is_class p c"
  shows "(c,Object)\<in>(subclass p)"
proof -
  have "wf ((direct_subclass p)\<inverse>)" using assms wf_direct_subclass by simp
  then have "wf_prog p \<Longrightarrow> is_class p c \<Longrightarrow> (Object,c)\<in>((direct_subclass p)\<inverse>)\<^sup>*"
  proof (induction c) (*  arbitrary:c *)
    case a1: (less x)
    then obtain xCl y where a2: "class p x = Some xCl \<and> y = (cextends xCl)" 
      unfolding is_class_def by blast
    then show ?case proof (cases "x = Object")
      case True
      then show ?thesis using a1 by simp
    next
      case a3: False (* x*)
      then have "wf_cdecl_extension p (x,xCl) y" using prog_wf_cdecl_extension a1 a2 a3 by simp
      then have "is_class p y" using is_class_def unfolding wf_cdecl_extension_def by blast
      moreover have a4: "(y,x) \<in> (direct_subclass p)\<inverse>" unfolding direct_subclass_def using a1 a2 a3 by simp
      ultimately have "(Object,y) \<in> ((direct_subclass p)\<inverse>)\<^sup>*" using a1 by simp
      then show ?thesis using a4 by (meson rtrancl_into_rtrancl) 
    qed
  qed  
  then show ?thesis using assms
    by (simp add: rtrancl_converse)
qed

lemma prog_wf_object_exists:
  assumes "wf_prog p"
  assumes "is_class p c"
  shows "is_class p Object"
  using assms class_extends_object class_extends_exists by simp

theorem subclass_induction [consumes 1, case_names base step]:
  assumes prereq: "wf_prog p \<and> is_class p c"
  assumes base_p: "\<And>cl. \<lbrakk> class p Object = Some cl \<rbrakk> \<Longrightarrow> P Object"
  assumes step_p: "\<And>c d cl. \<lbrakk> c \<noteq> Object; class p c = Some cl; cextends cl = d; P d \<rbrakk> \<Longrightarrow> P c"
  shows "P c"
proof -
  have a1: "(Object,c)\<in>((direct_subclass p)\<inverse>)\<^sup>*" using class_extends_object assms 
    by (simp add: rtrancl_converse)
  then have "is_class p Object" using prereq prog_wf_object_exists by metis
  then obtain oCl where a2: "class p Object = Some oCl" unfolding is_class_def by blast

  have "\<lbrakk> wf_prog p; is_class p c; \<And>cl. \<lbrakk> class p Object = Some cl \<rbrakk> \<Longrightarrow> P Object; 
                                   \<And>c d cl. \<lbrakk> c \<noteq> Object; class p c = Some cl; cextends cl = d; P d \<rbrakk> \<Longrightarrow> P c \<rbrakk> \<Longrightarrow> P c" 
    using a1
  proof (induction)
    case (base)
    then show ?case using a2 unfolding direct_subclass_def by auto
  next
    case b2: (step y z)
    then show ?case 
    proof (cases z)
      case Object
      then show ?thesis using a2 b2 by simp 
    next
      case b3: (ClassName x2)
      then obtain zCl where b4: "class p z = Some zCl \<and> cextends zCl = y" using b2 unfolding direct_subclass_def by auto
      then have "wf_cdecl_extension p (z,zCl) y" using prog_wf_cdecl_extension b2 b3 by simp
      then have "is_class p y" using is_class_def unfolding wf_cdecl_extension_def by blast
      then have "P y" using b2 by simp
      then show ?thesis using b2 b3 b4 by simp
    qed
  qed
  then show ?thesis using assms by simp
qed

lemma method_declaring_class:
  assumes wf: "wf_prog P"
  assumes "is_class P c"
  assumes "cmethod P c mname = Some (d,m)"
  shows "(c,d)\<in>(subclass P) \<and> (\<exists>cl. class P d = Some cl \<and> (map_of (cmethods cl)) mname = Some m)"
proof -
  have a1: "wf_prog P \<and> is_class P c" using assms by simp
  then have "cmethod P c mname = Some (d,m) \<Longrightarrow> (c,d)\<in>(subclass P) \<and> 
                                                   (\<exists>cl. class P d = Some cl \<and> 
                                                     (map_of (cmethods cl)) mname = Some m)"
  proof (induction rule: subclass_induction)
    case b1: (base cl)
    then have b2: "cmethod P Object = cdeclmethods (Object,cl)"
      using cmethod_unfold wf_direct_subclass a1 by simp
    then have "(map_of (cmethods cl)) mname = Some m"
      using b1 unfolding cdeclmethods_def by (simp add: map_comp_Some_iff)
    then have "(Object,Object)\<in>(subclass P) \<and> class P Object = Some cl \<and> (map_of (cmethods cl)) mname = Some m"
      using b1 by simp
    moreover have "d = Object" using b1 b2 unfolding cdeclmethods_def by (simp add: map_comp_Some_iff)
    ultimately show ?case by blast
  next
    case b1: (step c s cl)
    then have b2: "(c,s) \<in> subclass P" using direct_subclass_def by auto
    show ?case
    proof (cases "cmethod P s mname = Some (d,m)")
      case True (* method implementation m was inherited from subclass d *)
      then obtain cl' where c1: "(s, d) \<in> subclass P \<and> class P d = Some cl' \<and> map_of (cmethods cl') mname = Some m" using b1 by blast
      moreover have "(c, d) \<in> subclass P" using c1 b2 by auto
      ultimately show ?thesis by blast
    next
      case b2: False
      have "cmethod P c = cmethod P s ++ cdeclmethods (c,cl)"
        using cmethod_unfold wf_direct_subclass a1 b1 by simp
      then have b3: "cdeclmethods (c,cl) mname = Some (d,m)" 
        using b1 b2 by (simp add: map_add_Some_iff)
      then have "map_of (cmethods cl) mname = Some m" 
        unfolding cdeclmethods_def by (simp add: map_comp_Some_iff) 
      moreover have "c = d" 
        using b3 unfolding cdeclmethods_def by (simp add: map_comp_Some_iff) 
      ultimately have "(c, d) \<in> subclass P \<and> class P d = Some cl \<and> map_of (cmethods cl) mname = Some m"
        using b1 by simp
      then show ?thesis by blast 
    qed
  qed
  then show ?thesis using assms by simp
qed

lemma subclass_creq: 
  assumes wf: "wf_prog P"
  assumes cls: "is_class P c"
  assumes "(c,d)\<in>(subclass P)"
  shows "(\<exists>cl dcl. class P c = Some cl \<and> class P d = Some dcl \<and> (creq dcl \<subseteq> creq cl))"
proof -
  have "(c,d)\<in>(subclass P)" using assms by simp
  then have "wf_prog P \<and> is_class P c \<Longrightarrow> (\<exists>cl dcl. class P c = Some cl \<and> class P d = Some dcl \<and> (creq dcl \<subseteq> creq cl))"
  proof (induction c d)
    case (rtrancl_refl a)
    then obtain cl where "class P a = Some cl"
      using cls unfolding is_class_def by auto
    then show ?case by simp
  next
    case a1: (rtrancl_into_rtrancl a b c)
    then obtain aCl bCl where a2: "class P a = Some aCl \<and> class P b = Some bCl \<and> creq bCl \<subseteq> creq aCl"
      unfolding is_class_def by auto
    then obtain cCl where a3: "class P c = Some cCl"
      using a1 direct_subclass_maintains_exists is_class_def by blast
    have "wf_cdecl P (b,bCl) \<and> b \<noteq> Object \<and> cextends bCl = c" 
      using a1 a2 prog_wf_cdecl unfolding direct_subclass_def by simp
    then have "(creq cCl \<subseteq> creq bCl)"
      using a3 unfolding wf_cdecl_def wf_cdecl_extension_def by auto
    then show ?case using a2 a3 by auto
  qed
  then show ?thesis using assms by simp
qed

lemma method_declaring_class_subtype:
  assumes wf: "wf_prog P"
  assumes "is_class P c"
  assumes "cmethod P c mname = Some (d,m)"
  shows "P \<turnstile> (ClassT c) <: (ClassT d)"
  using method_declaring_class assms subclass_subtype by blast

lemma prog_wf_method:
  assumes wf: "wf_prog P"
  assumes is_class: "is_class P c"
  assumes method: "cmethod P c mname = Some (d,m)"
  shows "\<exists>cl. class P d = Some cl \<and> wf_method P (d,cl) m"
proof -
  obtain cl where a1: "(c,d)\<in>(subclass P) \<and> class P d = Some cl \<and> (map_of (cmethods cl)) mname = Some m"
    using method_declaring_class wf is_class method by blast
  then have a2: "(mname,m) \<in> (set (cmethods cl))" 
    by (simp add: map_of_SomeD)
  moreover have "wf_cdecl P (d,cl)" 
    using prog_wf_cdecl wf a1 by metis
  ultimately show ?thesis 
    unfolding wf_cdecl_def using a1 by blast
qed

lemma prog_wf_mstmt_exists: 
  assumes wf: "wf_prog P"
  assumes is_class: "is_class P c"
  assumes method: "cmethod P c mname = Some (d,m)"
  shows stmt: "mstmt m \<noteq> None"
proof -
  obtain c' cl where a1: "(c,c')\<in>(subclass P) \<and> class P c' = Some cl \<and> (map_of (cmethods cl)) mname = Some m"
    using method_declaring_class wf is_class method by blast
  then have a2: "(mname,m) \<in> (set (cmethods cl))" 
    by (simp add: map_of_SomeD)
  moreover have "wf_cdecl P (c',cl)"
    using prog_wf_cdecl wf a1 by simp
  ultimately have "wf_method P (c',cl) m" 
    unfolding wf_cdecl_def by blast
  then show ?thesis 
    unfolding wf_method_def using option.simps(4) by fastforce 
qed

(* The supertype of a capability must be a capability *)
lemma supertype_is_cap_type:
  assumes wfp: "wf_prog P"                       
  shows "P \<turnstile> t' <: t \<Longrightarrow> is_cap_type P t' \<Longrightarrow> is_cap_type P t"
proof  (induction "t'" "t" rule:subtype.induct)
  case (subtype_self t)
  then show ?case by simp
next
  case (subtype_cextend t1 c1 t2)
  then show ?case by simp (* premises are false; no class can be a captype *)
next
  case (subtype_cimpl t1 c1 t2)
  then show ?case by simp (* premises are false; no class can be a captype *)
next
  case a1: (subtype_iextend t1 i1 t2)
  then have "wf_ifdecl P (t1,i1)"
    using prog_wf_ifdecl wfp by simp
  then have "wf_ifdecl_extension P (t1,i1) t2"
    unfolding wf_ifdecl_def using a1 by blast
  then obtain i2 where "interface P t2 = Some i2 \<and> (icap i1 \<longrightarrow> icap i2)"
    unfolding wf_ifdecl_extension_def by blast
  moreover have "icap i1"
    using a1 is_cap_def by simp
  ultimately show ?case using is_cap_def by simp
next
  case (subtype_trans t1 t2 t3)
  then show ?case by simp
qed

(* The subtype of a non-capability must be a non-capability type *)
lemma subtype_is_not_cap_type:
  assumes wfp: "wf_prog P"
  shows "P \<turnstile> t' <: t \<Longrightarrow> \<not>is_cap_type P t \<Longrightarrow> \<not>is_cap_type P t'"
  using assms supertype_is_cap_type by blast


(* superinterface_set is monotonically increasing over the subtyping relation *)
lemma superinterface_set_subtype_mono:
  assumes wfp: "wf_prog P"
  shows "P \<turnstile> (IfaceT t') <: i \<Longrightarrow> \<exists>t. i = (IfaceT t) \<and> superinterface_set P t \<subseteq> superinterface_set P t'"
proof (induction "(IfaceT t')" "i" arbitrary: t' rule:subtype.induct)
  case subtype_self
  then show ?case by simp
next
  case (subtype_iextend t1 i1 t2)
  then have "(t1, t2) \<in> (direct_subinterface P)"
    using subtype_iextend unfolding direct_subinterface_def by simp
  then show ?case unfolding superinterface_set_def by auto
next
  case (subtype_trans t2 t3)
  then show ?case by blast
qed

(* cap_label is monotonically increasing over the subtyping relation *)
lemma cap_label_subtype_mono:
  assumes wfp: "wf_prog P"
  shows "P \<turnstile> (IfaceT t') <: i \<Longrightarrow> \<exists>t. i = (IfaceT t) \<and> cap_label P t \<subseteq> cap_label P t'"
proof (induction "(IfaceT t')" "i" arbitrary: t' rule:subtype.induct)
  case subtype_self
  then show ?case by simp
next
  case (subtype_iextend t1 i1 t2)
  define t1methods where "t1methods \<equiv> imethoddecl P t1"
  define t2methods where "t2methods \<equiv> imethoddecl P t2"
  have a1: "(t1, t2) \<in> (direct_subinterface P)"
    using subtype_iextend unfolding direct_subinterface_def by simp
  
  have "\<forall>m\<in>dom(t2methods). m\<in>dom(t1methods) \<and> (sum_method_labels (the (t1methods m)) = sum_method_labels (the (t2methods m)))"
  proof 
    fix m
    assume b2: "m \<in> dom(t2methods)" 
    then obtain md2 where b3: "t2methods m = Some md2"
      by auto
    then obtain md1 where b4: "t1methods m = Some md1 \<and> mdecl_compatible md2 md1"
      using a1 imethoddecl_subinterface wfp unfolding t2methods_def t1methods_def by blast
    then have "sum_method_labels md1 = sum_method_labels md2"
      unfolding sum_method_labels_def mdecl_compatible_def by simp
    then show "m\<in>dom(t1methods) \<and> (sum_method_labels (the (t1methods m)) = sum_method_labels (the (t2methods m)))"
      using b3 b4 by auto
  qed
  moreover have "superinterface_set P t2 \<subseteq> superinterface_set P t1"
    using a1 unfolding superinterface_set_def by auto
  ultimately have "cap_label P t2 \<subseteq> cap_label P t1"
    unfolding t1methods_def t2methods_def cap_label_def
    by (metis (no_types, lifting) SUP_mono order_refl sup_mono)
  then show ?case by simp
next
  case (subtype_trans t2 t3)
  then show ?case by blast
qed

lemma grant_subclass_mono:
  assumes wfp: "wf_prog P"
  shows "(c,d) \<in> (subclass P) \<Longrightarrow> the (grant P c) \<subseteq> the (grant P d)"
proof (induction rule:rtrancl_induct)
case base
  then show ?case by simp
next
  case (step y z)
  then obtain yCl where "y \<noteq> Object \<and> class P y = Some yCl \<and> cextends yCl = z"
    unfolding direct_subclass_def by auto
  then have "wf_cdecl_extension P (y,yCl) z"
    using prog_wf_cdecl_extension wfp by simp
  then have "the (grant P y) \<subseteq> the (grant P z)"
    unfolding wf_cdecl_extension_def by simp
  then show ?case using step by auto
qed

end