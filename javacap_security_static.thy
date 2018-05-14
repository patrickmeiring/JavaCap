theory javacap_security_static
imports
  Main
  javacap_syntax
  javacap_auxiliary
  javacap_static
  javacap_runtime_representation
  javacap_operational
begin   

inductive allowed_transition :: "prog \<Rightarrow> label \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" ("_ _ \<turnstile> \<langle>_\<rangle> \<rightarrow>\<^sub>A \<langle>_\<rangle>" 50)
  for P :: "prog"
  where 
    at_reflexive: "P \<gamma> \<turnstile> \<langle>S\<rangle> \<rightarrow>\<^sub>A \<langle>S\<rangle>" |
    at_trans: "\<lbrakk> P \<gamma> \<turnstile> \<langle>S\<rangle> \<rightarrow>\<^sub>A \<langle>S1\<rangle>; P \<gamma> \<turnstile> \<langle>S1\<rangle> \<rightarrow>\<^sub>A \<langle>S2\<rangle>  \<rbrakk> \<Longrightarrow> P \<gamma> \<turnstile> \<langle>S\<rangle> \<rightarrow>\<^sub>A \<langle>S2\<rangle>" |
    at_cap_call: "\<lbrakk>  (* any state change by a type-correct call to a capability of a type in \<gamma>
                        is allowed *)
                      P M \<Gamma> \<^bold>\<turnstile> S; P M \<Gamma> \<turnstile> (calli x mname args) : T; P \<turnstile> \<langle>(calli x mname args) | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S'\<rangle>;
                       \<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some (tcap,\<gamma>cap); tcap = IfaceT cbname; is_cap P cbname; cbname \<in> \<gamma> \<rbrakk> \<Longrightarrow> P \<gamma> \<turnstile> \<langle>S\<rangle> \<rightarrow>\<^sub>A \<langle>S'\<rangle>" |    
    at_stack_update: "\<lbrakk> (* no restrictions on stack updates beyond standard type-correctness 
                           and integrity of labels *) 
                          S' = S\<lparr>stack := s'\<rparr> \<rbrakk> \<Longrightarrow> P \<gamma> \<turnstile> \<langle>S\<rangle> \<rightarrow>\<^sub>A \<langle>S'\<rangle>"  |
    at_except_update: "\<lbrakk> (* no restrictions on exception raising beyond standard type-correctness 
                           and integrity of labels *) 
                          S' = S\<lparr>except := e'\<rparr> \<rbrakk> \<Longrightarrow> P \<gamma> \<turnstile> \<langle>S\<rangle> \<rightarrow>\<^sub>A \<langle>S'\<rangle>"  |
    at_retval_update: "\<lbrakk> (* no restrictions on returning beyond standard type-correctness 
                           and integrity of labels *) 
                          S' = S\<lparr>retval := r'\<rparr> \<rbrakk> \<Longrightarrow> P \<gamma> \<turnstile> \<langle>S\<rangle> \<rightarrow>\<^sub>A \<langle>S'\<rangle>"  |
    at_heap_update: "\<lbrakk> (* the new object must have a label less than gamma
                          N.B. heap extension property of preservation proof already guarantees that 
                               if we are updating an existing object, the updated object will have
                               the same label as the original label  *)
                          (HLabel obj') \<subseteq> \<gamma>; 
                          S' = S\<lparr>heap := (heap S)(l\<mapsto>obj')\<rparr>
                       \<rbrakk> \<Longrightarrow> P \<gamma> \<turnstile> \<langle>S\<rangle> \<rightarrow>\<^sub>A \<langle>S'\<rangle>" |
    at_globals_update: "\<lbrakk> is_class P c; field P c f = Some fdecl; tlabel (ftype fdecl) \<subseteq> \<gamma>;
                          classStatics = the ((globals S) c);
                          S' = S\<lparr>globals := (globals S)(c\<mapsto>(classStatics(f\<mapsto>v)))\<rparr> 
                       \<rbrakk> \<Longrightarrow> P \<gamma> \<turnstile> \<langle>S\<rangle> \<rightarrow>\<^sub>A \<langle>S'\<rangle>" |
    at_privs_update: "\<lbrakk> (* We don't really need to show this is true, but provides 
                          some confidence. *)
                         S' = S\<lparr>privs:= \<gamma>'\<rparr>; \<gamma>' \<subseteq> \<gamma> \<rbrakk> \<Longrightarrow> P \<gamma> \<turnstile> \<langle>S\<rangle> \<rightarrow>\<^sub>A \<langle>S'\<rangle>"

lemma allowed_transition_expr_new:
  assumes op1: "v = href l"
  assumes op2: "l \<notin> dom (heap S)"
  assumes op3: "S' = S\<lparr>heap := (heap S)(l \<mapsto> new_object P cname (lbl \<inter> privs S))\<rparr>"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wf: "P M \<Gamma> \<turnstile> new lbl cname : T"
  assumes wfp: "wf_prog P"
  assumes gamma: "(privs S) \<subseteq> \<gamma>"
  shows "allowed_transition P \<gamma> S S'"
proof -
  (* presently unused *)
  have "(P M \<Gamma> \<^bold>\<turnstile> S') \<and> (transition_ok S S') \<and> (is_expr_value_ok P S' T v)"
    using preservation_expr_new assms by simp

  have "HLabel (new_object P cname (lbl \<inter> privs S)) \<subseteq> \<gamma>"
    using gamma unfolding new_object_def by auto
  then show "allowed_transition P \<gamma> S S'"
    using op3 at_heap_update by simp
qed

lemma allowed_transition_expr_calli:
  assumes op1: "a = the (stack S x)"
  assumes op2: "l = the_href a"
  assumes op3: "a \<noteq> v.null"
  assumes op4: "obj = the (heap S l)"
  assumes op5: "(d, m) = the (cmethod P (HClass obj) mname)"
  assumes op6: "s = the (mstmt m)"
  assumes s0: "S0 = S\<lparr>stack := (stack S \<circ>\<^sub>m map_formalpar_to_args (mdecl m) args)(This \<mapsto> a), retval := None, privs := (HLabel obj)\<rparr>"
  assumes s': "S' = S1\<lparr>stack := stack S, retval := retval S, privs := privs S\<rparr>"
  assumes retval_if_noexcept: "except S1 = None \<longrightarrow> retval S1 \<noteq> None"
  assumes v: "v = the (retval S1)"
  assumes "P \<turnstile> \<langle>s | S0\<rangle> \<rightarrow>\<^sub>s \<langle>S1\<rangle>"
  (* induction hypothesis *)
  assumes hyp: "(\<forall>M \<Gamma>. (P M \<Gamma> \<^bold>\<turnstile> S0) \<and> (P M \<Gamma> \<turnstile> s \<bullet>) \<and> privs S0 \<subseteq> \<gamma> \<longrightarrow> (P \<gamma> \<turnstile> \<langle>S0\<rangle> \<rightarrow>\<^sub>A \<langle>S1\<rangle>))"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wfp: "wf_prog P"
  assumes wf: "P M \<Gamma> \<turnstile> calli x mname args : T"
  assumes gamma: "(privs S) \<subseteq> \<gamma>"
  shows "allowed_transition P \<gamma> S S'"
proof -
  (* Bits of this proof have been taken from the preservation proof. *)
  define M0 where "M0 = call_menv d m"
  moreover define \<Gamma>0 where "\<Gamma>0 = call_lenvi P d (mdecl m)"
  ultimately have a1: "(P M0 \<Gamma>0 \<^bold>\<turnstile> S0) \<and> (P M0 \<Gamma>0 \<turnstile> s \<bullet>)" using calli_prems assms by metis
  
  obtain t0 \<gamma>0 decl t' where a2: "(\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some (t0,\<gamma>0)) \<and> methoddecl P t0 mname = Some decl \<and>
                        is_type P t0 \<and> (\<forall>t. t0 \<noteq> (ValT t)) \<and> \<not>mstatic decl \<and>
                        wf_method_call P \<Gamma> decl args \<gamma>0 (t',(tlabel T)) \<and> (subsumption P t' (ttype T))"
    using wf wf_expr_calli_intro by (metis prod.collapse) 
                           
  (* Infer the the object pointed to by x exists, and has a runtime type compatible with the static type t0. *)
  have a3: "a = (href l) \<and> heap S l = Some obj \<and> (P \<turnstile> (ClassT (HClass obj)) <: t0) \<and> is_obj_label_ok P obj (intersect_label (t0,\<gamma>0) (privs S))"
    using object_correspondence a2 op1 op2 op3 op4 corr by (metis fst_conv) 

  show ?thesis proof (cases "is_cap_type P t0")
    case True
    then obtain cbname where b1: "t0 = IfaceT cbname \<and> is_cap P cbname"
      by (metis \<tau>.exhaust a2 is_cap_type.simps(2) is_cap_type.simps(3))
    then have b2: "\<gamma>0 \<inter> (privs S) = (cap_label P cbname) \<inter> (HLabel obj) \<and>
                (* This gives some 'meaning' to the labels. *)
                (superinterface_set P cbname) \<subseteq> \<gamma>0 \<inter> (privs S)"
      using a3 intersect_label_label intersect_label_type unfolding is_obj_label_ok_def by auto
    then have b3: "cbname \<in> \<gamma>"
      unfolding superinterface_set_def using gamma by auto
    moreover have "(\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some (t0,\<gamma>0))" using a2 by simp
    moreover have "P \<turnstile> \<langle>(calli x mname args) | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S'\<rangle>" using assms op_expr_calli by simp
    ultimately show "allowed_transition P \<gamma> S S'"
      using at_cap_call corr wf b1 by simp
  next
    case False
    then have "(HLabel obj) = \<gamma>0 \<inter> (privs S)"
      using a3 intersect_label_label intersect_label_type unfolding is_obj_label_ok_def by auto
    then have b1: "(HLabel obj) \<subseteq> \<gamma>" using gamma by auto
    then have "allowed_transition P \<gamma> S S0"
      using at_stack_update at_retval_update at_privs_update at_trans s0 by metis
    moreover have "allowed_transition P \<gamma> S0 S1"
      using hyp a1 s0 b1 by fastforce
    moreover have "allowed_transition P \<gamma> S1 S'"
      using at_stack_update at_retval_update at_privs_update at_trans s' gamma by metis
    ultimately show ?thesis
      using at_trans by metis
  qed
qed

lemma allowed_transition_expr_calls:
  assumes op5: "(d, m) = the (cmethod P c mname)"
  assumes "P \<turnstile> \<langle>s | S0\<rangle> \<rightarrow>\<^sub>s \<langle>S1\<rangle>"
  assumes hyp: "\<forall>M \<Gamma>. (P M \<Gamma> \<^bold>\<turnstile> S0) \<and> (P M \<Gamma> \<turnstile> s \<bullet>) \<and> privs S0 \<subseteq> \<gamma> \<longrightarrow> (P \<gamma> \<turnstile> \<langle>S0\<rangle> \<rightarrow>\<^sub>A \<langle>S1\<rangle>)"
  assumes "s = the (mstmt m)"
  assumes s0: "S0 = S\<lparr>stack := stack S \<circ>\<^sub>m map_formalpar_to_args (mdecl m) args, retval := None, privs := (privs S) \<inter> lbl\<rparr>"
  assumes s': "S' = S1\<lparr>stack := stack S, retval := retval S, privs := privs S\<rparr>"
  assumes retval_if_noexcept: "except S1 = None \<longrightarrow> retval S1 \<noteq> None"
  assumes v: "v = the (retval S1)"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wfp: "wf_prog P"
  assumes wf: "P M \<Gamma> \<turnstile> calls c mname lbl args : T"
  assumes gamma: "(privs S) \<subseteq> \<gamma>"
  shows "allowed_transition P \<gamma> S S'"
proof -
  have "privs S \<inter> lbl \<subseteq> \<gamma>"
    using gamma by auto
  then have "allowed_transition P \<gamma> S S0"
    using at_stack_update at_retval_update at_privs_update at_trans s0 by metis
  moreover have "allowed_transition P \<gamma> S0 S1"
  proof -
    define M0 where "M0 = call_menv d m"
    moreover define \<Gamma>0 where "\<Gamma>0 = call_lenvs P (mdecl m)"
    ultimately have "(P M0 \<Gamma>0 \<^bold>\<turnstile> S0) \<and> (P M0 \<Gamma>0 \<turnstile> s \<bullet>)" using calls_prems assms by metis
    moreover have "privs S0 \<subseteq> \<gamma>"
      using gamma s0 by auto
    ultimately show ?thesis using hyp by blast
  qed
  moreover have "allowed_transition P \<gamma> S1 S'"
    using at_stack_update at_retval_update at_privs_update at_trans s' gamma by metis
  ultimately show ?thesis 
    using at_trans by metis
qed


lemma allowed_transition_stmt_assignfi:
  assumes op1: "no_exception_or_return S" (* unused *)
  assumes op2: "a = the (stack S1 x)"
  assumes op3: "a \<noteq> v.null"
  assumes op4: "l = the_href a"
  assumes op5: "obj = the (heap S1 l)"
  assumes op6: "S' = (if except S1 = None then S1\<lparr>heap := heap S1(l \<mapsto> obj\<lparr>HFields := HFields obj(f \<mapsto> v)\<rparr>)\<rparr> else S1)"
  assumes op7: "P \<turnstile> \<langle>e | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S1\<rangle>" (* unused *)
  assumes hyp: "\<And>M \<Gamma> T. (P M \<Gamma> \<^bold>\<turnstile> S) \<and> (P M \<Gamma> \<turnstile> e : T) \<and> (privs S \<subseteq> \<gamma>)  \<longrightarrow> allowed_transition P \<gamma> S S1"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wf: "P M \<Gamma> \<turnstile> assignfi x f e \<bullet>"
  assumes wfp: "wf_prog P"
  assumes gamma: "(privs S) \<subseteq> \<gamma>"
  shows "allowed_transition P \<gamma> S S'"
proof -
  obtain T where a1: "wf_fieldi_access P \<Gamma> x f T \<and> (P M \<Gamma> \<turnstile> e : T)"
    using wf wf_stmt_assignfi_intro by blast
  obtain c \<gamma>0 fdecl where a2: "(\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some ((ClassT c),\<gamma>0)) \<and> field P c f = Some fdecl \<and>
                                    \<not>fstatic fdecl \<and> T = intersect_label (ftype fdecl) \<gamma>0"
    using a1 unfolding wf_fieldi_access_def by blast
  have a3: "(P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S S1 \<and> is_expr_value_ok P S1 T v"
    using preservation op7 wfp corr a1 by metis

  have "allowed_transition P \<gamma> S S1"
    using a1 corr gamma hyp by blast
  moreover have "allowed_transition P \<gamma> S1 S'" proof (cases "except S1")
    case None
    have "heap S1 l = Some obj \<and> (P \<turnstile> (ClassT (HClass obj)) <: (ClassT c)) \<and> 
            is_obj_label_ok P obj (intersect_label ((ClassT c),\<gamma>0) (privs S1))"  
      using object_correspondence a2 a3 op2 op3 op4 op5 by (metis \<tau>.simps(5) fst_conv)
    then have "HLabel obj \<subseteq> (privs S1)"
      unfolding is_obj_label_ok_def by (simp add: intersect_label_label intersect_label_type) 
    then have "HLabel obj \<subseteq> \<gamma>"
      using a3 gamma unfolding transition_ok_def by simp 
    then show ?thesis using  at_heap_update op6 None by simp
  next
    case (Some a)
    then have "S' = S1" using op6 by simp
    then show ?thesis using at_reflexive by simp
  qed
  ultimately show ?thesis using at_trans by metis
qed

lemma allowed_transition_stmt_assignfs:
  assumes op1: "no_exception_or_return S"
  assumes op2: "classStatics = the (globals S1 c)"
  assumes op3: "S' = (if except S1 = None then S1\<lparr>globals := globals S1(c \<mapsto> classStatics(f \<mapsto> v))\<rparr> else S1)"
  assumes op4: "P \<turnstile> \<langle>e | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S1\<rangle>"
  assumes hyp: "\<And>M \<Gamma> T. (P M \<Gamma> \<^bold>\<turnstile> S) \<and> (P M \<Gamma> \<turnstile> e : T) \<and> (privs S \<subseteq> \<gamma>)  \<longrightarrow> allowed_transition P \<gamma> S S1"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wf: "P M \<Gamma> \<turnstile> assignfs c f e \<bullet>"
  assumes wfp: "wf_prog P"
  assumes gamma: "(privs S) \<subseteq> \<gamma>"
  shows "allowed_transition P \<gamma> S S'"
proof -
  obtain T where a1: "wf_fields_access P M c f T \<and> (P M \<Gamma> \<turnstile> e : T)"
    using wf wf_stmt_assignfs_intro by blast
  then obtain fdecl where a2: "is_class P c \<and> field P c f = Some fdecl \<and> fstatic fdecl \<and> 
                                  (T = (ftype fdecl) \<and> (tlabel (ftype fdecl)) \<subseteq> (msreq M))"
    using wf_fields_access_def by auto
  have a3: "(P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S S1 \<and> is_expr_value_ok P S1 T v"
    using preservation op4 wfp a1 corr by blast
  
  have "allowed_transition P \<gamma> S S1"
    using a1 corr gamma hyp by blast
  moreover have "allowed_transition P \<gamma> S1 S'" proof (cases "except S1")
    case None
    have "(tlabel (ftype fdecl)) \<subseteq> \<gamma>"
      using a2 corr gamma unfolding corr_def by auto
    then show ?thesis using a2 at_globals_update op2 op3 None by metis
  next
    case (Some a)
    then show ?thesis using op3 at_reflexive by simp
  qed
  ultimately show ?thesis using at_trans by metis
qed

lemma allowed_transition_stmt_letin:
  assumes op1: "no_exception_or_return S"
  assumes op2: "P \<turnstile> \<langle>e | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S1\<rangle>"
  assumes op3: "S2 = (if except S1 = None then S1\<lparr>stack := stack S1(x \<mapsto> v)\<rparr> else S1)"
  assumes op4: "P \<turnstile> \<langle>s | S2\<rangle> \<rightarrow>\<^sub>s \<langle>S3\<rangle>"
  assumes op5: "S' = S3\<lparr>stack := (stack S3)(x := stack S x)\<rparr>"
  assumes hype: "\<And>M \<Gamma> T. (P M \<Gamma> \<^bold>\<turnstile> S) \<and> (P M \<Gamma> \<turnstile> e : T) \<and> (privs S) \<subseteq> \<gamma> \<longrightarrow> allowed_transition P \<gamma> S S1"
  assumes hyps: "\<And>M \<Gamma>. (P M \<Gamma> \<^bold>\<turnstile> S2) \<and> (P M \<Gamma> \<turnstile> s \<bullet>)  \<and> (privs S2) \<subseteq> \<gamma> \<longrightarrow> allowed_transition P \<gamma> S2 S3"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wf: "P M \<Gamma> \<turnstile> letin T x e s \<bullet>"
  assumes wfp: "wf_prog P"
  assumes gamma: "(privs S) \<subseteq> \<gamma>"
  shows "allowed_transition P \<gamma> S S'"
proof -
  have wfi: "(P M \<Gamma> \<turnstile> e : T) \<and> (P M \<Gamma>(x\<mapsto>T) \<turnstile> s \<bullet>)"
    using wf wf_stmt_letin_intro by simp
  then have "(P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S S1 \<and> is_expr_value_ok P S1 T v"
    using wfp preservation op2 corr by metis
  (* If the exception did not throw an exception during evaluation, the assignment occurs 
     and S2 is type-correct to \<Gamma>(x\<mapsto>T). Otherwise the assignment does not occur and we
     end-up correct to \<Gamma> only. We rely on the fact that the let-in body will not be executed
     in this case (due to an unhandled exception.)  *)
  then have a2: "(except S2 = None \<longrightarrow> (P M \<Gamma>(x\<mapsto>T) \<^bold>\<turnstile> S2)) \<and> 
                 (except S2 \<noteq> None \<longrightarrow> (P M \<Gamma> \<^bold>\<turnstile> S2)) \<and> transition_ok S S2"
    using preservation_stmt_assign_base op3 by metis

  have a1: "allowed_transition P \<gamma> S S1"
    using wfi hype corr gamma by blast
  moreover have "allowed_transition P \<gamma> S1 S2"
    using op3 at_stack_update at_reflexive by simp
  moreover have "allowed_transition P \<gamma> S2 S3"
  proof (cases "except S2")
    case None
    then have "(P M \<Gamma>(x \<mapsto> T) \<^bold>\<turnstile> S2) \<and> (privs S2 \<subseteq> \<gamma>)"
      using a2 gamma unfolding transition_ok_def by simp
    then show "allowed_transition P \<gamma> S2 S3"
      using hyps wfi by metis
  next
    case (Some a)
    then have "S2 = S3"
      using exception_or_return_skips op4 unfolding no_exception_or_return_def by simp
    then show "allowed_transition P \<gamma> S2 S3"
      using at_reflexive by simp
  qed
  moreover have "allowed_transition P \<gamma> S3 S'"
    using op5 at_stack_update at_reflexive by simp
  ultimately show ?thesis 
    using at_trans by metis
qed

lemma allowed_transition_stmt_seq:
  assumes op1: "no_exception_or_return S"
  assumes op2: "P \<turnstile> \<langle>s1 | S\<rangle> \<rightarrow>\<^sub>s \<langle>S1\<rangle>"
  assumes op3: "\<forall>M \<Gamma>. (P M \<Gamma> \<^bold>\<turnstile> S) \<and> (P M \<Gamma> \<turnstile> s1 \<bullet>) \<and> privs S \<subseteq> \<gamma> \<longrightarrow> (P \<gamma> \<turnstile> \<langle>S\<rangle> \<rightarrow>\<^sub>A \<langle>S1\<rangle>)"
  assumes op4: "P \<turnstile> \<langle>s2 | S1\<rangle> \<rightarrow>\<^sub>s \<langle>S2\<rangle>"
  assumes op5: "\<forall>M \<Gamma>. (P M \<Gamma> \<^bold>\<turnstile> S1) \<and> (P M \<Gamma> \<turnstile> s2 \<bullet>) \<and> privs S1 \<subseteq> \<gamma> \<longrightarrow> (P \<gamma> \<turnstile> \<langle>S1\<rangle> \<rightarrow>\<^sub>A \<langle>S2\<rangle>)"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wf: "P M \<Gamma> \<turnstile> seq s1 s2 \<bullet>"
  assumes wfp: "wf_prog P"
  assumes gamma: "(privs S) \<subseteq> \<gamma>"
  shows "allowed_transition P \<gamma> S S2"
proof -
  have a1: "(P M \<Gamma> \<turnstile> s1 \<bullet>) \<and> (P M \<Gamma> \<turnstile> s2 \<bullet>)"
    using wf wf_stmt_seq_intro by metis
  have a2: "(P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S S1"
    using wfp preservation op2 corr a1 by metis

  have "allowed_transition P \<gamma> S S1"
    using op3 corr a1 gamma by metis
  moreover have "allowed_transition P \<gamma> S1 S2"
    using op5 a1 a2 gamma unfolding transition_ok_def by metis
  ultimately show ?thesis using at_trans by metis
qed


lemma allowed_transition_stmt_trycatch_ex:
  assumes op1: "no_exception_or_return S"
  assumes op2: "except S1 = Some ex"
  assumes op3: "a = the_href ex"
  assumes op4: "exObj = the (heap S1 a)"
  assumes op5: "P \<turnstile> \<langle>s | S\<rangle> \<rightarrow>\<^sub>s \<langle>S1\<rangle>"
  assumes op6: "i = Min {j::nat. (j = length ch) \<or> ((j < length ch) \<and> (P \<turnstile> (ClassT (HClass exObj)) <: (chtype (ch !j)))) }"
  assumes op7: "if i < length ch
                then h = ch ! i \<and>
                     var = chvar h \<and>
                     S2 = S1\<lparr>except := None, stack := (stack S1)(var \<mapsto> ex)\<rparr> \<and>
                     ((P \<turnstile> \<langle>chstmt h | S2\<rangle> \<rightarrow>\<^sub>s \<langle>S3\<rangle>) \<and> (\<forall>M \<Gamma>. (P M \<Gamma> \<^bold>\<turnstile> S2) \<and> (P M \<Gamma> \<turnstile> chstmt h \<bullet>) \<and> (privs S2) \<subseteq> \<gamma>
                           \<longrightarrow> allowed_transition P \<gamma> S2 S3)) \<and> 
                     S' = S3\<lparr>stack := (stack S3)(var := stack S1 var)\<rparr>
                else S' = S1"
  assumes hyp: "\<And>M \<Gamma>. (P M \<Gamma> \<^bold>\<turnstile> S) \<and> (P M \<Gamma> \<turnstile> s \<bullet>) \<and> (privs S) \<subseteq> \<gamma> \<longrightarrow>allowed_transition P \<gamma> S S1"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wf: "P M \<Gamma> \<turnstile> trycatch s ch \<bullet>"
  assumes wfp: "wf_prog P"
  assumes gamma: "(privs S) \<subseteq> \<gamma>"
  shows "allowed_transition P \<gamma> S S'"
proof -
  (* Need to statisfy induction hypothesis of existing proof *)
  have "if i < length ch
                then h = ch ! i \<and>
                     var = chvar h \<and>
                     S2 = S1\<lparr>except := None, stack := (stack S1)(var \<mapsto> ex)\<rparr> \<and>
                     ((P \<turnstile> \<langle>chstmt h | S2\<rangle> \<rightarrow>\<^sub>s \<langle>S3\<rangle>) \<and> (\<forall>M \<Gamma>. (P M \<Gamma> \<^bold>\<turnstile> S2) \<and> (P M \<Gamma> \<turnstile> chstmt h \<bullet>)
                           \<longrightarrow> (P M \<Gamma> \<^bold>\<turnstile> S3) \<and> transition_ok S2 S3)) \<and> 
                     S' = S3\<lparr>stack := (stack S3)(var := stack S1 var)\<rparr>
                else S' = S1"
    using op7 preservation wfp  by meson
  moreover have  "\<And>M \<Gamma>. (P M \<Gamma> \<^bold>\<turnstile> S) \<and> (P M \<Gamma> \<turnstile> s \<bullet>) \<longrightarrow> (P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S S1"
    using preservation op5 wfp by meson
  moreover define \<Gamma>' where "\<Gamma>' = \<Gamma>(var \<mapsto> ((chtype h),{}))"
  ultimately have a1: "(P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S S1 \<and>
          (i < length ch \<longrightarrow> (P M \<Gamma>' \<^bold>\<turnstile> S2) \<and> (P M \<Gamma>' \<turnstile> chstmt h \<bullet>) \<and> transition_ok S1 S2 \<and>
                             (P M \<Gamma>' \<^bold>\<turnstile> S3) \<and> transition_ok S2 S3 \<and> transition_ok S3 S') \<and>
          (P M \<Gamma> \<^bold>\<turnstile> S') \<and> transition_ok S1 S'"
    using preservation_stmt_trycatch_ex_helper assms by blast

  have a2: "(P M \<Gamma> \<turnstile> s \<bullet>) \<and> (\<forall>(t,x,s')\<in>(set ch). (P M \<Gamma>(x\<mapsto>(t,{})) \<turnstile> s' \<bullet>) \<and> \<not>is_cap_type P t)"
    using wf wf_stmt_trycatch_intro by simp

  have "allowed_transition P \<gamma> S S1" using corr hyp a2 gamma by metis
  moreover have "allowed_transition P \<gamma> S1 S'"
  proof (cases "i < length ch")
    case True
    then have "allowed_transition P \<gamma> S1 S2"
      using op7 at_stack_update at_except_update at_trans by metis
    moreover have "allowed_transition P \<gamma> S2 S3"
    proof -
      have "privs S2 \<subseteq> \<gamma>" using a1 True gamma unfolding transition_ok_def by simp
      then show ?thesis using op7 a1 True by metis
    qed
    moreover have "allowed_transition P \<gamma> S3 S'"
      using op7 True at_stack_update by metis
    ultimately show ?thesis using at_trans by metis
  next
    case False
    then show ?thesis using op7 at_reflexive by metis
  qed
  ultimately show ?thesis using at_trans by metis
qed

lemma security_proof_state:
  assumes wfp: "wf_prog P"
  shows "((P \<turnstile> \<langle>e | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S'\<rangle>) \<longrightarrow> (\<forall>M \<Gamma> T. (P M \<Gamma> \<^bold>\<turnstile> S) \<and> (P M \<Gamma> \<turnstile> e : T) \<and> (privs S) \<subseteq> \<gamma> \<longrightarrow> (allowed_transition P \<gamma> S S')))
       \<and> ((P \<turnstile> \<langle>s | S\<rangle> \<rightarrow>\<^sub>s \<langle>S'\<rangle>) \<longrightarrow> (\<forall>M \<Gamma>. (P M \<Gamma> \<^bold>\<turnstile> S) \<and> (P M \<Gamma> \<turnstile> s \<bullet>) \<and> (privs S) \<subseteq> \<gamma> \<longrightarrow> (allowed_transition P \<gamma> S S')))"
proof (induction S S' rule: op_expr_op_stmt.induct)
  case (op_expr_ref v S x)
  then show ?case using at_reflexive by simp
next
  case (op_expr_new v l S S' cname lbl)
  then show ?case using allowed_transition_expr_new wfp by blast
next
  case (op_expr_calli a S x l obj d m mname s S0 args S1 S' v)
  then show ?case using allowed_transition_expr_calli wfp by force
next
  case (op_expr_calls d m c mname s S0 S lbl args S1 S' v)
  then show ?case using allowed_transition_expr_calls wfp by force
next
  case (op_expr_cast e S v S' hobj t)
  then show ?case using wf_expr_cast_intro by (metis prod.exhaust_sel)
next
  case (op_expr_const k v S)
  then show ?case using at_reflexive by simp
next
  case (op_expr_fieldacci a S x l obj v f)
  then show ?case using at_reflexive by simp
next
  case (op_expr_fieldaccs classStatics S c v f)
  then show ?case using at_reflexive by simp
next
  case (op_expr_wrap e S v S' cbname)
  then show ?case using wf_expr_wrap_intro by (metis prod.exhaust_sel)
next
  case (op_stmt_assign S e v S1 S' x)
  then show ?case using wf_stmt_assign_intro at_trans at_stack_update by metis
next
  case (op_stmt_assignfi S e v S1 a x l obj S' f)
  then show ?case using allowed_transition_stmt_assignfi wfp by blast
next
  case (op_stmt_assignfs S e v S1 classStatics c S' f)
  then show ?case using allowed_transition_stmt_assignfs wfp by blast
next
  case (op_stmt_expr S e v S')
  then show ?case using wf_stmt_expr_intro by metis
next
  case (op_stmt_then S v x s1 S1 s2)
  then show ?case using wf_stmt_ifelse_intro by metis
next
  case (op_stmt_else S v x s2 S2 s1)
  then show ?case using wf_stmt_ifelse_intro by metis
next
  case (op_stmt_letin S e v S1 S2 x s S3 S' T)
  then show ?case using allowed_transition_stmt_letin wfp by blast
next
  case (op_stmt_return S e v S1 S')
  then show ?case using wf_stmt_return_intro at_trans at_retval_update by metis
next
  case (op_stmt_seq S s1 S1 s2 S2)
  then show ?case using allowed_transition_stmt_seq wfp by blast
next
  case (op_stmt_throw S e v S1 S')
  then show ?case using wf_stmt_throw_intro at_trans at_except_update by metis
next
  case (op_stmt_trycatch_ok S s S1 S' catchhandlers)
  then show ?case using wf_stmt_trycatch_intro by metis
next
  case (op_stmt_trycatch_ex S s S1 ex a exObj i ch h var S2 S3 S')
  then show ?case using allowed_transition_stmt_trycatch_ex wfp by blast
next
  case (op_stmt_exception_or_return S s)
  then show ?case using at_reflexive by simp
qed

end