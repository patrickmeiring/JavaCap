theory javacap_operational
imports
  Main
  javacap_syntax
  javacap_auxiliary
  javacap_static
  javacap_runtime_representation
begin   

definition no_exception_or_return :: "State \<Rightarrow> bool"
  where "no_exception_or_return S \<equiv> (except S = None) \<and> (retval S = None)"

definition map_formalpar_to_args :: "mdecl \<Rightarrow> var list \<Rightarrow> (var \<rightharpoonup> var)"
  where "map_formalpar_to_args md args \<equiv> map_of (zip (map fst (mpar md)) args)"

lemma map_formalpar_to_args_match:
  assumes "length (mpar md) = length args"
  assumes "fst ((mpar md) ! i) = formalpar"
  assumes "args ! i = actualpar"
  assumes unique_keys: "unique_keys (mpar md)"
  assumes "i < length args"
  shows "(map_formalpar_to_args md args) formalpar = Some actualpar"
  using assms unfolding map_formalpar_to_args_def unique_keys_def
  by (metis (no_types, lifting) comp_def length_map map_of_zip_nth nth_map) 

inductive op_expr :: "prog \<Rightarrow> exp \<Rightarrow> State \<Rightarrow> v \<Rightarrow> State \<Rightarrow> bool" ("_ \<turnstile> \<langle>_ | _\<rangle> \<rightarrow>\<^sub>e \<langle>_ | _\<rangle>" 50) and
          op_stmt :: "prog \<Rightarrow> stmt \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool"     ("_ \<turnstile> \<langle>_ | _\<rangle> \<rightarrow>\<^sub>s \<langle>_\<rangle>" 50)
  for P :: "prog"
(* datatype exp =
      ref "var" 
    | new "cname" 
    | calli "var" "mname" "var list" (* instance method call *)
    | calls "cname" "mname" "var list" (* static method call *)
    | cast "\<tau>" "exp" 
    | const "k"
    | fieldacci "var" "fname"  (* instance field access *)
    | fieldaccs "cname" "fname" (* static field access *)
    | wrap "iname" "exp" *)
  where op_expr_ref: "\<lbrakk> v = the (stack S x) \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>(ref x) | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S\<rangle>"
      (*Assumes new heap location l is always available *)
      | op_expr_new: "\<lbrakk> v = (href l); l \<notin> dom (heap S);
                       S' = S\<lparr>heap := (heap S)(l\<mapsto>(new_object P cname (lbl \<inter> (privs S))))\<rparr>\<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>(new lbl cname) | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S'\<rangle>"
      | op_expr_calli: "\<lbrakk> a = the (stack S x); l = the_href a;
                          a \<noteq> null; (* added, exception to be thrown otherwise *)
                         obj = the (heap S l); (d,m) = the (cmethod P (HClass obj) mname); s = the (mstmt m);      
                        (* Compose S0 from S by mapping the formal parameter names to the actual parameter names. Add the 'this' parameter. *)
                        S0 = S\<lparr>stack := ((stack S) \<circ>\<^sub>m map_formalpar_to_args (mdecl m) args)(This \<mapsto> a), retval := None, privs := (HLabel obj) \<rparr>;
                        P \<turnstile> \<langle>s | S0\<rangle> \<rightarrow>\<^sub>s \<langle>S1\<rangle>;
                        (* note: the updated heap, globals and any exceptions carry through.
                           the stack and any return value do not. *)
                        S' = S1\<lparr>stack := (stack S), retval := (retval S), privs := (privs S)\<rparr>;
                        (except S1 = None \<longrightarrow> retval S1 \<noteq> None); (* added, exception to be thrown otherwise *)
                        v = the (retval S1)
                      \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>(calli x mname args) | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S'\<rangle>"
      | op_expr_calls: "\<lbrakk> (d,m) = the (cmethod P c mname); s = the (mstmt m);
                        (* Compose S0 from S by mapping the formal parameter names (that is, the first component of (msig m)) to 
                           the actual parameter names as stored in args.  *)
                        S0 = S\<lparr>stack := ((stack S) \<circ>\<^sub>m map_formalpar_to_args (mdecl m) args), retval := None, privs := (privs S) \<inter> lbl\<rparr>;
                        P \<turnstile> \<langle>s | S0\<rangle> \<rightarrow>\<^sub>s \<langle>S1\<rangle>;
                        (* note: the updated heap, globals and any exceptions carry through.
                           the stack and any return value does not. *)
                        S' = S1\<lparr>stack := (stack S), retval := (retval S), privs := privs S\<rparr>;
                        (except S1 = None \<longrightarrow> retval S1 \<noteq> None); (* added, exception to be thrown otherwise *)
                        v = the (retval S1) \<rbrakk> 
                         \<Longrightarrow> P \<turnstile> \<langle>(calls c mname lbl args) | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S'\<rangle>"
      | op_expr_cast: "\<lbrakk> P \<turnstile> \<langle>e | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S'\<rangle>;
                       (case v of (href l) \<Rightarrow> (hobj = the (heap S' l)) \<and> (P \<turnstile> (ClassT (HClass hobj)) <: t) 
                                | (num n) \<Rightarrow> t = ValT IntT ) \<rbrakk>
                            \<Longrightarrow> P \<turnstile> \<langle>(cast t e) | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S'\<rangle>"
      | op_expr_const: "\<lbrakk> (case k of k.null \<Rightarrow> v = v.null | k.num n \<Rightarrow> v = v.num n) \<rbrakk>
                         \<Longrightarrow> P \<turnstile> \<langle>(const k) | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S\<rangle>"
      (* PM: For now, we make execution infeasible if the address is null. *)
      | op_expr_fieldacci: "\<lbrakk> a = the (stack S x); a \<noteq> null; l = the_href a; obj = the (heap S l); v = the ((HFields obj) f) \<rbrakk>
                        \<Longrightarrow> P \<turnstile> \<langle>(fieldacci x f) | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S\<rangle>"      
      | op_expr_fieldaccs: "\<lbrakk> classStatics = the (globals S c); v = the (classStatics f) \<rbrakk>
                         \<Longrightarrow> P \<turnstile> \<langle>(fieldaccs c f) | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S\<rangle>"
      (* Wrapping does absolutely nothing at runtime *)
      | op_expr_wrap: "\<lbrakk> P \<turnstile> \<langle>e | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S'\<rangle>  \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>(wrap cbname e) | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S'\<rangle>"

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
      (* if no exception *)
      | op_stmt_assign: "\<lbrakk> no_exception_or_return S; 
                           P \<turnstile> \<langle>e | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S1\<rangle>;
                           S' = (if except S1 = None then S1\<lparr>stack := (stack S1)(x\<mapsto>v)\<rparr> else S1) \<rbrakk>
                           \<Longrightarrow> P \<turnstile> \<langle>(assign x e) | S\<rangle> \<rightarrow>\<^sub>s \<langle>S'\<rangle>"
      (* PM: Currently assume no null reference.*)
      | op_stmt_assignfi: "\<lbrakk> no_exception_or_return S;
                             P \<turnstile> \<langle>e | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S1\<rangle>; a = the (stack S1 x); a \<noteq> null;
                             l = the_href a; obj = the (heap S1 l);
                             S' = (if except S1 = None then S1\<lparr>heap := (heap S1)(l\<mapsto>(obj\<lparr>HFields := ((HFields obj)(f\<mapsto>v))\<rparr>))\<rparr> else S1) \<rbrakk>
                             \<Longrightarrow> P \<turnstile> \<langle>(assignfi x f e) | S\<rangle> \<rightarrow>\<^sub>s \<langle>S'\<rangle>"
      | op_stmt_assignfs: "\<lbrakk> no_exception_or_return S;
                             P \<turnstile> \<langle>e | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S1\<rangle>; classStatics = the ((globals S1) c);
                             S' = (if except S1 = None then S1\<lparr>globals := (globals S1)(c\<mapsto>(classStatics(f\<mapsto>v)))\<rparr> else S1) \<rbrakk>
                             \<Longrightarrow> P \<turnstile> \<langle>(assignfs c f e) | S\<rangle> \<rightarrow>\<^sub>s \<langle>S'\<rangle>"
      | op_stmt_expr: "\<lbrakk> no_exception_or_return S;
                         P \<turnstile> \<langle>e | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S'\<rangle> \<rbrakk>
                         \<Longrightarrow> P \<turnstile> \<langle>(expr e) | S\<rangle> \<rightarrow>\<^sub>s \<langle>S'\<rangle>"
      | op_stmt_then: "\<lbrakk> no_exception_or_return S;
                         v = the (stack S x); (the_num v) > 0;
                         P \<turnstile> \<langle>s1 | S\<rangle> \<rightarrow>\<^sub>s \<langle>S1\<rangle> \<rbrakk> \<Longrightarrow>
                         P \<turnstile> \<langle>(ifelse x s1 s2) | S\<rangle> \<rightarrow>\<^sub>s \<langle>S1\<rangle>"
      | op_stmt_else: "\<lbrakk> no_exception_or_return S;
                         v = the (stack S x); (the_num v) \<le> 0; 
                         P \<turnstile> \<langle>s2 | S\<rangle> \<rightarrow>\<^sub>s \<langle>S2\<rangle> \<rbrakk> \<Longrightarrow>
                         P \<turnstile> \<langle>(ifelse x s1 s2) | S\<rangle> \<rightarrow>\<^sub>s \<langle>S2\<rangle>"
      | op_stmt_letin: "\<lbrakk> no_exception_or_return S; 
                          S1 = S\<lparr>stack := (stack S)(x\<mapsto>v.null)\<rparr>; (* initialise empty *)
                          P \<turnstile> \<langle>(seq (assign x e) s) | S1\<rangle> \<rightarrow>\<^sub>s \<langle>S2\<rangle>;
                          S' = S2\<lparr>stack := (stack S2)(x := (stack S x))\<rparr>
                         \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>(letin T x e s) | S\<rangle> \<rightarrow>\<^sub>s \<langle>S'\<rangle>"
      | op_stmt_return: "\<lbrakk> no_exception_or_return S;                         
                           P \<turnstile> \<langle>e | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S1\<rangle>; 
                           S' = (if except S1 = None then S1\<lparr>retval := Some v\<rparr> else S1) \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>(return e) | S\<rangle> \<rightarrow>\<^sub>s \<langle>S'\<rangle>"
      | op_stmt_seq: "\<lbrakk> no_exception_or_return S;
                        P \<turnstile> \<langle>s1 | S\<rangle> \<rightarrow>\<^sub>s \<langle>S1\<rangle>;                        
                        P \<turnstile> \<langle>s2 | S1\<rangle> \<rightarrow>\<^sub>s \<langle>S2\<rangle>\<rbrakk> \<Longrightarrow>
                        P \<turnstile> \<langle>(seq s1 s2) | S\<rangle> \<rightarrow>\<^sub>s \<langle>S2\<rangle>"
      | op_stmt_throw: "\<lbrakk> no_exception_or_return S;                         
                           P \<turnstile> \<langle>e | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S1\<rangle>; 
                           v \<noteq> null; (* else a NullReferenceException should be thrown *)
                           S' = (if except S1 = None then S1\<lparr>except := Some v\<rparr> else S1) \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>(throw e) | S\<rangle> \<rightarrow>\<^sub>s \<langle>S'\<rangle>"
      | op_stmt_trycatch_ok: "\<lbrakk> no_exception_or_return S;
                             P \<turnstile> \<langle>s | S\<rangle> \<rightarrow>\<^sub>s \<langle>S1\<rangle>;
                             except S1 = None;
                             S' = S1 \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>(trycatch s catchhandlers) | S\<rangle> \<rightarrow>\<^sub>s \<langle>S'\<rangle>"
      | op_stmt_trycatch_ex: "\<lbrakk> no_exception_or_return S;
                             P \<turnstile> \<langle>s | S\<rangle> \<rightarrow>\<^sub>s \<langle>S1\<rangle>;
                             except S1 = Some ex;
                             a = the_href ex; exObj = the (heap S1 a);
                             i = Min {j::nat. (j = length ch) \<or> ((j < length ch) \<and> (P \<turnstile> (ClassT (HClass exObj)) <: (chtype (ch !j)))) };
                             if (i < length ch) 
                             then (h = (ch ! i)) \<and>
                                  var = (chvar h) \<and>
                                  S2 = S1\<lparr>except := None, stack := (stack S1)(var \<mapsto> ex)\<rparr> \<and>
                                  (P \<turnstile> \<langle>(chstmt h) | S2\<rangle> \<rightarrow>\<^sub>s \<langle>S3\<rangle>) \<and>
                                  S' = S3\<lparr>stack:= (stack S3)(var := (stack S1 var))\<rparr>
                             else S' = S1 \<rbrakk>
                             \<Longrightarrow> P \<turnstile> \<langle>(trycatch s ch) | S\<rangle> \<rightarrow>\<^sub>s \<langle>S'\<rangle>"
      | op_stmt_exception_or_return: "\<lbrakk> \<not>no_exception_or_return S \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>s | S\<rangle> \<rightarrow>\<^sub>s \<langle>S\<rangle>" (* skip over the statement *)


lemma is_value_ok_subsumption:
  assumes wfp: "wf_prog P"
  assumes ok: "is_value_ok P H T' v"
  assumes t'_implements_t: "subsumption P (ttype T') (ttype T)"
  assumes label_same: "tlabel T' = tlabel T"
  shows "is_value_ok P H T v"
proof (cases "(P, H, T, v)" rule: is_value_ok.cases)
  case (1 P H t v)
  then show ?thesis proof (cases "is_cap_type P (ttype T)")
    case True
    then show ?thesis using 1 ok t'_implements_t subtype_int_parity unfolding subsumption_def by simp
  next
    case False
    then have "P \<turnstile> (ttype T') <: (ttype T)"
      using 1 t'_implements_t unfolding subsumption_def by simp
    then show ?thesis using 1 ok subtype_int_parity by simp
  qed
next
  case a1: (2 P H T loc)
  then show ?thesis proof (cases "is_cap_type P (ttype T)")
    case True
    then have "ttype T' = ttype T" using t'_implements_t a1 unfolding subsumption_def by simp
    then show ?thesis using a1 ok label_same
      by (metis old.prod.inject prod.exhaust_sel) 
  next
    case False
    obtain obj where a2: "H loc = Some obj \<and> (P \<turnstile> (ClassT (HClass obj)) <: (ttype T')) \<and> is_obj_label_ok P obj T'" 
      using a1 ok by auto
    moreover have a3: "P \<turnstile> (ttype T') <: (ttype T)" 
      using a1 False t'_implements_t unfolding subsumption_def by simp
    ultimately have a4: "P \<turnstile> (ClassT (HClass obj)) <: (ttype T)" 
      using subtype_trans by blast
    have "\<not>is_cap_type P (ttype T')"
      using False a1 wfp a3 subtype_is_not_cap_type by simp
    then have "is_obj_label_ok P obj T"
      using a1 a2 False label_same unfolding is_obj_label_ok_def by auto
    then have "(is_value_ok P H T (href loc))" 
      using a2 a4 by simp
    then show ?thesis using a1 by simp
  qed
next
  case (3 P H t)
  then show ?thesis by simp
qed


lemma heap_access_ok:
  assumes wf: "wf_prog P"
  assumes ok: "is_value_ok P (heap S) ((ClassT t0),\<gamma>) (href l)"
  assumes field: "field P t0 f = Some fd"
  assumes nonstatic: "\<not>fstatic fd"
  assumes dynamic: "obj = the (heap S l)"
  assumes dynamicf: "v = the ((HFields obj) f)"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  shows "is_value_ok P (heap S) (intersect_label (ftype fd) (HLabel obj)) v"
proof -
  have a1: "heap S l = Some obj \<and> (P \<turnstile> (ClassT (HClass obj)) <: (ClassT t0)) \<and> is_obj_label_ok P obj ((ClassT t0),\<gamma>)"
    using ok dynamic by auto
  then have a2: "field P (HClass obj) f = Some fd"
    using field field_subtype wf by metis
  have "l \<in> dom(heap S) \<and> obj = the (heap S l)" 
    using a1 by auto
  then have "is_heapobj_ok P (heap S) obj"
    using a1 corr corr_def unfolding is_heap_ok_def by blast
  then have "(HFields obj) f = Some v \<and> is_value_ok P (heap S) (intersect_label (ftype fd) (HLabel obj)) v"
    using a2 dynamicf nonstatic unfolding is_heapobj_ok_def by fastforce 
  then show ?thesis by simp
qed


(* Begin parts of preservation proof. *)
definition is_expr_value_ok :: "prog \<Rightarrow> State \<Rightarrow> \<T> \<Rightarrow> v \<Rightarrow> bool"
  where "is_expr_value_ok P S T v \<equiv> (except S = None) \<longrightarrow> (is_value_ok P (heap S) (intersect_label T (privs S)) v)"

lemma is_expr_value_ok_value:
  assumes "is_value_ok P (heap S) (intersect_label T (privs S)) v"
  shows "is_expr_value_ok P S T v"
  unfolding is_expr_value_ok_def using assms by blast

lemma is_expr_value_ok_return:
  assumes "except S = None \<longrightarrow> retval S \<noteq> None"
  assumes "P M \<Gamma> \<^bold>\<turnstile> S"
  shows "is_expr_value_ok P S (msreturn M) (the (retval S))"
  using assms unfolding is_expr_value_ok_def corr_def is_retval_ok_def by simp

lemma preservation_expr_ref: 
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wf: "P M \<Gamma> \<turnstile> ref x : T"
  assumes op: "v = the (stack S x)"
  assumes wfp: "wf_prog P"
  shows "(P M \<Gamma> \<^bold>\<turnstile> S) \<and> (transition_ok S S) \<and> (is_expr_value_ok P S T v)"
proof -
  obtain T'  where a2: "(\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some T') \<and> (subsumption P (ttype T') (ttype T)) \<and> (tlabel T' = tlabel T)"
    using wf_expr_ref_intro wf by (metis prod.collapse) 
  then have "is_value_ok P (heap S) (intersect_label T' (privs S)) v" 
    using stack_access_ok op corr by metis 
  then have "is_value_ok P (heap S) (intersect_label T (privs S)) v" 
    using wfp is_value_ok_subsumption a2 intersect_label_type intersect_label_label by simp
  then have "is_expr_value_ok P S T v"
    using is_expr_value_ok_value by simp
  then show ?thesis using corr transition_ok_self by simp
qed

lemma preservation_expr_new:
  assumes op1: "v = href l"
  assumes op2: "l \<notin> dom (heap S)"
  assumes op3: "S' = S\<lparr>heap := (heap S)(l \<mapsto> new_object P cname (lbl \<inter> privs S))\<rparr>"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wf: "P M \<Gamma> \<turnstile> new lbl cname : T"
  assumes wfp: "wf_prog P"
  shows "(P M \<Gamma> \<^bold>\<turnstile> S') \<and> (transition_ok S S') \<and> (is_expr_value_ok P S' T v)"
proof -
  obtain c where a1: "(tlabel T = lbl) \<and> class P cname = Some c
                       \<and> (creq c) \<subseteq> (msreq M) \<and> (creq c) \<subseteq> (tlabel T)
                       \<and> (tlabel T) \<inter> the (grant P (mscname M)) \<subseteq> (the (grant P cname))
                       \<and> (subsumption P (ClassT cname) (ttype T))"
    using wf wf_expr_new_intro by (metis prod.collapse)
  have "creq (the (class P cname)) \<subseteq> (lbl \<inter> privs S)"
  proof -
    have "creq c \<subseteq> lbl" using a1 by metis
    (* combine (creq c) \<subseteq> (msreq M) and corr: (msreq M) \<subseteq> (privs S) *)
    moreover have "creq c \<subseteq> privs S" using a1 corr unfolding corr_def by auto
    ultimately show ?thesis using a1 by simp
  qed
  moreover have "(lbl \<inter> privs S) \<subseteq> the (grant P cname)"
    using a1 corr unfolding corr_def by auto
  ultimately have "is_value_ok P (heap S') (intersect_label ((ClassT cname),lbl) (privs S')) v" 
    using allocate_new_value_ok op1 op3 unfolding intersect_label_def by force 
  then have "is_value_ok P (heap S') (intersect_label T (privs S')) v"
    using wfp is_value_ok_subsumption a1 intersect_label_type intersect_label_label by simp
  then have "is_expr_value_ok P S' T v" 
    using a1 is_expr_value_ok_value by simp
  moreover have "P M \<Gamma> \<^bold>\<turnstile> S'" 
    using allocate_ok allocate_new_object_ok op2 op3 corr by metis
  moreover have "transition_ok S S'" 
    using allocate_extends_heap op2 op3 unfolding transition_ok_def by simp
  ultimately show ?thesis by simp
qed

lemma call_params_typecorrect:
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes call_context: "\<Gamma>' = call_lenvs P md"
  assumes mcompat: "mdecl_compatible decl md"
  assumes wf: "wf_method_call P \<Gamma> decl args \<gamma>0 (t',(tlabel T))"
  assumes wfm: "wf_mdecl P md"
  assumes lbls: "(\<forall>par\<in>(set (msig (mpar decl))). (tlabel par) \<inter> \<gamma>0 \<inter> (privs S) = (tlabel par) \<inter> privs')"
  assumes op7: "S0 = S\<lparr>stack := (stack S \<circ>\<^sub>m map_formalpar_to_args md args), retval:= None, privs := privs'\<rparr>"
  assumes privs1: "(msreq M0) \<subseteq> privs'"
  assumes privs2: "privs' \<subseteq> the (grant P (mscname M0))"
  shows "(P M0 \<Gamma>' \<^bold>\<turnstile> S0)"
proof -
  (* Show P \<Gamma>' \<^bold>\<turnstile> S0, by reasoning about parameters *)
  have "\<forall>x\<in>dom(map_of (mpar md)). var_corr P \<Gamma>' S0 x"
  proof
    fix formalpar
    (* Show that by definition of \<Gamma>', formalpar is typed to t. *)
    assume b1: "formalpar \<in> dom (map_of (mpar md))"
    then obtain T where b2: "map_of (mpar md) formalpar = Some T" by (meson domD)
    then have "\<Gamma>'\<lbrakk>formalpar\<rbrakk>\<^sub>v = Some T" using call_context call_lenvs_def by simp
    then obtain t \<gamma> where b3: "\<Gamma>'\<lbrakk>formalpar\<rbrakk>\<^sub>v = Some (t,\<gamma>) \<and> (t,\<gamma>) = T" by (metis prod.collapse)

    (* Get list index of this argument and obtain type, parameter name, argument information. *)
    obtain i where b4: "(mpar md) ! i = (formalpar,T) \<and> (i < length (mpar md))"
      using b2 by (meson in_set_conv_nth map_of_SomeD)   

   (* Show the type of the parameter in the runtime declaration and the
      static declaration are the same.  *)
    moreover have b5: "(msig (mpar decl)) ! i = T \<and> (i < length (msig (mpar decl)))" 
      using mcompat b4 mdecl_compatible_def by auto
    moreover obtain actualpar where b6: "(actualpar = args ! i) \<and> (i < length args)"
      using wf b5 wf_method_call_def by auto

    (* Show that due to static semantics, actualpar is type-correct to its declaration. *)
    ultimately have "\<Gamma>\<lbrakk>actualpar\<rbrakk>\<^sub>v = Some (intersect_label T \<gamma>0)" 
      using wf unfolding wf_method_call_def by auto
    then have b7: "\<Gamma>\<lbrakk>actualpar\<rbrakk>\<^sub>v = Some (t,\<gamma> \<inter> \<gamma>0)"
      using b3 unfolding intersect_label_def by (metis case_prod_conv)
    
    (* Prove using relationship between S0 formalpar and S actualpar *)
    have "unique_keys (mpar md)"
      using wfm unfolding wf_method_def wf_mdecl_def by simp
    moreover have "length (mpar md) = length args"
      using wf mcompat unfolding wf_method_call_def mdecl_compatible_def by (metis length_map) 
    ultimately have "(map_formalpar_to_args md args) formalpar = Some actualpar"
      using map_formalpar_to_args_match b4 b6 by fastforce 
    then have "stack S0 formalpar = stack S actualpar" 
      using op7 by simp

    (* show formal par will be type-correct under the new environment *)
    moreover obtain v where "stack S actualpar = Some v \<and> is_value_ok P (heap S) (intersect_label (t,\<gamma> \<inter> \<gamma>0) (privs S)) v"
      using corr b7 unfolding corr_def var_corr_def by blast
    moreover have "intersect_label (t,\<gamma> \<inter> \<gamma>0) (privs S) = intersect_label T (privs S0)"
    proof -
      have "T \<in> set (msig (mpar decl))" using b5 by auto
      then have "\<gamma> \<inter> \<gamma>0 \<inter> (privs S) = \<gamma> \<inter> (privs S0)" using lbls b3 op7 unfolding intersect_label_def by fastforce 
      then show ?thesis using b3 unfolding intersect_label_def by auto 
    qed
    ultimately have "stack S0 formalpar = Some v \<and> is_value_ok P (heap S0) (intersect_label T (privs S0)) v"
      using op7 by simp
    then show "var_corr P \<Gamma>' S0 formalpar" 
       using b3 unfolding var_corr_def call_lenvs_def by auto
  qed
  then have "(\<forall>x. var_corr P \<Gamma>' S0 x)" using call_context unfolding var_corr_def call_lenvs_def
    by (metis (mono_tags, lifting) domI id_apply) 
  moreover have "(is_heap_ok P (heap S0))"
    using corr op7 unfolding corr_def by simp
  ultimately show "P M0 \<Gamma>' \<^bold>\<turnstile> S0" using corr op7 privs1 privs2 unfolding corr_def is_retval_ok_def
    by simp
qed

(* Used to show a method exists at runtime and that 
   the statically-inferred  method signature of an object matches the signature at runtime *)
lemma method_correspondence:
  assumes wfp: "wf_prog P"
  assumes op: "(d, m) = the (cmethod P (HClass obj) mname)"
  assumes decl: "methoddecl P t0 mname = Some decl"
  assumes subtype: "(P \<turnstile> (ClassT (HClass obj)) <: t0)"
  shows "cmethod P (HClass obj) mname = Some (d,m) \<and> mdecl_compatible decl (mdecl m)"
proof -
  obtain rdecl where a1: "methoddecl P (ClassT (HClass obj)) mname = Some rdecl \<and> mdecl_compatible decl rdecl" 
    using methoddecl_subtype wfp decl subtype by metis
  then have a2: "cmethoddecl P (HClass obj) mname = Some rdecl" 
    unfolding methoddecl_def by simp
  then have a3: "cmethod P (HClass obj) mname = Some (d,m)" 
    using op unfolding cmethoddecl_def
    by (metis (no_types, lifting) map_comp_simps(1) option.collapse option.discI) 
  then have "(mdecl m) = rdecl" 
    using a2 unfolding cmethoddecl_def by auto   
  then show ?thesis 
    using a1 a3 by simp
qed

(* Shows an object exists at runtime, and its runtime type is a subtype of the static type. *)
lemma object_correspondence:
  assumes static: "\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some T"  
  assumes object_type: "(\<forall>t. (ttype T) \<noteq> (ValT t))"
  assumes op1: "a = the (stack S x)"
  assumes op2: "a \<noteq> v.null"
  assumes op3: "l = the_href a"
  assumes op4: "obj = the (heap S l)"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  shows "a = (href l) \<and> heap S l = Some obj \<and> (P \<turnstile> (ClassT (HClass obj)) <: (ttype T)) \<and> is_obj_label_ok P obj (intersect_label T (privs S))"
proof -
  have a1: "is_value_ok P (heap S) (intersect_label T (privs S)) a" 
    using stack_access_ok op1 corr static by (metis)
  moreover have a2: "a = (href l)" 
    using op2 op3 object_type intersect_label_type a1 by (metis is_value_ok.elims(2) the_href.simps(1)) (* given t0 \<noteq> IntT, a \<noteq> null *)
  moreover have a3: "heap S l = Some obj \<and> (P \<turnstile> (ClassT (HClass obj)) <: (ttype T))" 
    using a1 a2 op4 intersect_label_type by (metis is_value_ok_href option.sel)
  moreover have a4: "is_obj_label_ok P obj (intersect_label T (privs S))" 
    using a1 a2 op4 intersect_label_label by (metis is_value_ok_href option.sel)
  ultimately show ?thesis by simp
qed

(*lemma no_retval_corr:
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  shows "P M0 \<Gamma> \<^bold>\<turnstile> (S\<lparr>retval := None\<rparr>)"
proof -
  have "\<And>P H T. is_retval_ok P H T None" 
    unfolding is_retval_ok_def by simp
  then show ?thesis using corr unfolding corr_def by (simp add: var_corr_def) 
qed*)
lemma mreq_less_than_object_label:
  assumes wfp: "wf_prog P"
  assumes method: "cmethod P (HClass obj) mname = Some (d,m)"
  assumes nonstatic: "\<not>mstatic (mdecl m)"
  assumes cls: "is_class P (HClass obj)"
  assumes olbl: "is_obj_label_ok P obj T"
  shows "mreq m \<subseteq> (HLabel obj)"
proof -
  have "((HClass obj),d)\<in>(subclass P)"
    using method_declaring_class wfp cls method by simp
  then obtain cl dcl where a1: "class P (HClass obj) = Some cl \<and> class P d = Some dcl \<and> creq dcl \<subseteq> creq cl"
    using subclass_creq wfp cls by blast 
  then have "class P d = Some dcl \<and> wf_method P (d,dcl) m"
    using prog_wf_method wfp cls method by fastforce
  moreover have "mstmt m \<noteq> None"
    using cls method prog_wf_mstmt_exists wfp by fastforce
  ultimately have a2: "mreq m \<subseteq> creq dcl"
    unfolding wf_method_def using nonstatic by auto
  then have "mreq m \<subseteq> (HLabel obj)"
    using olbl a1 unfolding is_obj_label_ok_def by auto
  then show ?thesis .
qed


lemma grant_more_than_object_label:
  assumes wfp: "wf_prog P"
  assumes method: "cmethod P (HClass obj) mname = Some (d,m)"
  assumes cls: "is_class P (HClass obj)"
  assumes olbl: "is_obj_label_ok P obj T"
  shows "(HLabel obj) \<subseteq> the (grant P d)"
proof -
  have "((HClass obj),d)\<in>(subclass P)"
    using method_declaring_class wfp cls method by simp
  then have "(the (grant P (HClass obj))) \<subseteq> (the (grant P d))"
    using wfp grant_subclass_mono by simp
  moreover have "(HLabel obj) \<subseteq> (the (grant P (HClass obj)))"
    using olbl unfolding is_obj_label_ok_def by simp
  ultimately show ?thesis by auto
qed

lemma call_params_label_invariant:
  assumes ok: "is_obj_label_ok P obj (intersect_label (t0,\<gamma>0) (privs S))"
  assumes meth: "methoddecl P t0 mname = Some decl"
  shows "(\<forall>par\<in>(set (msig (mpar decl))). (tlabel par) \<inter> \<gamma>0 \<inter> (privs S) = (tlabel par) \<inter> (HLabel obj)) \<and> 
         (tlabel (mret decl)) \<inter> \<gamma>0 \<inter> (privs S) = (tlabel (mret decl)) \<inter> (HLabel obj)"
proof (cases "is_cap_type P t0")
  case True
  then obtain ifname where a1: "t0 = (IfaceT ifname)"
    using True by (metis \<tau>.exhaust is_cap_type.simps(1) is_cap_type.simps(2)) 
  have "imethoddecl P ifname mname = Some decl"
    using a1 meth unfolding methoddecl_def by simp
  then have "sum_method_labels decl \<subseteq> cap_label P ifname"
    unfolding cap_label_def by (metis (no_types, lifting) Sup_upper domI image_iff le_supI2 option.sel) 
  then have "(\<forall>par\<in>(set (msig (mpar decl))). (tlabel par) \<subseteq> cap_label P ifname) 
             \<and> (tlabel (mret decl)) \<subseteq> cap_label P ifname"
    unfolding sum_method_labels_def by auto
  (* from is_obj_label_ok *)
(*  moreover have "cap_label P ifname = \<gamma>0 \<inter> (privs S) \<and> cap_label P ifname \<subseteq> (HLabel obj)"
    using a1 True ok intersect_label_label intersect_label_type unfolding is_obj_label_ok_def by simp*)
  moreover have "(cap_label P ifname) \<inter> (HLabel obj) = \<gamma>0 \<inter> (privs S)"
    using a1 True ok intersect_label_label intersect_label_type unfolding is_obj_label_ok_def by simp
  ultimately show "(\<forall>par\<in>(set (msig (mpar decl))). (tlabel par) \<inter> \<gamma>0 \<inter> (privs S) = (tlabel par) \<inter> (HLabel obj))\<and> 
         tlabel (mret decl) \<inter> \<gamma>0 \<inter> (privs S) = tlabel (mret decl) \<inter> (HLabel obj)"
    by blast
next
  case False
  then have "(HLabel obj) = \<gamma>0 \<inter> (privs S)"
    using ok intersect_label_label intersect_label_type unfolding is_obj_label_ok_def by simp
  then show ?thesis by blast
qed

(* Show that:
  - The initial stack, S0, is type-correct with respect to the environment of the method being called, and
  - The statement that is the method body is type-correct within the same context *)
lemma calli_prems:
  assumes op1: "a = the (stack S x)"
  assumes op2: "l = the_href a"
  assumes op3: "a \<noteq> v.null"
  assumes op4: "obj = the (heap S l)"
  assumes op5: "(d, m) = the (cmethod P (HClass obj) mname)"
  assumes op6: "s = the (mstmt m)"
  assumes op7: "S0 = S\<lparr>stack := (stack S \<circ>\<^sub>m map_formalpar_to_args (mdecl m) args)(This \<mapsto> a), retval := None, privs := HLabel obj\<rparr>"
  assumes wf: "P M \<Gamma> \<turnstile> calli x mname args : T"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wfp: "wf_prog P"
  assumes call_contextm: "M0 = call_menv d m"
  assumes call_contextl: "\<Gamma>0 = call_lenvi P d (mdecl m)"
  shows "(P M0 \<Gamma>0 \<^bold>\<turnstile> S0) \<and> (P M0 \<Gamma>0 \<turnstile> s \<bullet>)"
proof -
  obtain t0 \<gamma>0 decl t' where a1: "(\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some (t0,\<gamma>0)) \<and> methoddecl P t0 mname = Some decl \<and>
                        is_type P t0 \<and> (\<forall>t. t0 \<noteq> (ValT t)) \<and> \<not>mstatic decl \<and>
                        wf_method_call P \<Gamma> decl args \<gamma>0 (t',(tlabel T)) \<and> (subsumption P t' (ttype T))"
    using wf wf_expr_calli_intro by (metis prod.collapse) 
                           
  (* Infer the the object pointed to by x exists, and has a runtime type compatible with the static type t0. *)
  have a2: "a = (href l) \<and> heap S l = Some obj \<and> (P \<turnstile> (ClassT (HClass obj)) <: t0) \<and> is_obj_label_ok P obj (intersect_label (t0,\<gamma>0) (privs S))"
    using object_correspondence a1 op1 op2 op3 op4 corr by (metis fst_conv) 

  (* Infer the method exists at runtime and that its signature is compatible *)
  then have a6: "cmethod P (HClass obj) mname = Some (d,m) \<and> mdecl_compatible decl (mdecl m)"
    using method_correspondence wfp op5 a1 by blast

  (* Show the statement that isthe method body is well-formed. *)
  have a8: "is_class P (HClass obj)" using subtype_exists a1 a2 is_type.simps by blast  (* runtime type exists *)
  then obtain dcl where a9: "class P d = Some dcl \<and> wf_method P (d,dcl) m" using prog_wf_method a6 wfp by blast
  moreover have "mstmt m = Some s" using prog_wf_mstmt_exists wfp op6 a8 a6 by fastforce (* body exists *)
  moreover have a10: "\<not>mstatic (mdecl m)" using a6 a1 unfolding mdecl_compatible_def by simp
  ultimately have a11: "P M0 \<Gamma>0 \<turnstile> s \<bullet>" unfolding wf_method_def using call_contextm call_contextl by simp

  (* Show the initial stack for statement s is well-formed. *)
  moreover define S0' where "S0' = S\<lparr>stack := (stack S \<circ>\<^sub>m map_formalpar_to_args (mdecl m) args), retval := None, privs := HLabel obj\<rparr>"
  moreover define \<Gamma>0' where "\<Gamma>0' = call_lenvs P (mdecl m)"
  moreover have "wf_mdecl P (mdecl m)" using a9 unfolding wf_method_def by simp
  moreover have "(\<forall>par\<in>(set (msig (mpar decl))). (tlabel par) \<inter> \<gamma>0 \<inter> (privs S) = (tlabel par) \<inter> (HLabel obj))" using call_params_label_invariant a1 a2 by metis
  moreover have "(msreq M0) \<subseteq> HLabel obj" using mreq_less_than_object_label call_contextm wfp a6 a8 a2 a10 unfolding call_menv_def by fastforce 
  moreover have "HLabel obj \<subseteq> the (grant P (mscname M0))" using grant_more_than_object_label wfp a6 a8 a2 call_contextm unfolding call_menv_def by fastforce 
  ultimately have a12: "P M0 \<Gamma>0' \<^bold>\<turnstile> S0'" using corr a6 a1 call_params_typecorrect by blast

  have "(P \<turnstile> (ClassT (HClass obj)) <: (ClassT d))" using method_declaring_class_subtype a6 a8 wfp by blast
  moreover have "is_obj_label_ok P obj ((ClassT d),(privs S0))" using op7 a2 unfolding is_obj_label_ok_def by simp
  ultimately have "is_value_ok P (heap S0) (intersect_label ((ClassT d),UNIV) (privs S0)) a" using a2 op7 unfolding intersect_label_def by auto
  then have "P M0 \<Gamma>0 \<^bold>\<turnstile> S0" using a12 S0'_def \<Gamma>0'_def op7 call_contextl unfolding call_lenvi_def corr_def var_corr_def by simp
  then show ?thesis using a11 by simp
qed

lemma is_expr_value_ok_subsumption:
  assumes wfp: "wf_prog P"
  assumes ok: "is_expr_value_ok P S' T' v"
  assumes subsumption: "subsumption P (ttype T') (ttype T)"
  assumes label: "tlabel T' = tlabel T"
  shows "is_expr_value_ok P S' T v"
  using wfp ok subsumption label is_value_ok_subsumption intersect_label_type intersect_label_label
  unfolding is_expr_value_ok_def by metis

lemma preservation_call_return:
  assumes wfp: "wf_prog P"
  assumes corr: "P M0 \<Gamma>0 \<^bold>\<turnstile> S1" (* after state of method correct w.r.t context *)
  assumes heap: "heap S1 = heap S'"
  assumes except: "except S1 = except S'" (* required relationship between stack after method body and final stack *)
  assumes M0_def: "M0 = call_menv d rdecl" (* context based on runtime method declaration *)
  assumes mcompat: "mdecl_compatible decl (mdecl rdecl)" (* runtime and compile-time method declaration compatible *)
  assumes T': "T' = intersect_label (mret decl) \<gamma>0" (* static type of method return *)
  assumes subsumption: "subsumption P (ttype T') (ttype T)" (* type of method return may be a subtype of the expression, due to subsumption *)
  assumes label: "(tlabel T) = (tlabel T')"
  assumes label_inv: "(tlabel T') \<inter> (privs S') = (tlabel (mret decl)) \<inter> (privs S1)"
  assumes retval_if_noexcept: "except S1 = None \<longrightarrow> retval S1 \<noteq> None" 
  assumes v: "v = the (retval S1)"
  shows "is_expr_value_ok P S' T v"
proof -
  have "is_expr_value_ok P S1 (msreturn M0) v" (* inferred from type-correctness of final state *)
    using is_expr_value_ok_return retval_if_noexcept corr v by metis
  then have "is_expr_value_ok P S1 (mret decl) v" (* by method compatibility *)
    using call_menv_def fst_conv M0_def mcompat mdecl_compatible_def by simp
  moreover have "(intersect_label (mret decl) (privs S1)) = (intersect_label T' (privs S'))"
    using intersect_label_label intersect_label_type label_inv T' by (simp add: prod_eq_iff)
  ultimately have b1: "is_expr_value_ok P S' T' v" (* by label relations *)
    using heap except unfolding is_expr_value_ok_def by simp
  (* the return type of the expression (after subsumption) may be a supertype of the method return type *)
  then show ?thesis 
    using b1 is_expr_value_ok_subsumption wfp subsumption intersect_label_type label by metis
qed

(* Shows type-correctness is maintained over the call to an instance method. We show that:
    The final state is consistent with the types of the environment.
    The heap in the state only extends itself.
    The return value is type-correct with the return type of the method (provided no exception was thrown.)  *)
lemma preservation_expr_calli:
  assumes op1: "a = the (stack S x)"
  assumes op2: "l = the_href a"
  assumes op3: "a \<noteq> v.null"
  assumes op4: "obj = the (heap S l)"
  assumes op5: "(d, m) = the (cmethod P (HClass obj) mname)"
  assumes op6: "s = the (mstmt m)"
  assumes s0: "S0 = S\<lparr>stack := (stack S \<circ>\<^sub>m map_formalpar_to_args (mdecl m) args)(This \<mapsto> a), retval := None, privs := (HLabel obj)\<rparr>"
  assumes s': "S' = S1\<lparr>stack := stack S, retval := retval S, privs := privs S\<rparr>"
  assumes v: "v = the (retval S1)"
  assumes "P \<turnstile> \<langle>s | S0\<rangle> \<rightarrow>\<^sub>s \<langle>S1\<rangle>"
  (* induction hypothesis *)
  assumes hyp: "\<And>M \<Gamma>. (P M \<Gamma> \<^bold>\<turnstile> S0) \<and> (P M \<Gamma> \<turnstile> s \<bullet>) \<Longrightarrow> (P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S0 S1"
  assumes retval_if_noexcept: "except S1 = None \<longrightarrow> retval S1 \<noteq> None"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wfp: "wf_prog P"
  assumes wf: "P M \<Gamma> \<turnstile> calli x mname args : T"
  shows "(P M \<Gamma> \<^bold>\<turnstile> S') \<and> transition_ok S S' \<and> is_expr_value_ok P S' T v"
proof -
  define M0 where "M0 = call_menv d m"
  moreover define \<Gamma>0 where "\<Gamma>0 = call_lenvi P d (mdecl m)"
  ultimately have a1: "(P M0 \<Gamma>0 \<^bold>\<turnstile> S0) \<and> (P M0 \<Gamma>0 \<turnstile> s \<bullet>)" using calli_prems assms by metis
  then have a2: "(P M0 \<Gamma>0 \<^bold>\<turnstile> S1) \<and> transition_ok S0 S1" using hyp by metis
  then have a3: "(P M \<Gamma> \<^bold>\<turnstile> S')" using heap_extends_corr s0 s' corr unfolding transition_ok_def by metis
  moreover have "transition_ok S S'" using a2 s0 s' unfolding heap_extends_def transition_ok_def by auto
  moreover have "is_expr_value_ok P S' T v"
  proof -
    (* infer what P M \<Gamma> \<turnstile> calli x mname args : T means
       t' is the actual method return type, (ttype T) is the subsumed type.
       it is given that T' = (intersect_label (mret decl) (tlabel T0))  *)
    obtain T0 decl T' where b2: "(\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some T0) \<and> methoddecl P (ttype T0) mname = Some decl \<and>
                        is_type P (ttype T0) \<and> (\<forall>t. ttype T0 \<noteq> (ValT t)) \<and> \<not>mstatic decl \<and>
                        wf_method_call P \<Gamma> decl args (tlabel T0) T' \<and> (subsumption P (ttype T') (ttype T)) \<and> (tlabel T' = tlabel T)"
      using wf wf_expr_calli_intro by (metis fst_conv snd_conv prod.collapse)
    (* object exists and subtype of static type t0, label satisfies invariant *)
    have b3: "(P \<turnstile> (ClassT (HClass obj)) <: (ttype T0)) \<and> is_obj_label_ok P obj (intersect_label T0 (privs S))"
      using object_correspondence b2 op1 op2 op3 op4 corr by blast
   (* method exists and compatible with static definition *)
    then have b4: "mdecl_compatible decl (mdecl m)"
      using method_correspondence wfp op5 b2 by metis
    moreover have "T' = intersect_label (mret decl) (tlabel T0)" using b2 unfolding wf_method_call_def by simp (* expanding static wellformedness defn *)
    moreover have "heap S1 = heap S' \<and> except S1 = except S'" using s' by simp
    moreover have "(subsumption P (ttype T') (ttype T)) \<and> (tlabel T' = tlabel T)" using b2 by simp
    (* show labels are consistent *)
    moreover have "(tlabel T') \<inter> (privs S') = (tlabel (mret decl)) \<inter> (privs S1)"
    proof -
      have "(tlabel (mret decl)) \<inter> (tlabel T0) \<inter> (privs S) = (tlabel (mret decl)) \<inter> (HLabel obj)"
        using call_params_label_invariant b3 b2 by (metis prod.collapse) 
      moreover have "privs S = privs S'" using s' by simp
      moreover have "privs S0 = (HLabel obj)" using s0 by simp
      moreover have "privs S1 = privs S0" using a2 unfolding transition_ok_def by simp
      moreover have "tlabel T' = tlabel (mret decl) \<inter> (tlabel T0)" using b2 intersect_label_label unfolding wf_method_call_def by simp
      ultimately show ?thesis by auto
    qed
    ultimately show ?thesis using wfp preservation_call_return a2 M0_def retval_if_noexcept v by metis
  qed
  ultimately show ?thesis by simp 
qed


(* Show starting stack of a static method call, and the statement to be executed, are type-correct.*)
lemma calls_prems:
  assumes op5: "(d, m) = the (cmethod P c mname)"
  assumes op6: "s = the (mstmt m)"
  assumes op7: "S0 = S\<lparr>stack := (stack S \<circ>\<^sub>m map_formalpar_to_args (mdecl m) args), retval := None, privs := (privs S) \<inter> lbl\<rparr>"
  assumes wf: "P M \<Gamma> \<turnstile> calls c mname lbl args : T"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wfp: "wf_prog P"
  assumes call_contextm: "M0 = call_menv d m"
  assumes call_contextl: "\<Gamma>0 = call_lenvs P (mdecl m)"
  shows "(P M0 \<Gamma>0 \<^bold>\<turnstile> S0) \<and> (P M0 \<Gamma>0 \<turnstile> s \<bullet>)"
proof -
   obtain t' where a1: "is_class P c \<and> cmethod P c mname = Some (d,m) \<and> mstatic (mdecl m) \<and>
                               wf_method_call P \<Gamma> (mdecl m) args lbl (t',(tlabel T)) \<and> (mreq m) \<subseteq> (msreq M)
                               \<and> lbl \<inter> the (grant P (mscname M)) \<subseteq> the (grant P c)
                               \<and> (mreq m) \<subseteq> lbl \<and> (subsumption P t' (ttype T))"
     using wf wf_expr_calls_intro op7 by (metis (mono_tags, lifting) op5 option.sel prod.collapse snd_conv)
  
  (* Show the statement that is the method body is well-formed. *)
  obtain dCl where a10: "class P d = Some dCl \<and> wf_method P (d,dCl) m" using prog_wf_method a1 wfp by blast
  moreover have "mstmt m = Some s" using prog_wf_mstmt_exists wfp op6 a1 by fastforce (* body exists *)
  moreover have "mstatic (mdecl m)" using a1 by simp
  ultimately have a11: "P M0 \<Gamma>0 \<turnstile> s \<bullet>" unfolding wf_method_def using call_contextm call_contextl by simp

  (* Show the initial stack for statement s is well-formed. *)
  have "wf_mdecl P (mdecl m)" using a10 unfolding wf_method_def by simp
  moreover have "(\<forall>par\<in>(set (msig (mpar (mdecl m)))). (tlabel par) \<inter> lbl \<inter> (privs S) = (tlabel par) \<inter> ((privs S) \<inter> lbl))" by blast
 (* for static methods, there is no difference between the signature we type-check against and the one we call, not even
    non-functional differences (method parameters) *)
  moreover have "mdecl_compatible (mdecl m) (mdecl m)" unfolding mdecl_compatible_def by simp
  moreover have "msreq M0 \<subseteq> (privs S) \<inter> lbl"
  proof -
    have "msreq M0 \<subseteq> (msreq M) \<inter> lbl" using a1 call_contextm call_menv_def by auto (* typing rules *)
    moreover have "(msreq M) \<subseteq> (privs S)" using corr unfolding corr_def by simp (* by invariant *)
    ultimately show ?thesis by auto
  qed
  moreover have "((privs S) \<inter> lbl) \<subseteq> the (grant P (mscname M0))"
  proof -
    have "(c,d) \<in> (subclass P)"
      using wfp method_declaring_class a1 by metis
    then have "the (grant P c) \<subseteq> the (grant P d)"
      using wfp grant_subclass_mono by simp
    moreover have "(privs S) \<inter> lbl \<subseteq> the (grant P c)"
      using corr a1 unfolding corr_def by auto
    ultimately show ?thesis using call_contextm call_menv_def by auto
  qed
  ultimately have a12: "P M0 \<Gamma>0 \<^bold>\<turnstile> S0" using op7 corr a1  call_contextl call_params_typecorrect by metis
  then show ?thesis using a11 by simp
qed

lemma preservation_expr_calls:
  assumes op5: "(d, m) = the (cmethod P c mname)"
  assumes "P \<turnstile> \<langle>s | S0\<rangle> \<rightarrow>\<^sub>s \<langle>S1\<rangle>"
  assumes hyp: "\<And>M \<Gamma>. (P M \<Gamma> \<^bold>\<turnstile> S0) \<and> (P M \<Gamma> \<turnstile> s \<bullet>) \<Longrightarrow> (P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S0 S1"
  assumes "s = the (mstmt m)"
  assumes s0: "S0 = S\<lparr>stack := stack S \<circ>\<^sub>m map_formalpar_to_args (mdecl m) args, retval := None, privs := (privs S) \<inter> lbl\<rparr>"
  assumes s': "S' = S1\<lparr>stack := stack S, retval := retval S, privs := privs S\<rparr>"
  assumes retval_if_noexcept: "except S1 = None \<longrightarrow> retval S1 \<noteq> None"
  assumes v: "v = the (retval S1)"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wfp: "wf_prog P"
  assumes wf: "P M \<Gamma> \<turnstile> calls c mname lbl args : T"
  shows "(P M \<Gamma> \<^bold>\<turnstile> S') \<and> transition_ok S S' \<and> is_expr_value_ok P S' T v"
proof -
  define M0 where "M0 = call_menv d m"
  moreover define \<Gamma>0 where "\<Gamma>0 = call_lenvs P (mdecl m)"
  ultimately have a1: "(P M0 \<Gamma>0 \<^bold>\<turnstile> S0) \<and> (P M0 \<Gamma>0 \<turnstile> s \<bullet>)" using calls_prems assms by metis
  then have a2: "(P M0 \<Gamma>0 \<^bold>\<turnstile> S1) \<and> transition_ok S0 S1" using hyp by metis
  then have a3: "(P M \<Gamma> \<^bold>\<turnstile> S')" using heap_extends_corr s0 s' corr unfolding transition_ok_def by metis
  moreover have "transition_ok S S'" using a2 s0 s' unfolding transition_ok_def heap_extends_def by auto
  moreover have "is_expr_value_ok P S' T v"
  proof -
    (* infer what P M \<Gamma> \<turnstile> calls c mname lbl args : T means *)
    obtain  T' where b2: "is_class P c \<and> cmethod P c mname = Some (d,m) \<and> mstatic (mdecl m) \<and>
                               wf_method_call P \<Gamma> (mdecl m) args lbl T' \<and> (mreq m) \<subseteq> (msreq M)
                               \<and> (mreq m) \<subseteq> lbl \<and> (subsumption P (ttype T') (ttype T)) \<and> (tlabel T' = tlabel T)"
          using wf wf_expr_calls_intro by (metis (mono_tags, lifting) op5 option.sel prod.collapse fst_conv snd_conv)
  
    then have b3: "mdecl_compatible (mdecl m) (mdecl m)" (* static definition and runtime definition the same for static methods *)
     using mdecl_compatible_def by simp
    moreover have "T' = intersect_label (mret (mdecl m)) lbl" using b2 unfolding wf_method_call_def by simp (* expanding wellformedness defn *)
    moreover have "heap S1 = heap S' \<and> except S1 = except S'" using s' by simp
    moreover have "(subsumption P (ttype T') (ttype T)) \<and> (tlabel T' = tlabel T)" using b2 by simp
    (* show labels are consistent *)
    moreover have "(tlabel T') \<inter> (privs S') = (tlabel (mret (mdecl m))) \<inter> (privs S1)"
    proof -
      have "privs S1 = privs S0" using a2 unfolding transition_ok_def by simp
      then have "privs S1 = privs S' \<inter> lbl" using s0 s' by simp
      moreover have "tlabel T' = tlabel (mret (mdecl m)) \<inter> lbl" using b2 intersect_label_label unfolding wf_method_call_def by simp
      ultimately show ?thesis by auto
    qed
    ultimately show ?thesis using wfp preservation_call_return a2 M0_def retval_if_noexcept v by metis
  qed
  ultimately show ?thesis by simp 
qed

lemma preservation_expr_cast:
  assumes op1: "P \<turnstile> \<langle>e | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S'\<rangle>"
  assumes hyp: "\<And>M \<Gamma> T. (P M \<Gamma> \<^bold>\<turnstile> S) \<and> (P M \<Gamma> \<turnstile> e : T) \<longrightarrow> (P M \<Gamma> \<^bold>\<turnstile> S') \<and> transition_ok S S' \<and> is_expr_value_ok P S' T v"
  assumes op2: "case v of href l \<Rightarrow> hobj = the (heap S' l) \<and> (P \<turnstile> ClassT (HClass hobj) <: tcast) | (num n) \<Rightarrow> tcast = ValT IntT"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wf: "P M \<Gamma> \<turnstile> cast tcast e : T"
  assumes wfp: "wf_prog P"
  shows "(P M \<Gamma> \<^bold>\<turnstile> S') \<and> transition_ok S S' \<and> is_expr_value_ok P S' T v"
proof -
  define Tcast where "Tcast \<equiv> (tcast, tlabel T)"
  obtain T' where a1: "(P M \<Gamma> \<turnstile> e : T') \<and> \<not>is_cap_type P (ttype T') 
                      \<and> \<not>is_cap_type P (ttype Tcast) \<and> (subsumption P (ttype Tcast) (ttype T)) \<and> (tlabel T' = tlabel T)" 
    using wf wf_expr_cast_intro Tcast_def by fastforce 
  then have a2: "(P M \<Gamma> \<^bold>\<turnstile> S') \<and> transition_ok S S' \<and> is_expr_value_ok P S' T' v"
    using hyp corr by metis 
  (* show the value is type correct to Tcast *)
  have "is_expr_value_ok P S' Tcast v"
  proof (cases v)
    case b1: (href l)
    then have "hobj = the (heap S' l) \<and> (P \<turnstile> ClassT (HClass hobj) <: (ttype Tcast))" using op2 Tcast_def by auto
    moreover have "is_expr_value_ok P S' T' v" using a2 by simp
    moreover have "tlabel Tcast = tlabel T'" using a1 Tcast_def by simp
    ultimately show ?thesis 
      using is_value_ok_valid_object_cast a1 b1 a2 intersect_label_label intersect_label_type 
      unfolding is_expr_value_ok_def by metis
  next
    case null
    then show ?thesis unfolding is_expr_value_ok_def by simp
  next
    case (num x3)
    then have "(ttype Tcast) = (ValT IntT)" using op2 Tcast_def by simp
    then show ?thesis unfolding is_expr_value_ok_def 
      using num intersect_label_type by auto
  qed
  (* show the value is type-correct to the supertype T by subsumption *)
  then have "is_expr_value_ok P S' T v" 
    using wfp a1 is_expr_value_ok_subsumption Tcast_def by simp
  then show ?thesis using a2 by simp
qed

lemma preservation_expr_const:
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wf: "P M \<Gamma> \<turnstile> const k : T"
  assumes op: "case k of k.null \<Rightarrow> v = v.null | k.num n \<Rightarrow> v = v.num n"
  shows "(P M \<Gamma> \<^bold>\<turnstile> S) \<and> transition_ok S S \<and> is_expr_value_ok P S T v"
proof -
  obtain t' where a1: "(case k of k.null \<Rightarrow> (\<forall>vt. t' \<noteq> (ValT vt)) | k.num n \<Rightarrow> (t' = ValT IntT)) \<and> (subsumption P t' (ttype T))" 
    using wf wf_expr_const_intro by (metis prod.collapse)
  have "is_expr_value_ok P S T v"
  proof (cases k)
    case null
    then have "v = v.null \<and> (\<forall>vt. t' \<noteq> (ValT vt))" using op a1 by simp
    then show ?thesis unfolding is_expr_value_ok_def by simp (* null is always OK *)
  next
    case (num n)
    then have b1: "v = v.num n \<and> (t' = ValT IntT)" using op a1 by simp 
    moreover have "ttype T = (ValT IntT)"
    proof (cases "is_cap_type P (ttype T)")
      case True (* Not possible *)
      then show ?thesis using a1 b1 unfolding subsumption_def by simp 
    next
      case False
      then show ?thesis using subtype_int_parity a1 b1 unfolding subsumption_def by auto
    qed     
    ultimately show ?thesis using intersect_label_type unfolding is_expr_value_ok_def by simp
  qed
  then show ?thesis using corr transition_ok_self by auto
qed

lemma preservation_expr_fieldacci:
  assumes op1: "a = the (stack S x)"
  assumes op2: "a \<noteq> v.null"
  assumes op3: "l = the_href a"
  assumes op4: "obj = the (heap S l)"
  assumes op5: "v = the (HFields obj f)"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wf: "P M \<Gamma> \<turnstile> fieldacci x f : T"
  assumes wfp: "wf_prog P"
  shows "(P M \<Gamma> \<^bold>\<turnstile> S) \<and> transition_ok S S \<and> is_expr_value_ok P S T v"
proof -
  obtain T' where a1: "(wf_fieldi_access P \<Gamma> x f T' \<and> (subsumption P (ttype T') (ttype T)) \<and> (tlabel T' = tlabel T))" 
    using wf wf_expr_fieldacci_intro by (metis prod.collapse fst_conv snd_conv)
  then obtain c \<gamma>0 fdecl where a2: "(\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some ((ClassT c),\<gamma>0)) \<and> field P c f = Some fdecl \<and>
                                    \<not>fstatic fdecl \<and> T' = intersect_label (ftype fdecl) \<gamma>0"
    unfolding wf_fieldi_access_def by blast
  have a3: "a = (href l) \<and> heap S l = Some obj \<and> (P \<turnstile> (ClassT (HClass obj)) <: (ClassT c)) \<and> is_obj_label_ok P obj (intersect_label ((ClassT c),\<gamma>0) (privs S))"
    using object_correspondence a2 op1 op2 op3 op4 corr by (metis \<tau>.simps(5) fst_conv)
  then have "is_value_ok P (heap S) ((ClassT c),\<gamma>0 \<inter> (privs S)) (href l)" (* object ok *)      
    using intersect_label_type intersect_label_label by (simp add: intersect_label_def) 
  then have "is_value_ok P (heap S) (intersect_label (ftype fdecl) (HLabel obj)) v" (* field value ok *)
    using heap_access_ok wfp a2 op4 op5 corr by simp
  moreover have "\<gamma>0 \<inter> (privs S) = (HLabel obj)" (* We do not have to consider the label relationship in the capability case as fields can only be accessed on classes. *)
    using a3 unfolding is_obj_label_ok_def by (simp add: intersect_label_label intersect_label_type) 
  ultimately have "is_value_ok P (heap S) (intersect_label T' (privs S)) v"
    using intersect_label_vary a2 a3 by metis
  then have "is_value_ok P (heap S) (intersect_label T (privs S)) v"
    using wfp is_value_ok_subsumption a1 intersect_label_label intersect_label_type by metis
  then have "is_expr_value_ok P S T v"
    unfolding is_expr_value_ok_def by simp
  then show ?thesis using corr transition_ok_self by auto
qed

lemma preservation_expr_fieldaccs:
  assumes op1: "classStatics = the (globals S c)"
  assumes op2: "v = the (classStatics f)"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wf: "P M \<Gamma> \<turnstile> fieldaccs c f : T"
  assumes wfp: "wf_prog P"
  shows "(P M \<Gamma> \<^bold>\<turnstile> S) \<and> transition_ok S S \<and> is_expr_value_ok P S T v"
proof -
  obtain T' where a1: "(wf_fields_access P M c f T') \<and> (subsumption P (ttype T') (ttype T)) \<and> (tlabel T' = tlabel T)" 
    using wf wf_expr_fieldaccs_intro by (metis prod.collapse fst_conv snd_conv)
  then obtain fdecl where a2: "is_class P c \<and> field P c f = Some fdecl \<and> fstatic fdecl \<and> 
                                (T' = (ftype fdecl) \<and> (tlabel (ftype fdecl)) \<subseteq> (msreq M))"
    unfolding wf_fields_access_def by blast
  then have "is_value_ok P (heap S) T' v"
    using globals_access_ok op1 op2 corr by metis 
  then have "is_value_ok P (heap S) T v"
    using is_value_ok_subsumption a1 wfp by simp
  moreover have "T = intersect_label T (privs S)" 
  proof -
    have "tlabel T \<subseteq> (msreq M)" using a1 a2 by simp
    moreover have "(msreq M) \<subseteq> (privs S)" using corr unfolding corr_def by simp
    ultimately show ?thesis using intersect_label_label intersect_label_type
      by (metis Int_absorb2 order_trans prod_eqI) 
  qed
  ultimately have "is_expr_value_ok P S T v" 
    unfolding is_expr_value_ok_def by simp
  then show ?thesis using corr transition_ok_self by simp
qed



lemma is_value_ok_wrap:
  assumes wfp: "wf_prog P"
  assumes ok: "is_value_ok P H T' v"
  assumes t'_implements_t: "(P \<turnstile> (ttype T') <: (ttype T))"
  assumes label: "(tlabel T') \<inter> (cap_label P cbname) = (tlabel T)"
  assumes reqs: "\<not>is_cap_type P (ttype T') \<longrightarrow> (superinterface_set P cbname) \<subseteq> (tlabel T')" (* in principle not requried if source type is a capability *)
  assumes cap: "is_cap P cbname \<and>  (ttype T) = (IfaceT cbname)"
  shows "is_value_ok P H T v"
proof (cases "(P, H, T, v)" rule: is_value_ok.cases)
  case (1 P H t v)
  (* Case not actually possible, because T is a capability. *)
  then show ?thesis using 1 ok t'_implements_t subtype_int_parity by simp
next
  case a1: (2 P H T loc)
  obtain obj where a2: "H loc = Some obj \<and> (P \<turnstile> (ClassT (HClass obj)) <: (ttype T')) \<and> is_obj_label_ok P obj T'" 
    using a1 ok by auto
  moreover have a3: "P \<turnstile> (ClassT (HClass obj)) <: (ttype T)" 
    using a1 a2 t'_implements_t subtype_trans by blast
  moreover have "is_obj_label_ok P obj T"
  proof (cases "is_cap_type P (ttype T')")
    case b1: True
    (* Helper lemmas; unfold is_obj_label_ok P obj T'  *)
    then obtain cbname' where b2: "(ttype T') = (IfaceT cbname')"
      by (metis \<tau>.exhaust is_cap_type.simps(1) is_cap_type.simps(2))
    then have b3: "(tlabel T') = (cap_label P cbname') \<inter> (HLabel obj) \<and> (superinterface_set P cbname') \<subseteq> (tlabel T')"
      using b1 a2 unfolding is_obj_label_ok_def by auto
    (* Main proof *)
    have "(tlabel T) = (cap_label P cbname) \<inter> (HLabel obj)"
    proof -
      have "(cap_label P cbname) \<subseteq> (cap_label P cbname')"
        using cap_label_subtype_mono t'_implements_t b2 cap wfp a1 by auto
      then show ?thesis
        using a1 b3 label by blast
    qed
    moreover have "(superinterface_set P cbname) \<subseteq> (tlabel T)"
    proof -
      have "(superinterface_set P cbname) \<subseteq> (superinterface_set P cbname')"
        using superinterface_set_subtype_mono t'_implements_t b2 cap wfp a1 by auto
      then show ?thesis
        using a1 b3 label unfolding cap_label_def by auto
    qed
    ultimately show ?thesis using a2 a1 cap unfolding is_obj_label_ok_def by simp
  next
    case False
    then have b1: "(tlabel T') = (HLabel obj)"
      using a2 unfolding is_obj_label_ok_def by simp
    then have b2: "(tlabel T) = (cap_label P cbname) \<inter> (HLabel obj)"
      using a1 label by blast
    moreover have "(superinterface_set P cbname) \<subseteq> (tlabel T)"
      using b1 b2 reqs a1 False unfolding cap_label_def by auto
    ultimately show ?thesis using a2 a1 cap unfolding is_obj_label_ok_def by simp
  qed
  ultimately show ?thesis using a1 by simp
next
  case (3 P H t)
  then show ?thesis by simp
qed

lemma is_expr_value_ok_wrap:
  assumes wfp: "wf_prog P"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes ok: "is_expr_value_ok P S T' v"
  assumes t'_implements_t: "(P \<turnstile> (ttype T') <: (ttype T))"
  assumes label: "(tlabel T') \<inter> (cap_label P cbname) = (tlabel T)"
  assumes reqs: "\<not>is_cap_type P (ttype T') \<longrightarrow> (superinterface_set P cbname) \<subseteq> (msreq M) \<inter> (tlabel T')"
  assumes cap: "is_cap P cbname \<and> (ttype T) = (IfaceT cbname)"
  shows "is_expr_value_ok P S T v"
proof (cases "except S")
  case None
  define T1' where "T1' \<equiv> (intersect_label T' (privs S))"
  define T1 where "T1 \<equiv> (intersect_label T (privs S))"
  have "is_value_ok P (heap S) T1' v"
    using None ok unfolding is_expr_value_ok_def T1'_def by simp
  moreover have "(tlabel T1') \<inter> (cap_label P cbname) = (tlabel T1)"
    using label T1'_def T1_def intersect_label_label by auto
  moreover have "\<not>is_cap_type P (ttype T1') \<longrightarrow> (superinterface_set P cbname) \<subseteq> (tlabel T1')" (* using msreq M \<subseteq> privs S *)
    using reqs T1'_def T1_def intersect_label_label intersect_label_type corr unfolding corr_def by auto
  moreover have "(P \<turnstile> (ttype T1') <: (ttype T1))"
    using T1'_def T1_def t'_implements_t intersect_label_type by auto
  moreover have "is_cap P cbname \<and> (ttype T1) = (IfaceT cbname)"
    using T1'_def T1_def cap intersect_label_type by auto
  ultimately have "is_value_ok P (heap S) T1 v"
    using is_value_ok_wrap wfp by simp
  then show ?thesis 
    using None unfolding T1_def is_expr_value_ok_def by simp
next
  case (Some a)
  then show ?thesis using ok unfolding is_expr_value_ok_def by simp
qed

lemma preservation_expr_wrap:
  assumes op1: "P \<turnstile> \<langle>e | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S'\<rangle>"
  assumes hyp: "\<And>M \<Gamma> T. (P M \<Gamma> \<^bold>\<turnstile> S) \<and> (P M \<Gamma> \<turnstile> e : T) \<longrightarrow> (P M \<Gamma> \<^bold>\<turnstile> S') \<and> transition_ok S S' \<and> is_expr_value_ok P S' T v"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wf: "P M \<Gamma> \<turnstile> wrap cbname e : T"
  assumes wfp: "wf_prog P"
  shows "(P M \<Gamma> \<^bold>\<turnstile> S') \<and> transition_ok S S' \<and> is_expr_value_ok P S' T v"
proof -
  obtain T' where a1: "(P M \<Gamma> \<turnstile> e : T') \<and> (P \<turnstile> (ttype T') <: (IfaceT cbname)) \<and>
           is_cap P cbname \<and> (\<not>is_cap_type P (ttype T') \<longrightarrow> (superinterface_set P cbname) \<subseteq> (msreq M) \<inter> (tlabel T')) \<and>
           (IfaceT cbname) = (ttype T) \<and> (tlabel T') \<inter> (cap_label P cbname) = (tlabel T)"
    using wf wf_expr_wrap_intro by (metis prod.collapse fst_conv snd_conv)
  then have a2: "(P M \<Gamma> \<^bold>\<turnstile> S') \<and> transition_ok S S' \<and> is_expr_value_ok P S' T' v"
    using hyp corr by metis
  then show ?thesis 
    using wfp a1 is_expr_value_ok_wrap by metis
qed

lemma preservation_stmt_assign:
  assumes op1: "no_exception_or_return S"
  assumes op2: "S' = (if except S1 = None then S1\<lparr>stack := stack S1(x \<mapsto> v)\<rparr> else S1)"
  assumes op3: "P \<turnstile> \<langle>e | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S1\<rangle>"
  assumes hyp: "\<And>M \<Gamma> T. (P M \<Gamma> \<^bold>\<turnstile> S) \<and> (P M \<Gamma> \<turnstile> e : T) \<longrightarrow> (P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S S1 \<and> is_expr_value_ok P S1 T v"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wf: "P M \<Gamma> \<turnstile> assign x e \<bullet>"
  shows "(P M \<Gamma> \<^bold>\<turnstile> S') \<and> transition_ok S S'"
proof -
  obtain T where a1: "(\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some T) \<and> (P M \<Gamma> \<turnstile> e : T)"
    using wf wf_stmt_assign_intro by blast
  then have a2: "(P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S S1 \<and> is_expr_value_ok P S1 T v"
    using corr hyp by blast
  then show ?thesis proof (cases "except S1")
    case None
    (* There was no exception evaluating the expression, hence the return value will be 
       valid and type-correct. *)
    have "P M \<Gamma> \<^bold>\<turnstile> S1" using a2 by simp
    moreover have "\<Gamma> = \<Gamma>(x\<mapsto>T)" using a1 by auto
    moreover have "is_value_ok P (heap S1) (intersect_label T (privs S1)) v" using a2 None unfolding is_expr_value_ok_def by simp 
    moreover have b1: "S' = S1\<lparr>stack := stack S1(x \<mapsto> v)\<rparr>" using op2 None by simp
    ultimately have "P M \<Gamma> \<^bold>\<turnstile> S'" using stack_update_ok by metis
    moreover have "transition_ok S1 S'" using b1 transition_ok_simple by simp
    ultimately show ?thesis using a2 transition_ok_trans by metis
  next
    (* There was an exception evaluation the expression, no assignment to take place *)
    case (Some ex)
    then have "S' = S1" using op2 by simp
    then show ?thesis using a2 by simp
  qed
qed

lemma preservation_stmt_assignfi:
  assumes op1: "no_exception_or_return S" (* unused *)
  assumes op2: "a = the (stack S1 x)"
  assumes op3: "a \<noteq> v.null"
  assumes op4: "l = the_href a"
  assumes op5: "obj = the (heap S1 l)"
  assumes op6: "S' = (if except S1 = None then S1\<lparr>heap := heap S1(l \<mapsto> obj\<lparr>HFields := HFields obj(f \<mapsto> v)\<rparr>)\<rparr> else S1)"
  assumes op7: "P \<turnstile> \<langle>e | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S1\<rangle>" (* unused *)
  assumes hyp: "\<And>M \<Gamma> T. (P M \<Gamma> \<^bold>\<turnstile> S) \<and> (P M \<Gamma> \<turnstile> e : T) \<longrightarrow> (P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S S1 \<and> is_expr_value_ok P S1 T v"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wf: "P M \<Gamma> \<turnstile> assignfi x f e \<bullet>"
  assumes wfp: "wf_prog P"
  shows "(P M \<Gamma> \<^bold>\<turnstile> S') \<and> transition_ok S S'"
proof -
  obtain T where a1: "wf_fieldi_access P \<Gamma> x f T \<and> (P M \<Gamma> \<turnstile> e : T)"
    using wf wf_stmt_assignfi_intro by blast
  then obtain c \<gamma>0 fdecl where a2: "(\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some ((ClassT c),\<gamma>0)) \<and> field P c f = Some fdecl \<and>
                                    \<not>fstatic fdecl \<and> T = intersect_label (ftype fdecl) \<gamma>0"
    unfolding wf_fieldi_access_def by blast
  have a3: "(P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S S1 \<and> is_expr_value_ok P S1 T v"
    using a1 corr hyp by blast
  then show ?thesis proof (cases "except S1")
    case None
    have "P M \<Gamma> \<^bold>\<turnstile> S1"
      using a3 by simp
    moreover have b1: "heap S1 l = Some obj \<and> (P \<turnstile> (ClassT (HClass obj)) <: (ClassT c)) \<and> is_obj_label_ok P obj (intersect_label ((ClassT c),\<gamma>0) (privs S1))"  
      using object_correspondence a2 a3 op2 op3 op4 op5 by (metis \<tau>.simps(5) fst_conv)
    moreover have "is_value_ok P (heap S1) (intersect_label (ftype fdecl) (HLabel obj)) v"
    proof - 
      have "is_value_ok P (heap S1) (intersect_label T (privs S1)) v"
        using a3 None a2 unfolding is_expr_value_ok_def by simp
      moreover have "(HLabel obj) = \<gamma>0 \<inter> (privs S1)"
        using a2 b1 intersect_label_label intersect_label_type unfolding is_obj_label_ok_def by auto
      ultimately show ?thesis using a2 intersect_label_vary by metis
    qed
    moreover have "field P (HClass obj) f = Some fdecl"
      using a2 b1 field_subtype wfp by metis
    moreover have b2: "S' = S1\<lparr>heap := heap S1(l \<mapsto> obj\<lparr>HFields := HFields obj(f \<mapsto> v)\<rparr>)\<rparr>" 
      using op6 None by simp
    ultimately have b3: "(P M \<Gamma> \<^bold>\<turnstile> S') \<and> heap_extends (heap S1) (heap S')"
      using heap_update_ok heap_extends_consistent_heap_update obj_consistent_field_update  by simp
    moreover have "transition_ok S1 S'" 
      using b2 b3 unfolding transition_ok_def by simp
    ultimately show ?thesis using a3 transition_ok_trans by blast
  next
    case (Some a)
    then have "S' = S1" using op6 by simp
    then show ?thesis using a3 by simp
  qed
qed

lemma preservation_stmt_assignfs:
  assumes op1: "no_exception_or_return S"
  assumes op2: "classStatics = the (globals S1 c)"
  assumes op3: "S' = (if except S1 = None then S1\<lparr>globals := globals S1(c \<mapsto> classStatics(f \<mapsto> v))\<rparr> else S1)"
  assumes op4: "P \<turnstile> \<langle>e | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S1\<rangle>"
  assumes hyp: "\<And>M \<Gamma> T. (P M \<Gamma> \<^bold>\<turnstile> S) \<and> (P M \<Gamma> \<turnstile> e : T) \<longrightarrow> (P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S S1 \<and> is_expr_value_ok P S1 T v"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wf: "P M \<Gamma> \<turnstile> assignfs c f e \<bullet>"
  assumes wfp: "wf_prog P"
  shows "(P M \<Gamma> \<^bold>\<turnstile> S') \<and> transition_ok S S'"
proof -
  obtain T where a1: "wf_fields_access P M c f T \<and> (P M \<Gamma> \<turnstile> e : T)"
    using wf wf_stmt_assignfs_intro by blast
  then obtain fdecl where a2: "is_class P c \<and> field P c f = Some fdecl \<and> fstatic fdecl \<and> 
                                  (T = (ftype fdecl) \<and> (tlabel (ftype fdecl)) \<subseteq> (msreq M))"
    using wf_fields_access_def by auto
  have a3: "(P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S S1 \<and> is_expr_value_ok P S1 T v"
    using a1 corr hyp by blast
  then show ?thesis proof (cases "except S1")
    case None
    then have "is_value_ok P (heap S1) (intersect_label T (privs S1)) v"
      using a2 a3 unfolding is_expr_value_ok_def by simp
    moreover have "T = (intersect_label T (privs S1))" 
    proof -
      have "tlabel T \<subseteq> (msreq M)" using a2 by simp
      moreover have "(msreq M) \<subseteq> (privs S1)" using a3 unfolding corr_def by simp
      ultimately show ?thesis using intersect_label_label intersect_label_type
        by (metis Int_absorb2 order_trans prod_eqI) 
    qed
    moreover have b1: "S' = S1\<lparr>globals := globals S1(c \<mapsto> classStatics(f \<mapsto> v))\<rparr>"
      using op3 None by simp
    ultimately have "P M \<Gamma> \<^bold>\<turnstile> S'"
      using globals_update_ok a2 a3 op2 by simp
    moreover have "transition_ok S1 S'"
      using transition_ok_simple op3 by simp
    ultimately show ?thesis 
      using b1 a3 transition_ok_trans by metis
  next
    case (Some a)
    then have "S' = S1" using op3 by simp
    then show ?thesis using a3 by simp
  qed
qed

lemma stack_variable_restore:
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes corr2: "(P M \<Gamma>' \<^bold>\<turnstile> S2)"
  assumes trans: "transition_ok S S2"
  assumes \<Gamma>': "\<Gamma>' = \<Gamma>(x\<mapsto>T)"
  assumes op3: "S' = S2\<lparr>stack := (stack S2)(x := (stack S x))\<rparr>"
  shows "(P M \<Gamma> \<^bold>\<turnstile> S') \<and> transition_ok S S'"
proof - 
  have "(P M \<Gamma> \<^bold>\<turnstile> S')" proof (cases "\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v")
    case None
    then show ?thesis using corr2 op3 unfolding corr_def \<Gamma>' var_corr_def by auto
  next
    case (Some T')
    then have b1: "(stack S x) \<noteq> None \<and> is_value_ok P (heap S) (intersect_label T' (privs S)) (the (stack S x))" 
      using corr stack_access_ok by blast
    then have "is_value_ok P (heap S2) (intersect_label T' (privs S2)) (the (stack S x))" 
      using trans is_value_ok_heap_extends unfolding transition_ok_def by metis
    moreover have "\<Gamma> = \<Gamma>'(x\<mapsto>T')" 
      using Some \<Gamma>' by auto
    moreover have "S' = S2\<lparr>stack := (stack S2)(x \<mapsto> the(stack S x))\<rparr>"
      using op3 b1 by simp
    ultimately show ?thesis using stack_update_ok corr2 op3 by simp
  qed
  moreover have "transition_ok S S'"
    using trans op3 unfolding transition_ok_def by simp
  ultimately show ?thesis by simp
qed

lemma preservation_stmt_letin:
  assumes op1: "no_exception_or_return S"
  assumes op2: "S1 = S\<lparr>stack := stack S(x \<mapsto> v.null)\<rparr>"
  assumes op3: "S' = S2\<lparr>stack := (stack S2)(x := (stack S x))\<rparr>"
  assumes op4: "P \<turnstile> \<langle>seq (assign x e) s | S1\<rangle> \<rightarrow>\<^sub>s \<langle>S2\<rangle>" (* unused *)
  assumes hyp: "\<And>M \<Gamma>. (P M \<Gamma> \<^bold>\<turnstile> S1) \<and> (P M \<Gamma> \<turnstile> seq (assign x e) s \<bullet>) \<longrightarrow> (P M \<Gamma> \<^bold>\<turnstile> S2) \<and> transition_ok S1 S2"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wf: "P M \<Gamma> \<turnstile> letin T x e s \<bullet>"
  shows "(P M \<Gamma> \<^bold>\<turnstile> S') \<and> transition_ok S S'"
proof -
  define \<Gamma>' where "\<Gamma>' = \<Gamma>(x\<mapsto>T)"
  have a1: "(P M \<Gamma>' \<^bold>\<turnstile> S1)"
    using corr stack_update_ok \<Gamma>'_def op2 by simp
  have a2: "(P M \<Gamma>(x := None) \<turnstile> e : T) \<and> (P M \<Gamma>(x\<mapsto>T) \<turnstile> s \<bullet>)"
    using wf wf_stmt_letin_intro by simp
  moreover have "(P M \<Gamma>(x\<mapsto>T) \<turnstile> e : T)"
    using a2 wf_expr_mono_lenv by (metis fun_upd_upd map_add_subsumed2 upd_None_map_le)
  ultimately have "(P M \<Gamma>' \<turnstile> (seq (assign x e) s) \<bullet>)"
    using wf_stmt_assign wf_stmt_seq \<Gamma>'_def by simp
  then have a3: "(P M \<Gamma>' \<^bold>\<turnstile> S2) \<and> transition_ok S1 S2"
    using hyp a1 by simp
  then have a4: "transition_ok S S2"
    using op2 unfolding transition_ok_def by auto
  show ?thesis
    using stack_variable_restore corr a3 \<Gamma>'_def op3 a4 by metis
qed

lemma preservation_stmt_return:
  assumes op1: "no_exception_or_return S"
  assumes op2: "S' = (if except S1 = None then S1\<lparr>retval := Some v\<rparr> else S1)"
  assumes op3: "P \<turnstile> \<langle>e | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S1\<rangle>" (* unused *)
  assumes hyp: "\<And>M \<Gamma> T. (P M \<Gamma> \<^bold>\<turnstile> S) \<and> (P M \<Gamma> \<turnstile> e : T) \<longrightarrow> (P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S S1 \<and> is_expr_value_ok P S1 T v"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wf: "P M \<Gamma> \<turnstile> return e \<bullet>"
  shows "(P M \<Gamma> \<^bold>\<turnstile> S') \<and> transition_ok S S'"
proof -
  have "P M \<Gamma> \<turnstile> e : (msreturn M)"
    using wf wf_stmt_return_intro by simp
  then have a1: "(P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S S1 \<and> is_expr_value_ok P S1 (msreturn M) v"
    using hyp corr by simp
  have "P M \<Gamma> \<^bold>\<turnstile> S'" proof (cases "except S1")
    case None
    then have "is_value_ok P (heap S1) (intersect_label (msreturn M) (privs S1)) v"
      using a1 unfolding is_expr_value_ok_def by simp
    moreover have "S' = S1\<lparr>retval := Some v\<rparr>"
      using op2 None by simp
    ultimately show "P M \<Gamma> \<^bold>\<turnstile> S'" 
      using retval_update_ok a1 by simp
  next
    case (Some a)
    then show ?thesis using op2 a1 by simp
  qed
  moreover have "transition_ok S S'"
    using a1 op2 unfolding transition_ok_def by simp
  ultimately show ?thesis by simp
qed

lemma preservation_stmt_throw:
  assumes op1: "no_exception_or_return S"
  assumes op2: "S' = (if except S1 = None then S1\<lparr>except := Some v\<rparr> else S1)"
  assumes op3: " P \<turnstile> \<langle>e | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S1\<rangle>"
  assumes op4: "v \<noteq> null"
  assumes hyp: "\<And>M \<Gamma> T. (P M \<Gamma> \<^bold>\<turnstile> S) \<and> (P M \<Gamma> \<turnstile> e : T) \<longrightarrow> (P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S S1 \<and> is_expr_value_ok P S1 T v"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wf: "P M \<Gamma> \<turnstile> throw e \<bullet>"
  shows "(P M \<Gamma> \<^bold>\<turnstile> S') \<and> transition_ok S S'"
proof -
  have "P M \<Gamma> \<turnstile> e : (ClassT Object,{})"
    using wf wf_stmt_throw_intro by simp
  then have a1: "(P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S S1 \<and> is_expr_value_ok P S1 ((ClassT Object),{}) v"
    using corr hyp by metis
  show ?thesis proof (cases "except S1")
    case None
    then have "is_value_ok P (heap S1) ((ClassT Object),{}) v" 
      using a1 unfolding is_expr_value_ok_def unfolding intersect_label_def by simp
    moreover have b1: "S' = S1\<lparr>except := Some v\<rparr>"
      using op2 None by simp
    ultimately have "P M \<Gamma> \<^bold>\<turnstile> S'" 
      using except_update_ok op4 a1 by simp
    moreover have "transition_ok S S'"
      using a1 b1 unfolding transition_ok_def by simp
    ultimately show ?thesis by simp
  next
    case (Some a)
    then show ?thesis 
      using a1 op2 by simp
  qed
qed

lemma minimum_list_item:
  assumes "i = Min {j. (j = length list) \<or> ((j < length list) \<and> P j)}"
  assumes "i < length list"
  shows "P i"
proof -
  have "finite {j. (j = length list) \<or> ((j < length list) \<and> P j)}"
    by simp
  then show ?thesis using assms
    by (metis (mono_tags, lifting) Min_in empty_iff mem_Collect_eq nat_neq_iff)
qed

lemma preservation_stmt_trycatch_ex_helper:
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
                     ((P \<turnstile> \<langle>chstmt h | S2\<rangle> \<rightarrow>\<^sub>s \<langle>S3\<rangle>) \<and> (\<forall>M \<Gamma>. (P M \<Gamma> \<^bold>\<turnstile> S2) \<and> (P M \<Gamma> \<turnstile> chstmt h \<bullet>)
                           \<longrightarrow> (P M \<Gamma> \<^bold>\<turnstile> S3) \<and> transition_ok S2 S3)) \<and> 
                     S' = S3\<lparr>stack := (stack S3)(var := stack S1 var)\<rparr>
                else S' = S1"
  assumes hyp: "\<And>M \<Gamma>. (P M \<Gamma> \<^bold>\<turnstile> S) \<and> (P M \<Gamma> \<turnstile> s \<bullet>) \<longrightarrow> (P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S S1"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wf: "P M \<Gamma> \<turnstile> trycatch s ch \<bullet>"
  assumes intermediate: "\<Gamma>' = \<Gamma>(var \<mapsto> ((chtype h),{}))"
  shows "(P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S S1 \<and>
          (i < length ch \<longrightarrow> (P M \<Gamma>' \<^bold>\<turnstile> S2) \<and> (P M \<Gamma>' \<turnstile> chstmt h \<bullet>) \<and> transition_ok S1 S2 \<and>
                             (P M \<Gamma>' \<^bold>\<turnstile> S3) \<and> transition_ok S2 S3 \<and> transition_ok S3 S') \<and>
          (P M \<Gamma> \<^bold>\<turnstile> S') \<and> transition_ok S1 S'"
proof -
  define TException where "TException \<equiv> ((ClassT Object),({}::(iname set)))"
  have a1: "(P M \<Gamma> \<turnstile> s \<bullet>) \<and> (\<forall>(t,x,s')\<in>(set ch). (P M \<Gamma>(x\<mapsto>(t,{})) \<turnstile> s' \<bullet>) \<and> \<not>is_cap_type P t)"
    using wf wf_stmt_trycatch_intro by simp
  then have a2: "(P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S S1"
    using corr hyp by metis
  then have a3: "is_value_ok P (heap S1) TException ex \<and> ex \<noteq> null"
    using op2 unfolding corr_def is_except_ok_def TException_def by simp
  show ?thesis proof (cases "i < length ch")
    case True
    define T where "T \<equiv> ((chtype h),({}::(iname set)))"
    then have \<Gamma>'_def: "\<Gamma>' \<equiv> \<Gamma>(var \<mapsto> (T))" using intermediate by simp
    (* Show S2 (start of catch handler) to be type-correct *)
    have b1: "(ttype T,var,chstmt h) \<in> (set ch)" 
      using T_def op7 True by simp
    then have b2: "P M \<Gamma>' \<turnstile> chstmt h \<bullet> \<and> \<not>is_cap_type P (ttype T)"
      using a1 b1 unfolding \<Gamma>'_def T_def by auto
    have "ex = (href a)"
      using op3 a3 TException_def by (metis \<tau>.simps(5) fst_conv is_value_ok_num the_href.simps(1) v.exhaust)
    moreover have "(P \<turnstile> ClassT (HClass exObj) <: (ttype T))" 
      using minimum_list_item op6 op7 True unfolding T_def by fastforce 
    moreover have "(tlabel T = tlabel TException)"
       unfolding TException_def T_def by fastforce 
    moreover have "\<not>is_cap_type P (ttype TException)"
       unfolding TException_def T_def by fastforce 
    ultimately have "is_value_ok P (heap S1) T ex"
      using is_value_ok_valid_object_cast a3 op4 b2 by simp 
    then have "is_value_ok P (heap S1) (intersect_label T (privs S1)) ex"
      unfolding T_def intersect_label_def by simp
    then have "P M \<Gamma>' \<^bold>\<turnstile> (S1\<lparr> stack := (stack S1)(var \<mapsto> ex)\<rparr>)"
      using a2 stack_update_ok \<Gamma>'_def by simp
    then have b3: "P M \<Gamma>' \<^bold>\<turnstile> S2"
      using op7 True unfolding corr_def is_except_ok_def var_corr_def by simp
    (* apply induction hypothesis (for execution of catch handler) *)
    then have b4: "(P M \<Gamma>' \<^bold>\<turnstile> S3) \<and> transition_ok S2 S3"
      using b2 op7 True by metis
    (* show restoring local variable var after execution of catch handler OK *)
    moreover have b5: "transition_ok S1 S2"
      using op7 True using transition_ok_simple by auto
    ultimately have "transition_ok S1 S3"
      using transition_ok_trans b4 by metis
    then have "(P M \<Gamma> \<^bold>\<turnstile> S')"
      using stack_variable_restore a2 b4 \<Gamma>'_def op7 True  by metis
    moreover have "transition_ok S3 S'"
      using op7 True using transition_ok_simple by auto
    ultimately show ?thesis using True a2 b2 b3 b4 b5 transition_ok_trans by blast
  next
    case False
    then show ?thesis using a2 op7 transition_ok_self by simp
  qed
qed


lemma preservation_stmt_trycatch_ex:
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
                     ((P \<turnstile> \<langle>chstmt h | S2\<rangle> \<rightarrow>\<^sub>s \<langle>S3\<rangle>) \<and> (\<forall>M \<Gamma>. (P M \<Gamma> \<^bold>\<turnstile> S2) \<and> (P M \<Gamma> \<turnstile> chstmt h \<bullet>)
                           \<longrightarrow> (P M \<Gamma> \<^bold>\<turnstile> S3) \<and> transition_ok S2 S3)) \<and> 
                     S' = S3\<lparr>stack := (stack S3)(var := stack S1 var)\<rparr>
                else S' = S1"
  assumes hyp: "\<And>M \<Gamma>. (P M \<Gamma> \<^bold>\<turnstile> S) \<and> (P M \<Gamma> \<turnstile> s \<bullet>) \<longrightarrow> (P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S S1"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes wf: "P M \<Gamma> \<turnstile> trycatch s ch \<bullet>"
  shows "(P M \<Gamma> \<^bold>\<turnstile> S') \<and> transition_ok S S'"
proof -
  define \<Gamma>' where "\<Gamma>' = \<Gamma>(var \<mapsto> ((chtype h),{}))"
  then have a1: "(P M \<Gamma> \<^bold>\<turnstile> S1) \<and> transition_ok S S1 \<and>
          (i < length ch \<longrightarrow> (P M \<Gamma>' \<^bold>\<turnstile> S2) \<and> transition_ok S1 S2 \<and>
                             (P M \<Gamma>' \<^bold>\<turnstile> S3) \<and> transition_ok S2 S3 \<and> transition_ok S3 S') \<and>
          (P M \<Gamma> \<^bold>\<turnstile> S') \<and> transition_ok S1 S'"
    using \<Gamma>'_def preservation_stmt_trycatch_ex_helper assms  by blast
  then show ?thesis using transition_ok_trans by blast
qed

lemma preservation:
  assumes wfp: "wf_prog P"
  shows "((P \<turnstile> \<langle>e | S\<rangle> \<rightarrow>\<^sub>e \<langle>v | S'\<rangle>) \<longrightarrow> (\<forall>M \<Gamma> T. ((P M \<Gamma> \<^bold>\<turnstile> S) \<and> (P M \<Gamma> \<turnstile> e : T)) \<longrightarrow> ((P M \<Gamma> \<^bold>\<turnstile> S') \<and> (transition_ok S S') \<and> (is_expr_value_ok P S' T v))))
       \<and> ((P \<turnstile> \<langle>s | S\<rangle> \<rightarrow>\<^sub>s \<langle>S'\<rangle>) \<longrightarrow> (\<forall>M \<Gamma>. ((P M \<Gamma> \<^bold>\<turnstile> S) \<and> (P M \<Gamma> \<turnstile> s \<bullet>)) \<longrightarrow> ((P M \<Gamma> \<^bold>\<turnstile> S') \<and> (transition_ok S S'))))"
proof (induction S S' rule: op_expr_op_stmt.induct)
  case (op_expr_ref v S x)
  then show ?case using preservation_expr_ref wfp by blast 
next
  case (op_expr_new v l S S' cname lname)
  then show ?case using preservation_expr_new wfp by metis
next
  case (op_expr_calli a S x l obj d m mname s S0 args S1 S' v)
  then show ?case using preservation_expr_calli assms by force
next
  case (op_expr_calls d m c mname s S0 S args S1 S' v)
  then show ?case using preservation_expr_calls assms by force
next
  case (op_expr_cast e S v S' hobj t)
  then show ?case using preservation_expr_cast wfp by blast
next
  case (op_expr_const k v S)
  then show ?case using preservation_expr_const by blast
next
  case (op_expr_fieldacci a S x l obj v f)
  then show ?case using preservation_expr_fieldacci assms by force
next
  case (op_expr_fieldaccs classStatics S c v f)
  then show ?case using preservation_expr_fieldaccs wfp by force
next
  case (op_expr_wrap e S v S' cbname)
  then show ?case using preservation_expr_wrap wfp by blast
next
  case (op_stmt_assign S e v S1 S' x)
  then show ?case using preservation_stmt_assign by blast
next
  case (op_stmt_assignfi S e v S1 a x l obj S' f)
  then show ?case using preservation_stmt_assignfi assms by blast
next
  case (op_stmt_assignfs S e v S1 classStatics c S' f)
  then show ?case using preservation_stmt_assignfs assms by blast
next
  case (op_stmt_expr S e v S')
  then show ?case using wf_stmt_expr_intro by blast
next
  case (op_stmt_then S v x s1 S1 s2)
  then show ?case using wf_stmt_ifelse_intro by blast
next
  case (op_stmt_else S v x s2 S2 s1)
  then show ?case using wf_stmt_ifelse_intro by blast
next  
  case (op_stmt_letin S S1 x e s S2 S' T)
  then show ?case using preservation_stmt_letin by blast
next
  case (op_stmt_return S e v S1 S')
  then show ?case using preservation_stmt_return by blast
next
  case (op_stmt_seq S s1 S1 s2 S2)
  then show ?case using wf_stmt_seq_intro transition_ok_trans by blast
next
  case (op_stmt_throw S e v S1 S')
  then show ?case using preservation_stmt_throw by blast
next  
  case (op_stmt_trycatch_ok S s S1 S' catchhandlers)
  then show ?case using wf_stmt_trycatch_intro by blast
next
  case (op_stmt_trycatch_ex S s S1 ex a exObj i ch h var S2 S3 S')
  then show ?case using preservation_stmt_trycatch_ex by blast
next
  case (op_stmt_exception_or_return S s)
  then show ?case using transition_ok_self by simp
qed (* [where ?x1.0 = e and ?x3.0 = v and ?x5.0 = s] *)

end