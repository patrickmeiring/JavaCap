theory javacap_runtime_representation
imports
  Main
  javacap_syntax
  javacap_auxiliary
  javacap_typing
begin

(* Dynamic semantics types *)
typedecl heaploc

datatype v = href "heaploc" | null | num "nat"

  
primrec the_href :: "v \<Rightarrow> heaploc"
  where "the_href (href l) = l" | 
        "the_href null = undefined" |
        "the_href (num n) = undefined"

primrec the_num :: "v \<Rightarrow> nat"
  where "the_num (num v) = v" |
        "the_num null = undefined" |
        "the_num (href l) = undefined"


record heapobj =
  HClass :: "cname"
  HFields :: "(fname \<rightharpoonup> v)"
  HLabel :: "label"        (*  The global label of this object.
                               This field exists merely to aid verification; the operational 
                               semantics should not use it to make any decision, so it need
                               not exist in an actual runtime. *)

type_synonym staticfields = "(fname \<rightharpoonup> v)"

type_synonym Stack = "(var \<rightharpoonup> v)"
type_synonym Heap = "(heaploc \<rightharpoonup> heapobj)"
type_synonym Globals = "(cname \<rightharpoonup> staticfields)"

record State =
  stack :: "Stack"
  heap :: "Heap"
  globals :: "Globals"
  except :: "v option"
  retval :: "v option"
  privs :: "label" (* Exists purely to aid verification, this is the maximal label
                      the currently executing code should be able to access. *)

(* Creates a mapping which sets all the fields in the specified class to null, and leaves
   everything else unset (None). *)
definition new_object :: "prog \<Rightarrow> cname \<Rightarrow> label \<Rightarrow> heapobj"
  where "new_object P cname label =
         \<lparr> HClass = cname, HFields = (\<lambda>f. case (field P cname f) of Some t \<Rightarrow> Some null | None \<Rightarrow> None), HLabel = label\<rparr>"

definition is_obj_label_ok :: "prog \<Rightarrow> heapobj \<Rightarrow> \<T> \<Rightarrow> bool"
  where "is_obj_label_ok P obj T \<equiv> 
            (if (is_cap_type P (ttype T)) 
            (* it's only safe to let (tlabel T) be less than (HLabel obj) this allowance because one cannot unwrap (downcast)
               a capability. One can only call the methods of the capability, and these have stricter restrictions than
               the label. *)
            then (let cbname = (the_iname (ttype T)) in (tlabel T) = (cap_label P cbname) \<inter> (HLabel obj) \<and>
                                                        (* This gives some 'meaning' to the labels. *)
                                                        (superinterface_set P cbname) \<subseteq> (tlabel T))
            else (HLabel obj) = (tlabel T))
         \<and> creq (the (class P (HClass obj))) \<subseteq> (HLabel obj) (* object must have a label that is a superset of the class ambient clause *) 
         \<and> (HLabel obj) \<subseteq> (the (grant P (HClass obj)))" (* object must have a label less than what has been granted *)

(* Performs basic (non-recursive) checks of the type-correctness of a value. 
   For pointers, this means the pointer points to a object that exists on the heap, and the
   object is of a type compatible with the static type of the value. *)
fun is_value_ok :: "prog \<Rightarrow> Heap \<Rightarrow> \<T> \<Rightarrow> v \<Rightarrow> bool"
  where is_value_ok_num: "is_value_ok P H T (num v) = ((ttype T) = (ValT IntT))"
      | is_value_ok_href: "is_value_ok P H T (href loc) = (\<exists>obj. H loc = Some obj \<and> (P \<turnstile> (ClassT (HClass obj)) <: (ttype T)) \<and> is_obj_label_ok P obj T)" 
      | is_value_ok_null: "is_value_ok P H T (null) = True"

(* Performs shallow checks that an object at runtime is type-correct to its own type. *)
definition is_heapobj_ok :: "prog \<Rightarrow> Heap \<Rightarrow> heapobj \<Rightarrow> bool"
  where "is_heapobj_ok P H obj \<equiv> (\<forall>f fd. field P (HClass obj) f = Some fd \<and> \<not>fstatic fd \<longrightarrow> (\<exists>v. (HFields obj) f = Some v \<and> is_value_ok P H (intersect_label (ftype fd) (HLabel obj)) v))"

definition is_heap_ok :: "prog \<Rightarrow> Heap \<Rightarrow> bool"
  where "is_heap_ok P H \<equiv> (\<forall>loc\<in>dom(H). (is_heapobj_ok P H (the (H loc))))"

definition is_staticfields_ok :: "prog \<Rightarrow> Heap \<Rightarrow> cname \<Rightarrow> staticfields \<Rightarrow> bool"
  where "is_staticfields_ok P H c sf \<equiv> (\<forall>f fd. field P c f = Some fd \<and> fstatic fd \<longrightarrow> (\<exists>v. sf f = Some v \<and> is_value_ok P H (ftype fd) v))"

definition is_globals_ok :: "prog \<Rightarrow> Heap \<Rightarrow> Globals \<Rightarrow> bool"
  where "is_globals_ok P H G \<equiv> (\<forall>c. is_class P c \<longrightarrow> (\<exists>sf. G c = Some sf \<and> is_staticfields_ok P H c sf)) "

(* For all method (even if they return void), the return value stored against the state should be
   a type-correct value when the method returns. Otherwise, an exception may be return upon return. *)
definition is_retval_ok :: "prog \<Rightarrow> Heap \<Rightarrow> \<T> \<Rightarrow> v option \<Rightarrow> bool" 
  where "is_retval_ok P H T rv \<equiv> (rv \<noteq> None \<longrightarrow> is_value_ok P H T (the rv))"

(* For now, we don't use a special base class for exceptions. Any object can be thrown. *)
definition is_except_ok :: "prog \<Rightarrow> Heap \<Rightarrow> v option \<Rightarrow> bool"
  where "is_except_ok P H e \<equiv> (e \<noteq> None \<longrightarrow> (is_value_ok P H ((ClassT Object),{}) (the e) \<and> (the e) \<noteq> null))"

definition var_corr :: "prog \<Rightarrow> lenv \<Rightarrow> State \<Rightarrow> var \<Rightarrow> bool"
  where "var_corr P \<Gamma> S x \<equiv>  (\<forall>T. (\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some T) \<longrightarrow> (\<exists>v. (stack S x = Some v) \<and> (is_value_ok P (heap S) (intersect_label T (privs S)) v)))"

(* Defines the correlation between the static typing and the runtime state of the system. *)
definition corr :: "prog \<Rightarrow> msenv \<Rightarrow> lenv \<Rightarrow> State \<Rightarrow> bool" ("_ _ _ \<^bold>\<turnstile> _") (* P \<Gamma> \<turnstile> S H *)
  where "P M \<Gamma> \<^bold>\<turnstile> S \<equiv> (\<forall>x. var_corr P \<Gamma> S x) \<and> 
                       (is_heap_ok P (heap S)) \<and> 
                       (is_globals_ok P (heap S) (globals S)) \<and>
                       (is_retval_ok P (heap S) (intersect_label (msreturn M) (privs S)) (retval S)) \<and>
                       (is_except_ok P (heap S) (except S)) \<and> 
                       (msreq M) \<subseteq> (privs S) \<and>
                       (privs S) \<subseteq> the (grant P (mscname M))
  "

(* A requirement that the heap is only extended (only grows) from H to H' and that the
   type of those objects remains the same. This is a simplifying assumption. If we want to 
   allow garbage collection in our operational semantics, we could instead do the following:
    - Redefine our configuration correlation (type-correctness) property to only require 
      type-correctness of all objects which are reachable from the stack
    - Extend the representation of the stack to include the frames of calling methods. In other
      words, \<Gamma> \<^bold>\<turnstile> S H will require all objects reachable from any variable on any stack frame
      to remain type-correct. All other objects on the heap then become irrelevant.
 *)
definition obj_consistent :: "heapobj \<Rightarrow> heapobj \<Rightarrow> bool"
  where "obj_consistent o1 o2 \<equiv> (HClass o1) = (HClass o2) \<and> (HLabel o1) = (HLabel o2)"

definition heap_extends :: "Heap \<Rightarrow> Heap \<Rightarrow> bool"
  where "heap_extends H H' \<equiv> (\<forall>l\<in>dom(H). l\<in>dom(H') \<and> (obj_consistent (the (H l)) (the (H' l))))"

(* Represents the invariants that must hold over all statement executions.
   Note that this invariant is end-to-end and does not need to be met in intermediate states. *)
definition transition_ok :: "State \<Rightarrow> State \<Rightarrow> bool"
  where "transition_ok S S' \<equiv> heap_extends (heap S) (heap S') \<and> (privs S = privs S')"

lemma heap_extends_transitive:
  assumes extends: "heap_extends S S1"
  assumes extends2: "heap_extends S1 S2"
  shows "heap_extends S S2"
  using assms unfolding heap_extends_def obj_consistent_def by auto

lemma transition_ok_self:
  shows "transition_ok S S"
  unfolding transition_ok_def heap_extends_def obj_consistent_def by simp

lemma transition_ok_simple:
  assumes "heap S = heap S' \<and> privs S = privs S'"
  shows "transition_ok S S'"
  using assms unfolding transition_ok_def heap_extends_def obj_consistent_def by simp

lemma transition_ok_trans:
  assumes ok1: "transition_ok S S1"
  assumes ok2: "transition_ok S1 S2"
  shows "transition_ok S S2"
  using assms heap_extends_transitive unfolding transition_ok_def by auto

lemma is_value_ok_valid_cast:
  assumes ok: "is_value_ok P H T' (href l)"
  assumes heap_access: "(obj::heapobj) = the (H l)"
  assumes cast_valid: "P \<turnstile> (ClassT (HClass obj)) <: (ttype T)"
  assumes label_same: "tlabel T = tlabel T'"
  assumes source_non_cap: "\<not>is_cap_type P (ttype T')"
  assumes target_non_cap: "\<not>is_cap_type P (ttype T)"
  shows "is_value_ok P H T (href l)"
proof -
  have a1: "H l = Some obj \<and> (P \<turnstile> (ClassT (HClass obj)) <: (ttype T')) \<and> is_obj_label_ok P obj T'"
    using ok heap_access by auto
  then have "is_obj_label_ok P obj T"
    using source_non_cap target_non_cap label_same unfolding is_obj_label_ok_def by auto
  then show ?thesis 
    using a1 cast_valid by auto
qed

lemma stack_access_ok:
  assumes static: "\<Gamma>\<lbrakk>x\<rbrakk>\<^sub>v = Some T"
  assumes dynamic: "v = the (stack S x)"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  shows "stack S x = Some v \<and> is_value_ok P (heap S) (intersect_label T (privs S)) v"
proof -
  have "\<exists>v. (stack S x = Some v) \<and> (is_value_ok P (heap S) (intersect_label T (privs S)) v)"
    using corr static unfolding corr_def var_corr_def by metis
  then show ?thesis
    using dynamic by auto
qed


lemma allocate_is_value_shallow_ok:
  assumes ok: "is_value_ok P H T v"
  assumes new: "l \<notin> dom(H)"
  assumes op: "H' = H(l\<mapsto>obj)" 
  shows "is_value_ok P H' T v"
proof (cases v)
  case (href x1) 
  then show ?thesis using ok new op by auto
next
  case null 
  then show ?thesis by simp
next
  case (num x3) 
  then show ?thesis using ok by simp
qed

lemma allocate_is_heapobj_ok:
  assumes ok: "is_heapobj_ok P H obj"
  assumes new: "l \<notin> dom(H)"
  assumes op: "H' = H(l\<mapsto>obj')" 
  shows "is_heapobj_ok P H' obj"
  using assms allocate_is_value_shallow_ok unfolding is_heapobj_ok_def by blast

lemma is_retval_ok_value_ok:
  assumes "\<And>T v. is_value_ok P H T v \<Longrightarrow> is_value_ok P H' T v"
  assumes "is_retval_ok P H T r"
  shows "is_retval_ok P H' T r"
  using assms unfolding is_retval_ok_def by simp

lemma is_except_ok_value_ok:
  assumes "\<And>T v. is_value_ok P H T v \<Longrightarrow> is_value_ok P H' T v"
  assumes "is_except_ok P H e"
  shows "is_except_ok P H' e"
  using assms unfolding is_except_ok_def by simp

lemma is_globals_ok_value_ok:
  assumes "\<And>T v. is_value_ok P H T v \<Longrightarrow> is_value_ok P H' T v"
  assumes "is_globals_ok P H G"
  shows "is_globals_ok P H' G"
  using assms unfolding is_globals_ok_def is_staticfields_ok_def by meson

lemma allocate_ok:
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes new: "l \<notin> dom(heap S)"
  assumes op: "S' = S\<lparr>heap := (heap S)(l\<mapsto>obj)\<rparr>" 
  assumes new_obj_ok: "is_heapobj_ok P (heap S) obj"
  shows "P M \<Gamma> \<^bold>\<turnstile> S'"
proof -
  have a1: "\<And>t v. is_value_ok P (heap S) t v \<Longrightarrow> is_value_ok P (heap S') t v"
    using assms allocate_is_value_shallow_ok by simp
  moreover have "privs S = privs S' \<and> stack S = stack S'" using op by simp
  ultimately have "(\<forall>x. var_corr P \<Gamma> S' x)" 
    using corr op unfolding corr_def var_corr_def by metis
  moreover have "is_heap_ok P (heap S')"
  proof -    
    have "(\<forall>loc\<in>dom(heap S). (is_heapobj_ok P (heap S) (the (heap S loc))))"
      using corr unfolding corr_def is_heap_ok_def by auto
    then have "(\<forall>loc\<in>dom(heap S). (is_heapobj_ok P (heap S') (the ((heap S') loc))))" 
      using allocate_is_heapobj_ok new op by auto
    moreover have "is_heapobj_ok P (heap S') obj" 
      using new_obj_ok allocate_is_heapobj_ok new op by auto
    moreover have "dom(heap S') = dom((heap S)) \<union> {l}" 
      using op by auto
    ultimately show ?thesis 
      unfolding is_heap_ok_def using op by auto
  qed
  moreover have "is_globals_ok P (heap S') (globals S')" 
    using a1 corr is_globals_ok_value_ok op unfolding corr_def by fastforce  
  moreover have "is_retval_ok P (heap S') (intersect_label (msreturn M) (privs S')) (retval S')"
  proof -
    have "(retval S') = (retval S) \<and> (privs S' = privs S) " using op by simp
    then show ?thesis using a1 is_retval_ok_value_ok corr unfolding corr_def by metis
  qed
  moreover have "is_except_ok P (heap S') (except S')"
    using a1 is_except_ok_value_ok corr op unfolding corr_def by fastforce
  moreover have "(msreq M) \<subseteq> (privs S')"
    using corr op unfolding corr_def by simp
  moreover have "(privs S') \<subseteq> (the (grant P (mscname M)))"
    using corr op unfolding corr_def by simp
  ultimately show ?thesis using corr_def by simp
qed

lemma allocate_extends_heap:
  assumes new: "l \<notin> dom(H)"
  assumes op: "H' = H(l\<mapsto>obj)" 
  shows "heap_extends H H'"
  unfolding heap_extends_def obj_consistent_def using new op by auto

lemma stack_update_ok:
  assumes corr_initial: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes static: "\<Gamma>' = \<Gamma>(x\<mapsto>T)"
  assumes ok: "is_value_ok P (heap S) (intersect_label T (privs S)) v"
  assumes op: "S' = S\<lparr>stack := (stack S)(x\<mapsto>v)\<rparr>"
  shows "P M \<Gamma>' \<^bold>\<turnstile> S'"
proof -
  have "\<And>x'. var_corr P \<Gamma>' S' x'" 
  proof -
    fix x'
    show "var_corr P \<Gamma>' S' x'"
    proof (cases "x = x'")
      case True
      then show ?thesis unfolding var_corr_def op using ok static by auto
    next
      case False
      then show ?thesis using corr_initial unfolding corr_def var_corr_def static op by simp
    qed
  qed
  then show ?thesis using corr_initial unfolding corr_def op by simp
qed

lemma retval_update_ok:
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes val_ok: "is_value_ok P (heap S) (intersect_label (msreturn M) (privs S)) v"
  assumes op: "S' = S\<lparr>retval := Some v\<rparr>"
  shows "P M \<Gamma> \<^bold>\<turnstile> S'"
  using corr op val_ok unfolding corr_def is_retval_ok_def var_corr_def by simp

lemma except_update_ok:
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes val_ok: "is_value_ok P (heap S) ((ClassT Object),{}) e"
  assumes notnull: "e \<noteq> null"
  assumes op: "S' = S\<lparr>except := Some e\<rparr>"
  shows "P M \<Gamma> \<^bold>\<turnstile> S'"
  using corr op val_ok notnull unfolding corr_def is_except_ok_def var_corr_def by simp

lemma is_obj_label_ok_consistent:
  assumes "obj_consistent obj obj'"
  shows "is_obj_label_ok P obj T = is_obj_label_ok P obj' T"
  using assms unfolding is_obj_label_ok_def obj_consistent_def by simp

lemma obj_consistent_field_update: (*field_update_consistent:*)
  assumes "upd_obj = (obj\<lparr>HFields := ((HFields obj)(f\<mapsto>v))\<rparr>)"
  shows "obj_consistent obj upd_obj"
  unfolding obj_consistent_def using assms by simp

lemma heap_extends_consistent_heap_update: (* heap_update_extends_heap *)
  assumes exist: "H l' = Some obj"
  assumes "obj_consistent obj upd_obj"
  assumes op: "H' = H(l'\<mapsto>upd_obj)"
  shows "heap_extends H H'"
  unfolding heap_extends_def using assms obj_consistent_def by auto

lemma is_value_ok_heap_extends: (*is_value_ok_heap_extends*)
  assumes extends: "heap_extends H H'"
  assumes ok: "is_value_ok P H T v"
  shows "is_value_ok P H' T v"
proof (cases v)
  case (href l)
  then obtain obj where a1: "H l = Some obj \<and> (P \<turnstile> (ClassT (HClass obj)) <: (ttype T)) \<and> is_obj_label_ok P obj T" 
    using ok by auto
  then obtain obj' where "H' l = Some obj' \<and> obj_consistent obj obj'"
    using extends unfolding heap_extends_def by (metis domI domIff option.collapse option.sel) 
  then have "H' l = Some obj' \<and> (P \<turnstile> (ClassT (HClass obj')) <: (ttype T)) \<and> is_obj_label_ok P obj' T" 
    using a1 is_obj_label_ok_consistent unfolding obj_consistent_def by metis
  then show ?thesis using href by simp
next
  case null
  then show ?thesis by simp
next
  case (num x3)
  then show ?thesis using assms by simp
qed

(* is_value_ok is a shallow check, so it doesn't depend on the fields of an object *)
lemma is_value_ok_heap_update: (* heap_update_is_value_ok*)
  assumes ok: "is_value_ok P H T v"
  assumes exist: "H l = Some obj"
  assumes op: "H' = H(l\<mapsto>obj')" (* assumes op: "H' = H(l\<mapsto>(obj\<lparr>HFields := (HFields obj)(f\<mapsto>v')\<rparr>))"*)
  assumes consistent: "obj_consistent obj obj'"
  shows "is_value_ok P H' T v"
  using assms is_value_ok_heap_extends heap_extends_consistent_heap_update by metis


(* When we update the heap in a type-correct way, any set of objects that exists and is type-correct
   will continue to exist and remain type-correct. *)
lemma heap_update_heap_ok:
  assumes ok: "is_heap_ok P H"
  assumes ok': "is_value_ok P H (intersect_label (ftype fd) (HLabel obj)) v"
  assumes field: "field P (HClass obj) f = Some fd"
  assumes exist: "H l = Some obj"
  assumes upd_obj: "upd_obj = (obj\<lparr>HFields := ((HFields obj)(f\<mapsto>v))\<rparr>)"
  assumes op: "H' = H(l\<mapsto>upd_obj)"
  shows "is_heap_ok P H'"
proof -
  have a1: "\<And>T v. is_value_ok P H T v \<Longrightarrow> is_value_ok P H' T v"
    using is_value_ok_heap_update obj_consistent_field_update exist op upd_obj by blast
  have a2: "\<forall>obj. is_heapobj_ok P H obj \<longrightarrow> is_heapobj_ok P H' obj"
    using a1 unfolding is_heapobj_ok_def by blast
  (* Ascertain that the new value is shallowly OK inside the updated heap H' *)
  have "is_value_ok P H' (intersect_label (ftype fd) (HLabel obj)) v" 
    using ok' a1 by blast
  (* Then that the updated object with that value is OK. *)
  moreover have "is_heapobj_ok P H' obj" 
    using a2 ok exist unfolding is_heap_ok_def by force
  ultimately have "is_heapobj_ok P H' upd_obj" 
    unfolding is_heapobj_ok_def upd_obj using field by simp
  (* Show that for each object in the original object graph, including l, it is (shallowly) OK inside H' *)
  then have "\<forall>loc\<in>dom(H'). is_heapobj_ok P H' (the (H' loc))"
    using ok a2 op unfolding is_heap_ok_def by auto
  then show "is_heap_ok P H'" unfolding is_heap_ok_def by simp
qed

lemma heap_update_ok:
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes ok: "is_value_ok P (heap S) (intersect_label (ftype fd) (HLabel obj)) v"
  assumes exist: "heap S l' = Some obj"
  assumes field: "field P (HClass obj) f = Some fd"
  assumes upd_obj: "upd_obj = (obj\<lparr>HFields := ((HFields obj)(f\<mapsto>v))\<rparr>)"
  assumes op: "S' = S\<lparr>heap:= (heap S)(l'\<mapsto>upd_obj)\<rparr>"
  shows "P M \<Gamma> \<^bold>\<turnstile> S'"
proof -
  have a1: "\<forall>t v. is_value_ok P (heap S) t v \<longrightarrow> is_value_ok P (heap S') t v"
    using is_value_ok_heap_update obj_consistent_field_update ok exist field upd_obj op by simp
  moreover have "\<forall>x. var_corr P \<Gamma> S x" using corr unfolding corr_def by simp
  moreover have "privs S = privs S' \<and> stack S = stack S'" using op by simp
  ultimately have "\<forall>x. var_corr P \<Gamma> S' x" using op unfolding var_corr_def by metis
  moreover have "is_heap_ok P (heap S')"
   using corr_def assms heap_update_heap_ok by simp
  moreover have "is_globals_ok P (heap S') (globals S')" 
    using a1 corr is_globals_ok_value_ok op unfolding corr_def by fastforce  
  moreover have "is_retval_ok P (heap S') (intersect_label (msreturn M) (privs S')) (retval S')"
  proof -
    have "retval S' = retval S \<and> privs S' = privs S" using op by simp
    then show ?thesis using a1 is_retval_ok_value_ok corr unfolding corr_def by metis
  qed
  moreover have "is_except_ok P (heap S') (except S')"
    using a1 is_except_ok_value_ok corr op unfolding corr_def by fastforce
  moreover have "(msreq M) \<subseteq> (privs S')"
    using corr op unfolding corr_def by simp
  moreover have "(privs S') \<subseteq> (the (grant P (mscname M)))"
    using corr op unfolding corr_def by simp
  ultimately show ?thesis using corr_def by simp
qed


(*lemma heap_extends_corr:
  assumes stack_corr: "P \<Gamma> \<^bold>\<turnstile> S"
  assumes extends: "heap_extends S S'"
  assumes heap_corr: "P \<Gamma>' \<^bold>\<turnstile> S'"
  shows "P \<Gamma> \<^bold>\<turnstile> (S\<lparr>heap := (heap S')\<rparr>)"
proof -
  have "\<forall>t v. is_value_ok P (heap S) t v \<longrightarrow> is_value_ok P (heap S') t v"
    using is_value_ok_heap_extends extends by simp
  then have "(\<forall>x. var_corr P \<Gamma> (S\<lparr>heap := (heap S')\<rparr>) x)"
    using stack_corr unfolding corr_def var_corr_def by force
  then show ?thesis using heap_corr unfolding corr_def by simp
qed*)

lemma heap_extends_corr:
  assumes s0: "S0 = S\<lparr>stack := s, retval:= r, privs := p\<rparr>"
  assumes s': "S' = S1\<lparr>stack := stack S, retval := retval S, privs := privs S\<rparr>" (* i.e. S' takes the heap, globals and exception from S1 but the rest from S *)
  assumes stack_corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  assumes extends: "heap_extends (heap S0) (heap S1)"
  assumes call_corr: "(P M0 \<Gamma>0 \<^bold>\<turnstile> S1)"
  shows "(P M \<Gamma> \<^bold>\<turnstile> S')"
proof -
  have a1: "\<forall>t v. is_value_ok P (heap S) t v \<longrightarrow> is_value_ok P (heap S') t v"
    using is_value_ok_heap_extends extends s0 s' by simp
  moreover have "stack S = stack S' \<and> privs S = privs S'" using s' by simp
  ultimately have "(\<forall>x. var_corr P \<Gamma> S' x)"
    using stack_corr s' unfolding corr_def var_corr_def by metis
  moreover have "is_heap_ok P (heap S')"
    using call_corr s' unfolding corr_def by simp 
  moreover have "is_globals_ok P (heap S') (globals S')" 
    using call_corr s' unfolding corr_def by fastforce  
  moreover have "is_retval_ok P (heap S') (intersect_label (msreturn M) (privs S')) (retval S')"
  proof -
    have "(privs S = privs S') \<and> (retval S' = retval S)" using s' by simp
    then show ?thesis using a1 is_retval_ok_value_ok stack_corr unfolding corr_def by metis
  qed
  moreover have "is_except_ok P (heap S') (except S')"
    using call_corr s' unfolding corr_def by simp
  moreover have "(msreq M) \<subseteq> (privs S')"
    using stack_corr s' unfolding corr_def by simp
  moreover have "(privs S') \<subseteq> (the (grant P (mscname M)))"
    using stack_corr s' unfolding corr_def by simp
  ultimately show ?thesis unfolding corr_def by simp
qed

lemma allocate_new_object_ok:
  shows "is_heapobj_ok P H (new_object P cname label)"
  unfolding is_heapobj_ok_def new_object_def by simp

lemma allocate_new_value_ok:
  assumes op: "H' = H(l\<mapsto>(new_object P cname label))"
  assumes lbl_min: "creq (the (class P cname)) \<subseteq> label"
  assumes lbl_max: "label \<subseteq> (the (grant P cname))"
  shows "is_value_ok P H' ((ClassT cname),label) (href l)"
  using assms by (simp add: new_object_def op subtype_self is_obj_label_ok_def)

lemma globals_access_ok:
  assumes cls: "is_class P c"
  assumes field: "field P c f = Some fd"
  assumes static: "fstatic fd"
  assumes op1: "classStatics = the (globals S c)"
  assumes op2: "v = the (classStatics f)"
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  shows "is_value_ok P (heap S) (ftype fd) v"
proof -
  have "globals S c = Some classStatics \<and> is_staticfields_ok P (heap S) c classStatics"
    using corr cls op1 unfolding corr_def is_globals_ok_def by auto
  then have "(classStatics f) = Some v \<and>  is_value_ok P (heap S) (ftype fd) v"
    using field static op2 unfolding is_staticfields_ok_def by fastforce
  then show ?thesis by simp
qed

lemma globals_update_globals_ok:
  assumes globals_ok: "is_globals_ok P (heap S) (globals S)"
  assumes cls: "is_class P c"
  assumes field: "field P c f = Some fd"
  assumes static: "fstatic fd"
  assumes value_ok: "is_value_ok P (heap S) (ftype fd) v"
  assumes update: "S' = S\<lparr>globals := globals S(c \<mapsto> (the (globals S c))(f \<mapsto> v))\<rparr>"  
  shows "is_globals_ok P (heap S') (globals S')"
proof -
  have a1: "is_globals_ok P (heap S') (globals S)"
    using update globals_ok is_globals_ok_value_ok by fastforce  
  then have "globals S c \<noteq> None \<and> is_staticfields_ok P (heap S') c (the (globals S c))"
    using cls unfolding is_globals_ok_def by auto
  moreover have "is_value_ok P (heap S') (ftype fd) v"
    using update value_ok by simp
  ultimately have "globals S' c \<noteq> None \<and> is_staticfields_ok P (heap S') c (the (globals S' c))"
    unfolding is_staticfields_ok_def using field static update by simp
  then show ?thesis 
    using a1 update unfolding is_globals_ok_def by simp
qed

lemma globals_update_ok:
  assumes cls: "is_class P c"
  assumes field: "field P c f = Some fd"
  assumes static: "fstatic fd"
  assumes ok: "is_value_ok P (heap S) (ftype fd) v"
  assumes update: "S' = S\<lparr>globals := globals S(c \<mapsto> (the (globals S c))(f \<mapsto> v))\<rparr>"  
  assumes corr: "P M \<Gamma> \<^bold>\<turnstile> S"
  shows "P M \<Gamma> \<^bold>\<turnstile> S'"
proof -
  have a1: "(heap S) = (heap S')"
    using update by simp
  have "\<forall>x. var_corr P \<Gamma> S' x" 
    using corr corr_def update unfolding var_corr_def by simp
  moreover have "is_heap_ok P (heap S')"
   using corr_def corr update by simp
  moreover have "is_retval_ok P (heap S') (intersect_label (msreturn M) (privs S')) (retval S')"
    using a1 corr update unfolding corr_def is_retval_ok_def by simp
  moreover have "is_globals_ok P (heap S') (globals S')" 
    using globals_update_globals_ok corr cls field static ok update unfolding corr_def by metis
  moreover have "is_except_ok P (heap S') (except S')"
    using a1 corr update unfolding corr_def by simp
  moreover have "(msreq M) \<subseteq> (privs S')"
    using corr update unfolding corr_def by simp
  moreover have "(privs S') \<subseteq> (the (grant P (mscname M)))"
    using corr update unfolding corr_def by simp
  ultimately show ?thesis using corr_def by simp  
qed


end