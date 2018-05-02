theory javacap_auxiliary
imports
  Main
  javacap_syntax
begin   

(* Basic accessors for classes and interfaces *)
definition "class" :: "prog \<Rightarrow> (cname \<rightharpoonup> class)" where
  "class p \<equiv> map_of (pclasses p)"

definition is_class :: "prog \<Rightarrow> cname \<Rightarrow> bool" where
  "is_class p c \<equiv> (class p c) \<noteq> None"

definition interface :: "prog \<Rightarrow> (iname \<rightharpoonup> interface)" where
  "interface p \<equiv> map_of (pinterfaces p)"

definition is_interface :: "prog \<Rightarrow> iname \<Rightarrow> bool" where
  "is_interface p i \<equiv> (interface p i) \<noteq> None"

(* Is this a capability interface? *)
definition is_cap :: "prog \<Rightarrow> iname \<Rightarrow> bool" where
  "is_cap p c \<equiv> (\<exists>iface. interface p c = Some iface \<and> icap iface)"

(* Determines if the specified type exists (is defined) in the given program *)
primrec is_type :: "prog \<Rightarrow> \<tau> \<Rightarrow> bool" where
  "is_type p (ValT t) = True" |
  "is_type p (ClassT c) = is_class p c" |
  "is_type p (IfaceT c) = is_interface p c"

primrec is_cap_type :: "prog \<Rightarrow> \<tau> \<Rightarrow> bool" where
  "is_cap_type p (ValT t) = False" |
  "is_cap_type p (ClassT c) = False" |
  "is_cap_type p (IfaceT i) = is_cap p i"

definition grant :: "prog \<Rightarrow> (cname \<rightharpoonup> label)" where
  "grant p \<equiv> map_of (pgrants p)"

(* utility *)
primrec map_adds :: "('a \<rightharpoonup> 'b) list \<Rightarrow> ('a \<rightharpoonup> 'b)"  where
  "map_adds Nil = empty" |
  "map_adds (x # xs) = x ++ (map_adds xs)"

(* Auxilliary definitions *)
definition direct_subclass :: "prog \<Rightarrow> cname rel"
  where "direct_subclass p \<equiv> {(c,s). c \<noteq> Object \<and> (\<exists>cl. class p c = Some cl \<and> cextends cl = s) }"

definition direct_subinterface :: "prog \<Rightarrow> iname rel"
  where "direct_subinterface p \<equiv> {(c,s). (\<exists>i. interface p c = Some i \<and> s \<in> set (iextends i))}"

(* Reflective transitive closure. *)
abbreviation "subclass" :: "prog \<Rightarrow> cname rel"
  where "subclass p \<equiv> (direct_subclass p)\<^sup>*"

abbreviation subinterface :: "prog \<Rightarrow> iname rel"
  where "subinterface p \<equiv> (direct_subinterface p)\<^sup>*"



(* Note: subtype overrides supertype. *)
(* 'a = cname, 'b = (class \<Rightarrow> ('a \<times> 'b) list) \<Rightarrow> ('a \<rightharpoonup> 'b) *)
definition class_recursion ::"prog \<Rightarrow> cname \<Rightarrow> (cdecl \<Rightarrow> ('a \<rightharpoonup> 'b)) \<Rightarrow> ('a \<rightharpoonup> 'b)"
  where
  "class_recursion p \<equiv> wfrec ((direct_subclass p)\<inverse>) (\<lambda>rec cname f.
     case class p cname of None \<Rightarrow> undefined
        | Some cl \<Rightarrow> (if cname = Object then empty else rec (cextends cl) f) ++ (f (cname,cl)))"
  (* With the map ++ operator, the RHS overrides the LHS. Therefore, the subtype overrides the
     supertype. *)

definition interface_recursion ::  "prog \<Rightarrow> iname \<Rightarrow> (interface \<Rightarrow> ('a \<times> 'b) list) \<Rightarrow> ('a \<rightharpoonup> 'b)"
  where "interface_recursion p \<equiv> wfrec ((direct_subinterface p)\<inverse>) (\<lambda>rec (iname::iname) f. 
    case interface p iname of None \<Rightarrow> undefined 
        | Some cb \<Rightarrow> map_adds (map (\<lambda>super. rec super f) (iextends cb)) ++ map_of (f cb))"

definition cdeclmethods :: "cdecl \<Rightarrow> (mname \<rightharpoonup> (cname \<times> method))"
  where "cdeclmethods \<equiv> (\<lambda>(cn,cl). map_comp (\<lambda>m. Some (cn,m)) (map_of (cmethods cl)))"
(* equivalent to:  where "cdeclmethods \<equiv> (\<lambda>(cn,cl). map_of (map (\<lambda>(mn,meth). (mn,(cn,meth))) (cmethods cl)))"*)

(* For a given class and program name, returns a mapping
   from method names to a (declaring class name, method declaration) pair.*)
definition cmethod :: "prog \<Rightarrow> cname \<Rightarrow> (mname \<rightharpoonup> (cname \<times> method))"
  where "cmethod p c \<equiv> class_recursion p c cdeclmethods"     

definition cmethoddecl :: "prog \<Rightarrow> cname \<Rightarrow> (mname \<rightharpoonup> mdecl)"
  where "cmethoddecl p c \<equiv> map_comp (\<lambda>(cn,m). Some (mdecl m)) (cmethod p c)"

definition imethoddecl :: "prog \<Rightarrow> iname \<Rightarrow> (mname \<rightharpoonup> mdecl)"
  where "imethoddecl p c \<equiv> interface_recursion p c imethods"

definition methoddecl :: "prog \<Rightarrow> \<tau> \<Rightarrow> (mname \<rightharpoonup> mdecl)"
  where "methoddecl p t \<equiv> (case t of ValT t' \<Rightarrow> undefined | ClassT c \<Rightarrow> cmethoddecl p c | IfaceT cb \<Rightarrow> imethoddecl p cb)"

definition field :: "prog \<Rightarrow> cname \<Rightarrow> (fname \<rightharpoonup> fdecl)"
  where "field p c \<equiv> class_recursion p c (\<lambda>(cn,cl). (map_of (cfields cl)))"


(* Gets the minimal label that acts as an identity when intersected with the method parameters
   and return values of this object. *)
definition sum_method_labels :: "mdecl \<Rightarrow> label"
  where "sum_method_labels md \<equiv> (tlabel (mret md)) \<union> (\<Union>p\<in>(set (msig(mpar md))). (tlabel p))"

(* The set of all superinterfaces (including itself) of an interface *)
definition superinterface_set :: "prog \<Rightarrow> iname \<Rightarrow> iname set" 
  where "superinterface_set p ifname \<equiv> {ifname'. (ifname, ifname') \<in> (subinterface p)}"

(* The set of capabilities that can be accessed via a capability interface. It is the minimal label that acts 
   as an the identity when intersected with the label of any method return value or parameter
   of that interface.  *)
definition cap_label :: "prog \<Rightarrow> iname \<Rightarrow> label"
  where "cap_label p ifname \<equiv> (superinterface_set p ifname) \<union> 
         (let meths = imethoddecl p ifname in (\<Union>m\<in>dom(meths). sum_method_labels (the (meths m))))"
                                                                                        
(* if x is in the domain of a mapping, and the mapping is in the list,
   then x must be in the domain of the final mapping. *)
lemma map_adds_domain:
  shows "x \<in> dom m \<Longrightarrow> m \<in> (set ms) \<Longrightarrow> x \<in> dom (map_adds ms)"
proof (induction ms)
  case Nil
  then show ?case by auto (* by contradiction; the premises are not possible *)
next
  case a1: (Cons a ms)
  then show ?case
  proof (cases "m \<in> set ms")
    case b1: True
    then have "x \<in> dom (map_adds ms)" using a1 by blast (* by induction *)
    then have "x \<in> dom (map_adds (a # ms))" by auto
    then show ?thesis by simp
  next
    case b1: False
    then have "m = a" using a1 by simp
    then have "x \<in> dom (map_adds (a # ms))" using a1 by auto
    then show ?thesis by simp
  qed
qed

lemma class_unfold:
  assumes wf_subclass: "wf ((direct_subclass P)\<inverse>)"
  assumes class_exist: "class P c = Some cl"
(* prog \<Rightarrow> cname \<Rightarrow> (class \<Rightarrow> ('a \<times> 'b) list) \<Rightarrow> ('a \<rightharpoonup> 'b) *)
(*  (f::(class \<Rightarrow> ('a \<times> 'b) list)) *)
  shows "((class_recursion P c f)::('a \<rightharpoonup> 'b)) = 
          (if c = Object then empty else class_recursion P (cextends cl) f) ++ (f (c,cl))"
proof -
  define R where "R = ((direct_subclass P)\<inverse>)"
  define F where "F = (\<lambda>rec cname (f::(cdecl \<Rightarrow> ('a \<rightharpoonup> 'b))).
     case class P cname of None \<Rightarrow> undefined
        | Some cl \<Rightarrow> (if cname = Object then empty else rec (cextends cl) f) ++ (f (cname,cl)))"
  have a1: "class_recursion P = wfrec R F" unfolding R_def F_def class_recursion_def by simp
  have "wf R" unfolding R_def using wf_subclass by simp
  then have "class_recursion P c = F (cut (wfrec R F) R c) c"
    unfolding class_recursion_def using R_def F_def wfrec by simp
  then have "class_recursion P c f = (
      case class P c of None \<Rightarrow> undefined
        | Some cl \<Rightarrow> (if c = Object then empty else 
              (if ((cextends cl), c) \<in> (direct_subclass P)\<inverse> then class_recursion P (cextends cl) else undefined) f) ++ (f (c,cl))
       )" using a1 R_def unfolding F_def cut_def by metis 
  also have "... = (if c = Object then empty else class_recursion P (cextends cl) f) ++ (f (c,cl))"
    using class_exist unfolding direct_subclass_def by simp
  finally show ?thesis .
qed

lemma interface_unfold:
  assumes wf_subinterface: "wf ((direct_subinterface P)\<inverse>)"
  assumes interface_exist: "interface P c = Some cb"
  shows "((interface_recursion P c f)::('a \<rightharpoonup> 'b)) = 
        map_adds (map (\<lambda>super. interface_recursion P super f) (iextends cb)) ++ map_of (f cb)"
proof -
  define R where "R = ((direct_subinterface P)\<inverse>)"
  define F where "F = (\<lambda>rec (iname::iname) (f::(interface \<Rightarrow> ('a \<times> 'b) list)). 
    case interface P iname of None \<Rightarrow> undefined 
        | Some cb \<Rightarrow>  map_adds (map (\<lambda>super. rec super f) (iextends cb)) ++ map_of (f cb))"
  have a1: "interface_recursion P = wfrec R F" unfolding R_def F_def interface_recursion_def by simp
  have a2: "\<forall>cb'\<in>set (iextends cb). (if (cb', c) \<in> (direct_subinterface P)\<inverse> then (interface_recursion P) cb' else undefined) f = ((interface_recursion P) cb') f"
    unfolding direct_subinterface_def using interface_exist by simp

  have "wf R" unfolding R_def using wf_subinterface by simp
  then have "interface_recursion P c = F (cut (wfrec R F) R c) c"
    unfolding interface_recursion_def using R_def F_def wfrec by simp
  then have "interface_recursion P c f = (
      case interface P c of None \<Rightarrow> undefined 
        | Some cb \<Rightarrow> map_adds (map (\<lambda>super. (if (super, c) \<in> (direct_subinterface P)\<inverse> then (interface_recursion P) super else undefined) f) (iextends cb)) ++ map_of (f cb)
       )" using a1 F_def unfolding cut_def R_def by metis
  also have "... = map_adds (map (\<lambda>super. (interface_recursion P) super f) (iextends cb)) ++ map_of (f cb)"
    using interface_exist a2 map_eq_conv option.simps(5) by (metis (no_types, lifting)) 
  finally show ?thesis .
qed

lemma cmethod_unfold:
  assumes wf_subclass: "wf ((direct_subclass P)\<inverse>)"
  assumes class_exist: "class P c = Some cl"
  shows "cmethod P c = (if c = Object then empty else cmethod P (cextends cl)) ++ (cdeclmethods (c,cl))"
  using assms class_unfold unfolding cmethod_def by metis

lemma cmethod_cmethods:
  assumes wf_subclass: "wf ((direct_subclass P)\<inverse>)"
  assumes class_exist: "class P c = Some cl"
  assumes method_exist: "(map_of (cmethods cl)) mname = Some m"
  shows "cmethod P c mname = Some (c,m)"
proof -
  have "cdeclmethods (c,cl) mname = Some (c,m)"
    unfolding cdeclmethods_def using method_exist by auto
  then show ?thesis using cmethod_unfold wf_subclass class_exist by auto
qed

lemma cmethoddecl_cmethods:
  assumes wf_subclass: "wf ((direct_subclass P)\<inverse>)"
  assumes class_exist: "class P c = Some cl"
  assumes method_exist: "(map_of (cmethods cl)) mname = Some m"
  shows "cmethoddecl P c mname = Some (mdecl m)"
  using cmethod_cmethods assms unfolding cmethoddecl_def by auto

lemma field_unfold:
  assumes wf_subclass: "wf ((direct_subclass P)\<inverse>)"
  assumes class_exist: "class P c = Some cl"
  shows "field P c = (if c = Object then empty else field P (cextends cl)) ++ (map_of (cfields cl))"
proof -
  have "field P c = (if c = Object then empty else field P (cextends cl)) ++ ((\<lambda>(cn,cl). (map_of (cfields cl))) (c,cl))"
    using assms class_unfold unfolding field_def by metis
  then show ?thesis by auto
qed

lemma imethoddecl_unfold:
  assumes wf_subinterface: "wf ((direct_subinterface P)\<inverse>)"
  assumes interface_exist: "interface P c = Some cb"
  shows "imethoddecl P c = map_adds (map (\<lambda>super. imethoddecl P super) (iextends cb)) ++ map_of (imethods cb)"
  using assms interface_unfold unfolding imethoddecl_def by metis

end