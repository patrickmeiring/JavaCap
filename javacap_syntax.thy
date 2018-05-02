theory javacap_syntax
imports
  Main
begin

(* Names: class names, capability names, method names, variable names, field names *)
datatype cname = Object | ClassName "string" (* class name *)
typedecl iname (* interface name *)
typedecl mname  (* method name *)
datatype var = This | VarName "string"    (* local variable name *)
typedecl fname  (* field name*)

(* Begin syntax *)
datatype valtype = VoidT | IntT
datatype \<tau> = ValT "valtype" | ClassT "cname" | IfaceT "iname"

(* For simplicity, we diverge from the precise representation of the syntax here and 
   use more of an abstract syntax. We represent a label directly as a set of capabilities,
   rather than allowing users to name certain sets of capabilities and specify only the 
   name of that set. *)
type_synonym label = "iname set"

type_synonym \<T> = "\<tau> \<times> label"

(* Constants *)
datatype k = null | num "nat"

datatype exp =
    ref "var" 
  | new "label" "cname" 
  | calli "var" "mname" "var list" (* instance method call *)
  | calls "cname" "mname" "label" "var list" (* static method call *)
  | cast "\<tau>" "exp" 
  | const "k"
  | fieldacci "var" "fname"  (* instance field access *)
  | fieldaccs "cname" "fname" (* static field access *)
  | wrap "iname" "exp" (* make a capability *)

datatype stmt =
    assign "var" "exp" 
  | assignfi "var" "fname" "exp" 
  | assignfs "cname" "fname" "exp" 
  | expr "exp"
  | ifelse "var" "stmt" "stmt" 
  | letin "\<T>" "var" "exp" "stmt"
  | return "exp"
  | seq "stmt" "stmt" 
  | throw "exp"
  | trycatch "stmt" "(\<tau> \<times> var \<times> stmt) list"

type_synonym catchhandler = "\<tau> \<times> var \<times> stmt"
type_synonym msig = "\<T> list"
type_synonym mpar = "(var \<times> \<T>) list"

record mdecl =
  mstatic :: "bool" (* is it static? *)
  mpar :: "mpar"
  mret :: "\<T>"

record method =
  mdecl :: "mdecl" (* declaration *)
  mstmt :: "stmt option" (* statement *)
  mreq :: "label" (* requires clause *)

record fdecl =
  fstatic :: "bool" (* is it static? *)
  ftype :: "\<T>"

type_synonym fentry = "fname \<times> fdecl"

type_synonym mentry = "mname \<times> method"

type_synonym msentry = "mname \<times> mdecl"

(* class declaration body *)
record "class" =
  cextends :: "cname"
  cimpl :: "iname list"
  cfields :: "fentry list" 
  cmethods :: "mentry list"
  creq :: "label" (* requires clause for class instances *)

(* interface declaration body *)
record interface = 
  icap :: "bool" (* is this a 'capability'? *)
  iextends :: "iname list"
  imethods :: "msentry list"

(* interface declaration *)
type_synonym ifdecl = "iname \<times> interface"

(* class declaration *)
type_synonym cdecl = "cname \<times> class"

(* a line in the policy file that defines which capabilities each class can use *)
type_synonym grant = "cname \<times> label"

record prog = 
  pinterfaces :: "ifdecl list"
  pclasses :: "cdecl list"
  pentryclass :: "cname"
  pentrymethod :: "mname"
  pgrants :: "grant list" 

(* Helpers to use syntax. *)
(* Obtains the method signature from a list of parameters. The signature 
   incorporates only the types of each parameter, rather than their names as well. *)
abbreviation msig :: "mpar \<Rightarrow> msig"
  where "msig pars \<equiv> (map snd pars)"

(* accessors for lbltype *)
abbreviation ttype :: "\<T> \<Rightarrow> \<tau>"
  where "ttype \<equiv> fst"

abbreviation tlabel :: "\<T> \<Rightarrow> label"
  where "tlabel \<equiv> snd"

abbreviation chtype :: "catchhandler \<Rightarrow> \<tau>"
  where "chtype ch \<equiv> fst ch"

abbreviation chvar :: "catchhandler \<Rightarrow> var"
  where "chvar ch \<equiv> fst (snd ch)"

abbreviation chstmt :: "catchhandler \<Rightarrow> stmt"
  where "chstmt ch \<equiv> snd (snd ch)"

(* Convenience function to obtain interface name from type *)
primrec the_iname :: "\<tau> \<Rightarrow> iname"
  where "the_iname (ValT v) = undefined" | 
        "the_iname (ClassT c) = undefined" |
        "the_iname (IfaceT i) = i"

end