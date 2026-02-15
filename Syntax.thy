theory "Syntax"
imports
  Complex_Main
  "Identifiers"
begin

section \<open>Syntax\<close>

text \<open>This section defines the syntax of the Dynamic Logic of Communicating Hybrid Programs (dLCHP) 
as inductively defined data types (\<open>https://doi.org/10.1007/978-3-031-38499-8_6\<close>).
Since dLCHP's syntax is context-sensitive, the data types, in fact, define a superset of the syntax. 
Well-formedness predicates characterize the actual syntax of dLCHP as a subset of these data types.\<close>

text \<open>The formalization used the formalization of Differential Game Logic (dGL) 
(\<open>https://www.isa-afp.org/entries/Differential_Game_Logic.html\<close>) as a starting point, thus has a
similar structure. However, the semantical foundations of parallel hybrid dynamics and game dynamics 
are of considerable difference, which prevents actual reuse of the dGL formalization.\<close>

subsection \<open>Signature\<close>

text \<open>The set of all identifiers\<close>
abbreviation allidents :: "ident set"
  where "allidents \<equiv> UNIV"

text \<open>Real variables and differential (primed) variables\<close>
datatype rvar =
  RVarName (rvarname: ident)
| DVarName (dvarname: ident)

definition is_primed :: "rvar \<Rightarrow> bool"
  where "is_primed x = (\<exists>y. x = DVarName y)"

text \<open>The global time \<mu> and its pace \<mu>' are reserved real variables, which serve the purpose of
synchronizing the duration of parallel continuous dynamics.\<close>
definition gtime :: "rvar" ("\<mu>") where "gtime \<equiv> RVarName (hd ''g'')"
definition gtime_pace :: "rvar" ("\<mu>p") where "gtime_pace \<equiv> DVarName (hd ''g'')"

text \<open>Trace variables\<close>
datatype tvar = TVarName (tvarname: ident) (* datatype is used to avoid confusion with channel names *)

text \<open>Channel names\<close>
datatype chan = ChanName (chname: ident)

datatype variable = Rv (getrv: rvar) | Tv (gettv: tvar)

text \<open>A communication event occurs on a certain channel and the event is appended to the recorder 
variable of the program that emitted the event. This appending to the recorder particularly takes 
effect on the subtrace of the recorder associated with the channel name.\<close>
type_synonym comtar = "tvar \<times> chan" (* comtar is short for communication target *)

abbreviation isRv :: "variable \<Rightarrow> bool" where "isRv z \<equiv> (\<exists>v. z = Rv v)"
abbreviation isTv :: "variable \<Rightarrow> bool" where "isTv z \<equiv> (\<exists>v. z = Tv v)"

definition iota_rvars :: "rvar set \<Rightarrow> variable set" ("\<iota>\<^sub>R")
  where "\<iota>\<^sub>R X = { Rv x | x. x \<in> X }"
definition iota_tvars :: "tvar set \<Rightarrow> variable set" ("\<iota>\<^sub>T")
  where "\<iota>\<^sub>T X = { Tv x | x. x \<in> X }"

definition pi_rvars :: "variable set \<Rightarrow> rvar set" ("\<pi>\<^sub>R") 
  where "\<pi>\<^sub>R X = {x | x. Rv x \<in> X}"
definition pi_tvars :: "variable set \<Rightarrow> tvar set" ("\<pi>\<^sub>T")
  where "\<pi>\<^sub>T X = {x | x. Tv x \<in> X}"

text \<open>Variables can be bound by programs and quantifiers, and variables are called free in an 
expression if their value has an impact on the evaluation of that expression. Communication targets
represent that communication events bind trace variables but only change the subtrace associated 
with the channel of that event. Likewise, a communication target is free in an expression if the 
evaluation of the expression depends on the subtrace. Since variables and communication targets 
behave equally in many aspects, they are summarized as bindables.\<close>
datatype bindr = Bv variable | Bc tvar chan (* binder with e is a reserved word *)

definition iota_vars :: "variable set \<Rightarrow> bindr set" ("\<iota>\<^sub>V")
  where "\<iota>\<^sub>V X = {Bv z | z. z \<in> X}"
definition iota_comtar :: "comtar set \<Rightarrow> bindr set" ("\<iota>\<^sub>C")
  where "\<iota>\<^sub>C W = {Bc h ch | h ch. (h, ch) \<in> W}" 

definition pi_vars :: "bindr set \<Rightarrow> variable set" ("\<pi>\<^sub>V")
  where "\<pi>\<^sub>V U = {z | z. Bv z \<in> U}"
definition pi_comtar :: "bindr set \<Rightarrow> comtar set" ("\<pi>\<^sub>C")
  where "\<pi>\<^sub>C U = { (h, ch) | h ch. Bc h ch \<in> U}"
definition pi_newtar :: "bindr set \<Rightarrow> comtar set" ("\<pi>\<^sub>N")
  where "\<pi>\<^sub>N U = { (h, ch) | h ch. Bv (Tv h) \<in> U \<or> Bc h ch \<in> U}"



paragraph \<open>Basic Sets of Names\<close>

text \<open>The set of all unprimed real variables\<close>
abbreviation alluvars :: "rvar set"
  where "alluvars \<equiv> {RVarName x | x. True}"

text \<open>The set of all differential variables\<close>
abbreviation alldvars :: "rvar set"
  where "alldvars \<equiv> {DVarName x | x. True}"

definition gtset :: "variable set" ("\<V>\<^sub>\<mu>")
  where "gtset \<equiv> { Rv \<mu>, Rv \<mu>p }"

text \<open>The set of all real variables (primed and unprimed)\<close>
abbreviation allrvars:: "rvar set" ("\<V>\<^sub>R")
  where "\<V>\<^sub>R \<equiv> UNIV"

text \<open>The set of all trace variables\<close>
abbreviation alltvars:: "tvar set" ("\<V>\<^sub>T")
  where "alltvars \<equiv> UNIV"

text \<open>The set of all variables of any type\<close>
abbreviation allvars:: "variable set" ("\<V>")
  where "allvars \<equiv> UNIV"

text \<open>The set of all channel names\<close>
abbreviation allchans:: "chan set" ("\<Omega>")
  where "allchans \<equiv> UNIV"



paragraph \<open>Relations Between the Syntactic Categories\<close>

lemma rvars_compl [simp]: "-\<iota>\<^sub>R \<V>\<^sub>R = \<iota>\<^sub>T \<V>\<^sub>T" 
  apply (auto simp add: iota_rvars_def iota_tvars_def)
  by (meson variable.exhaust)

lemma tvars_compl [simp]: "-\<iota>\<^sub>T \<V>\<^sub>T = \<iota>\<^sub>R \<V>\<^sub>R" using rvars_compl by blast

lemma inR_mono [simp, intro]: "V \<subseteq> W \<Longrightarrow> \<iota>\<^sub>R V \<subseteq> \<iota>\<^sub>R W" by (auto simp add: iota_rvars_def)
lemma inT_mono [simp, intro]: "V \<subseteq> W \<Longrightarrow> \<iota>\<^sub>T V \<subseteq> \<iota>\<^sub>T W" by (auto simp add: iota_tvars_def)

lemma compose_allvars: "\<V> = (\<iota>\<^sub>R \<V>\<^sub>R \<union> \<iota>\<^sub>T \<V>\<^sub>T)"
  apply (auto simp add: iota_rvars_def iota_tvars_def)
  using variable.exhaust by meson

lemma rvars_not_tvars: "\<iota>\<^sub>R \<V>\<^sub>R \<subseteq> -\<iota>\<^sub>T \<V>\<^sub>T" by auto



paragraph \<open>Laws for Injections and Projections of Names\<close>

lemma in_pi_rvars [simp]: "x \<in> \<pi>\<^sub>R X = (Rv x \<in> X)" by (simp add: pi_rvars_def)
lemma in_pi_tvars [simp]: "h \<in> \<pi>\<^sub>T X = (Tv h \<in> X)" by (simp add: pi_tvars_def)

lemma in_iota_rvars [simp]: "Rv x \<in> \<iota>\<^sub>R X = (x \<in> X)" by (simp add: iota_rvars_def)
lemma in_iota_tvars [simp]: "Tv h \<in> \<iota>\<^sub>T X = (h \<in> X)" by (simp add: iota_tvars_def)

lemma rvar_no_tvar [simp]: "Rv x \<notin> \<iota>\<^sub>T Y" by (simp add: iota_tvars_def)
lemma tvar_no_rvar [simp]: "Tv h \<notin> \<iota>\<^sub>R X" by (simp add: iota_rvars_def)

lemma rvars_of_rvars [simp]: "\<pi>\<^sub>R (\<iota>\<^sub>R X) = X" by auto
lemma tvars_of_tvars [simp]: "\<pi>\<^sub>T (\<iota>\<^sub>T X) = X" by auto
lemma tvars_of_rvars [simp]: "\<pi>\<^sub>T (\<iota>\<^sub>R X) = {}" by auto
lemma rvars_of_tvars [simp]: "\<pi>\<^sub>R (\<iota>\<^sub>T X) = {}" by auto

lemma iota_rvars_mono [simp, intro]: "\<iota>\<^sub>R X \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R" by (auto simp add: iota_rvars_def)
lemma iota_tvars_mono [simp, intro]: "\<iota>\<^sub>T X \<subseteq> \<iota>\<^sub>T \<V>\<^sub>T" by (auto simp add: iota_tvars_def)

lemma iota_vars_mono: "X \<subseteq> V \<Longrightarrow> \<iota>\<^sub>V X \<subseteq> \<iota>\<^sub>V V" by (auto simp add: iota_vars_def)
lemma iota_comtar_mono: "C \<subseteq> Y \<Longrightarrow> \<iota>\<^sub>C C \<subseteq> \<iota>\<^sub>C Y" by (auto simp add: iota_comtar_def)
lemma pi_vars_mono [simp, intro]: "Z \<subseteq> U \<Longrightarrow> \<pi>\<^sub>V Z \<subseteq> \<pi>\<^sub>V U" by (auto simp add: pi_vars_def)
lemma pi_comtar_mono [simp, intro]: "Z \<subseteq> U \<Longrightarrow> \<pi>\<^sub>C Z \<subseteq> \<pi>\<^sub>C U" by (auto simp add: pi_comtar_def)

lemma comtar_mono: "\<iota>\<^sub>C C \<subseteq> Z \<Longrightarrow> C \<subseteq> \<pi>\<^sub>C Z" apply (simp add: iota_comtar_def pi_comtar_def) by blast

lemma iota_rvars_empty [simp]: "\<iota>\<^sub>R {} = {}" by (simp add: iota_rvars_def)
lemma iota_tvars_empty [simp]: "\<iota>\<^sub>T {} = {}" by (simp add: iota_tvars_def)
lemma iota_vars_empty [simp]: "\<iota>\<^sub>V {} = {}" by (simp add: iota_vars_def)
lemma iota_comtar_empty [simp]: "\<iota>\<^sub>C {} = {}" by (simp add: iota_comtar_def)

lemma time_is_real [simp, intro]: "\<V>\<^sub>\<mu> \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R" by (simp add: gtset_def)



subsection \<open>Spaces\<close>

text \<open>Spaces are symbolic representations of sets of variables and channels (names). They combine a
boolean algebra of sets (top element, singletons, and standard set operators) with symbolic 
constants representing sets that are subject to the interpretation.\<close>

text \<open>A cspace represents a set of channel names\<close>  
datatype cspace =
  CTop ("\<top>\<^sub>\<Omega>") (* all channel names \<Omega> *)
| CChan chan
| CConst ident
| CCompl cspace ("-\<^sub>\<Omega>")
| CCap cspace cspace (infixr "\<inter>\<^sub>\<Omega>" 100)

text \<open>A bspace represents a set of variables\<close>  
datatype vspace =
  VRTop ("\<top>\<^sub>R") (* all real variables \<V>\<^sub>R; the set of all variables \<V> is definable on top of this *)
| VRVar rvar
| VTVar tvar
| VRConst ident
| VCompl vspace ("-\<^sub>V")
| VCap vspace vspace (infixr "\<inter>\<^sub>V" 100)

paragraph \<open>Derived Spaces\<close>

definition CBot :: "cspace" ("\<bottom>\<^sub>\<Omega>")
  where "CBot = -\<^sub>\<Omega> \<top>\<^sub>\<Omega>"

definition CCup :: "cspace \<Rightarrow> cspace \<Rightarrow> cspace" (infixr "\<union>\<^sub>\<Omega>" 10)
   where "CCup C Y = -\<^sub>\<Omega> (-\<^sub>\<Omega> C \<inter>\<^sub>\<Omega> -\<^sub>\<Omega> Y)"

definition VTTop :: "vspace" ("\<top>\<^sub>T") (* all trace variables \<V>\<^sub>T *)
  where "VTTop = -\<^sub>V \<top>\<^sub>R" 

definition VCup :: "vspace \<Rightarrow> vspace \<Rightarrow> vspace" (infixr "\<union>\<^sub>V" 100)
  where "VCup X Z = -\<^sub>V ((-\<^sub>V X) \<inter>\<^sub>V (-\<^sub>V Z))"

definition VTop :: "vspace" ("\<top>\<^sub>V") (* all variables *)
  where "VTop = \<top>\<^sub>R \<union>\<^sub>V \<top>\<^sub>T"

definition VBot :: "vspace"  ("\<bottom>\<^sub>V")
  where "VBot = (-\<^sub>V \<top>\<^sub>V)"

definition RCompl :: "vspace \<Rightarrow> vspace" ("-\<^sub>R")
  where "RCompl X = (-\<^sub>V X) \<inter>\<^sub>V \<top>\<^sub>R"

definition RCup :: "vspace \<Rightarrow> vspace \<Rightarrow> vspace" (infixr "\<union>\<^sub>R" 100)
  where "RCup X Z = -\<^sub>R ((-\<^sub>R X) \<inter>\<^sub>V (-\<^sub>R Z))"

definition BRvSet :: "rvar list \<Rightarrow> vspace" (* list of real variables *)
  where "BRvSet xs = foldr RCup (map VRVar xs) \<bottom>\<^sub>V"
     
text \<open>Every rspace expression represents a set of real variables\<close>
inductive_set rspace :: "vspace set"
  where
   "\<bottom>\<^sub>V \<in> rspace"
|  "\<top>\<^sub>R \<in> rspace"
| "(VRVar x) \<in> rspace"
| "(VRConst i) \<in> rspace"
| "X \<in> rspace \<or> Z \<in> rspace \<Longrightarrow> (X \<inter>\<^sub>V Z) \<in> rspace"
| "X \<in> rspace \<Longrightarrow> (RCompl X) \<in> rspace"
| "X \<in> rspace \<Longrightarrow> Z \<in> rspace \<Longrightarrow> -\<^sub>R ((-\<^sub>R X) \<inter>\<^sub>V (-\<^sub>R Z)) \<in> rspace"

lemma VTVar_no_rspace [simp]: "VTVar h \<notin> rspace"
  by (metis VBot_def RCompl_def rspace.cases vspace.distinct(11,19,21,23,3))

lemma RCup_rspace [simp, intro]: "X \<in> rspace \<Longrightarrow> Z \<in> rspace \<Longrightarrow> X \<union>\<^sub>R Z \<in> rspace" 
  by (simp add: RCup_def rspace.intros(7))

lemma BRvSet_rspace [simp, intro]: "BRvSet xs \<in> rspace"
  apply (induction xs)
   apply (simp_all add: BRvSet_def rspace.intros(1))
  using rspace.intros(3) by blast



subsection \<open>Terms\<close>

text \<open>Numeric literals\<close>
type_synonym rlit = real

text \<open>rtrm are real polynomials in rvars plus constant and function symbols and operators on trace 
terms ttrm. ttrm represents traces of communication events. Pure real polynomials are characterized 
as subset of rtrm. Real constant and function symbols have a boolean flag that restricts their 
evaluation to pure real polynomials.\<close>
datatype rtrm =
  RVar rvar
| RConst bool ident nat    
| RFunc  bool ident vspace "arg list"
| Number rlit
| Plus rtrm rtrm
| Times rtrm rtrm
| ChanOf ttrm
| ValOf ttrm
| TimeOf ttrm
| LenT ttrm
and ttrm =
  TVar tvar
| TConst ident nat
| TFunc ident vspace "arg list"
| Empty
| ComItm chan rtrm rtrm 
| Concat ttrm ttrm          (infixr "\<circ>\<^sub>T" 100)
| Proj ttrm cspace
| Access ttrm rtrm
and arg =
  RArg (rarg: rtrm)
| TArg (targ: ttrm)

datatype trm = Trtrm rtrm | Tttrm ttrm



paragraph \<open>Derived Terms\<close>

definition Neg ::"rtrm \<Rightarrow> rtrm" 
  where "Neg \<theta> = Times (Number (-1)) \<theta>"

definition Minus ::"rtrm \<Rightarrow> rtrm \<Rightarrow> rtrm"
  where "Minus \<theta> \<eta> = Plus \<theta> (Neg \<eta>)"

definition Dec :: "rtrm \<Rightarrow> rtrm"
  where "Dec \<theta> \<equiv> Minus \<theta> (Number 1)"



subsection \<open>Formulas and Communicating Hybrid Programs\<close>

text \<open>The formulas of dLCHP combine first-order dynamic logic as in differential dynamic logic with 
assumption-commitment reasoning.
The programs combine hybrid programs from dL with CSP-style communication and parallelism, i.e. 
parallel programs do not share state but can communicate via channels.
Communication takes place on a channel whenever a program and its environment can agree on the value 
and time of the communication on that channel.
For uniform substitution, the syntax features predicate symbols, program symbols, and system symbols,
which receive their meaning from the interpretation.\<close>
datatype fml =
\<comment> \<open>The predicate symbol p(b)(Z)(\<Theta>) depends on the arguments \<Theta> and on the variables Z. If the 
boolean flag b is set to true, the symbol is interpreted as a formula of first-order arithmetic.\<close>
  GPsymb bool ident vspace "arg list"
| Geq rtrm rtrm           ("_ \<ge>\<^sub>R _" [51,51] 50)
| Pref ttrm ttrm          ("(_ \<preceq>\<^sub>T _)" [51, 51] 50)
| Not fml                 ("!")
| And fml fml             (infixr "&&" 8)
| Exists variable fml
| Box chp fml             ("([[ _ ]] _)" 20)
| AcBox chp fml fml fml   
| ChanIn rtrm cspace      ("_ \<in>\<^sub>C _" [51, 51] 50)
and chp =
\<comment> \<open>The program symbol a(Z, Y) synchronizes on the channels Y, has free and bound variables Z\<close>
  Chp ident vspace cspace
| Assign rvar rtrm     (infixr ":=" 20)
| Nondet rvar          ("_ := *")
| Test fml                ("?")
| Evolution ident rtrm fml
| Choice chp chp        (infixr "\<union>\<union>" 10)
| Compose chp chp       (infixr ";;" 8)
| Loop chp               ("_**")
| Send chan tvar rtrm   
| Receive chan tvar rvar 
| Par chp chp           (infixr "par" 6)

datatype expr = Ertrm rtrm | Ettrm ttrm | Earg arg | Efml fml

text \<open>The class expr provides syntactic sugar especially for the theory Coincidence\<close>
class expr =
  fixes Ein :: "'a \<Rightarrow> expr"

instantiation rtrm :: expr
begin
definition "Ein (\<theta>::rtrm) = Ertrm \<theta>"
instance ..
end

instantiation ttrm :: expr
begin
definition "Ein (te::ttrm) = Ettrm te"
instance ..
end

instantiation arg :: expr
begin
definition "Ein (\<phi>::arg) = Earg \<phi>"
instance ..
end

instantiation fml :: expr
begin
definition "Ein (\<phi>::fml) = Efml \<phi>"
instance ..
end



paragraph \<open>Derived Logical Connectives and Programs\<close>

text \<open>Arbitrary real constant symbol\<close>
definition GRConst :: "ident \<Rightarrow> nat \<Rightarrow> rtrm"
  where "GRConst f n = RConst False f n"

text \<open>Real constant symbol evaluating to a pure real polynomial\<close>
definition QRConst :: "ident \<Rightarrow> nat \<Rightarrow> rtrm"
  where "QRConst f n = RConst True f n"

text \<open>Real function symbol evaluating to a pure real polynomial\<close>
definition QRFunc :: "ident \<Rightarrow> rtrm list \<Rightarrow> rtrm"
  where "QRFunc f \<Theta> = RFunc True f \<bottom>\<^sub>V (map RArg \<Theta>)"

text \<open>Arbitrary predicate symbol\<close>
definition Psymb :: "ident \<Rightarrow> vspace \<Rightarrow> arg list \<Rightarrow> fml"
  where "Psymb p Z \<Theta> = GPsymb False p Z \<Theta>"

text \<open>Predicate symbol evaluating to first-order real arithmetic\<close>
definition QRGPsymb :: "ident \<Rightarrow> rtrm list \<Rightarrow> fml"
  where "QRGPsymb p \<Theta> = GPsymb True p \<bottom>\<^sub>V (map RArg \<Theta>)"

definition REquals :: "rtrm \<Rightarrow> rtrm \<Rightarrow> fml" ("_ =\<^sub>R _" [51,51] 50)
  where "REquals \<theta> \<theta>' = ((Geq \<theta> \<theta>') && (Geq \<theta>' \<theta>))"

definition Greater :: "rtrm \<Rightarrow> rtrm \<Rightarrow> fml" ("_ >\<^sub>R _" [51,51] 50)
  where "Greater \<theta> \<theta>' = (Not (Geq \<theta>' \<theta>))"

definition RNeq :: "rtrm \<Rightarrow> rtrm \<Rightarrow> fml" ("_ \<noteq>\<^sub>R _" [51, 51] 50)
  where "RNeq \<theta> \<theta>' = !(\<theta> =\<^sub>R \<theta>')"

definition TEquals :: "ttrm \<Rightarrow> ttrm \<Rightarrow> fml" ("_ =\<^sub>T _" [51,51] 50)
  where "TEquals te\<^sub>1 te\<^sub>2 = ((te\<^sub>1 \<preceq>\<^sub>T te\<^sub>2) && (te\<^sub>2 \<preceq>\<^sub>T te\<^sub>1))"

definition SPref :: "ttrm \<Rightarrow> ttrm \<Rightarrow> fml" ("_ \<prec>\<^sub>T _ " [51,51] 50)
  where "SPref te' te = ((te' \<preceq>\<^sub>T te) && !(te' =\<^sub>T te))"

definition Or :: "fml \<Rightarrow> fml \<Rightarrow> fml" (infixr "||" 7)
  where "Or P Q = Not (And (Not P) (Not Q))"

definition Implies :: "fml \<Rightarrow> fml \<Rightarrow> fml" (infixr "\<rightarrow>" 10)
  where "Implies P Q = Or Q (Not P)"

definition Equiv :: "fml \<Rightarrow> fml \<Rightarrow> fml" (infixr "\<leftrightarrow>" 10)
  where "Equiv P Q = Or (And P Q) (And (Not P) (Not Q))"

definition Forall :: "variable \<Rightarrow> fml \<Rightarrow> fml"
  where "Forall z P = Not (Exists z (Not P))"

definition Diamond :: "chp \<Rightarrow> fml \<Rightarrow> fml" ("(\<langle>_\<rangle>_)" 20)
  where "Diamond \<alpha> P = Not (Box \<alpha> (Not P))"

definition AcDia :: "chp \<Rightarrow> fml \<Rightarrow> fml \<Rightarrow> fml \<Rightarrow> fml"
  where "AcDia \<alpha> A C P = Not (AcBox \<alpha> A (Not C) (Not P))"

definition ChanNotIn :: "rtrm \<Rightarrow> cspace \<Rightarrow> fml" ("_ \<notin>\<^sub>C _" [51, 51] 50)
  where "ChanNotIn ch Y = !(ch \<in>\<^sub>C Y)"

definition TT ::"fml" 
  where "TT = Geq (Number 0) (Number 0)"

definition FF ::"fml" 
  where "FF = Geq (Number 0) (Number 1)"

definition Skip ::"chp" 
  where "Skip = Test TT"

text \<open>Syntactical repetition of a CHP as repeated sequential composition\<close>
fun Repeat :: "chp \<Rightarrow> nat \<Rightarrow> chp"
  where
  "Repeat \<alpha> 0 = ? TT"
| "Repeat \<alpha> (Suc n) = (\<alpha> ;; (Repeat \<alpha> n))"

text \<open>Inference: premises, then conclusion\<close>
type_synonym inference = "fml list * fml"

text \<open>Sequent: premises, then conclusions\<close>
type_synonym sequent = "fml list * fml list"

text \<open>Rule: premises, then conclusion\<close>
type_synonym rule = "sequent list * sequent"



subsection \<open>Well-formed Syntax\<close>

text \<open>dLCHP has a context-sensitive syntax, which restricts the terms and formulas that may occur in
programs, the variables that may be shared between parallel programs, and ac-formulas that specify a
program in a ac-modality. The restrictions on programs are due to the fact that communicating hybrid 
programs model distributed hybrid systems, thus operate over the real-valued state and do not share 
bound variables in parallel. The restriction of ac-modalities ensures that ac-formulas only specify
observable communication.\<close>

text \<open>Pure real polynomials are polynomials over real variables\<close>
fun isQRpolynom :: "rtrm \<Rightarrow> bool" and
    isQRarg :: "arg \<Rightarrow> bool"
where
  "isQRpolynom (RVar x) = True"
| "isQRpolynom (RConst b f n) = b"
| "isQRpolynom (RFunc b f Z \<Theta>) = (b \<and> Z = \<bottom>\<^sub>V \<and> list_all isQRarg \<Theta>)"
| "isQRpolynom (Number l) = True"                        
| "isQRpolynom (Plus \<theta>1 \<theta>2) = (isQRpolynom \<theta>1 \<and> isQRpolynom \<theta>2)"
| "isQRpolynom (Times \<theta>1 \<theta>2) = (isQRpolynom \<theta>1 \<and> isQRpolynom \<theta>2)"
| "isQRpolynom _ = False"

| "isQRarg (RArg \<theta>) = isQRpolynom \<theta>"
| "isQRarg (TArg te) = False"

text \<open>First-order real-arithmetic are the first-order formulas over pure real polynomials\<close>
fun isFOL\<^sub>R :: "fml \<Rightarrow> bool" where
  "isFOL\<^sub>R (GPsymb b p Z \<Theta>) = (b \<and> Z = \<bottom>\<^sub>V \<and> list_all isQRarg \<Theta>)"
| "isFOL\<^sub>R (Geq \<theta>1 \<theta>2) = (isQRpolynom \<theta>1 \<and> isQRpolynom \<theta>2)"
| "isFOL\<^sub>R (Not \<phi>) = (isFOL\<^sub>R \<phi>)"
| "isFOL\<^sub>R (And \<phi> \<psi>) = (isFOL\<^sub>R \<phi> \<and> isFOL\<^sub>R \<psi>)"
| "isFOL\<^sub>R (Exists (Rv z) \<phi>) = (isFOL\<^sub>R \<phi>)"
| "isFOL\<^sub>R _ = False"

fun wf_rtrm :: "rtrm \<Rightarrow> bool" and
    wf_ttrm :: "ttrm \<Rightarrow> bool" and
    wf_arg :: "arg \<Rightarrow> bool"
  where
  "wf_rtrm (RVar x) = True"
| "wf_rtrm (RConst b c n) = True"
| "wf_rtrm (RFunc b f Z \<Theta>) = (list_all wf_arg \<Theta> \<and> (b \<longrightarrow> Z = \<bottom>\<^sub>V \<and> list_all isQRarg \<Theta>))" 
| "wf_rtrm (Number l) = True"
| "wf_rtrm (Plus \<theta> \<eta>) = (wf_rtrm \<theta> \<and> wf_rtrm \<eta>)"
| "wf_rtrm (Times \<theta> \<eta>) = (wf_rtrm \<theta> \<and> wf_rtrm \<eta>)"
| "wf_rtrm (ChanOf te) = wf_ttrm te"
| "wf_rtrm (ValOf te) = wf_ttrm te"
| "wf_rtrm (TimeOf te) = wf_ttrm te"
| "wf_rtrm (LenT te) = wf_ttrm te"

| "wf_ttrm (TVar h) = True"
| "wf_ttrm (TConst c n) = True"
| "wf_ttrm (TFunc f Z \<Theta>) = list_all wf_arg \<Theta>"
| "wf_ttrm Empty = True"
| "wf_ttrm (ComItm ch \<eta>\<^sub>1 \<eta>\<^sub>2) = (isQRpolynom \<eta>\<^sub>1 \<and> isQRpolynom \<eta>\<^sub>2)" 
| "wf_ttrm (Concat te\<^sub>1 te\<^sub>2) = (wf_ttrm te\<^sub>1 \<and> wf_ttrm te\<^sub>2)" 
| "wf_ttrm (Proj te Y) = wf_ttrm te"
| "wf_ttrm (Access te \<theta>) = (wf_ttrm te \<and> wf_rtrm \<theta>)"

| "wf_arg (RArg \<eta>) = wf_rtrm \<eta>"
| "wf_arg (TArg te) = wf_ttrm te"

text \<open>A program is well-formed if all terms are pure real polynomials and all formulas in tests and
domain constraints are formulas of first-order real-arithmetic. Further, parallel programs must not 
share bound variables. The ac-formulas in ac-modalities may only specify behavior observable by the
environment, thus must not read variables bound by the program.\<close>

text \<open>Well-formedness relies on the notions of free variables of formulas and bound variables of
programs that is provided by the static semantics.\<close>
record wf_stat_sem =
  FNE\<^sub>\<L> :: "expr \<Rightarrow> bindr set"
  BNP\<^sub>\<L> :: "chp \<Rightarrow> bindr set"


record stat_sem = wf_stat_sem + 
  FVP\<^sub>\<L> :: "chp \<Rightarrow> variable set" (* over-approximate free variables of program *)
  CNC\<^sub>\<L> :: "cspace \<Rightarrow> chan set" (* over-approximate channel names *)
  UACN\<^sub>\<L> :: "cspace \<Rightarrow> chan set" (* under-approximate channel names *)
  FVV\<^sub>\<L> :: "vspace \<Rightarrow> variable set" (* over-approximate variable names *)
  UAV\<^sub>\<L> :: "vspace \<Rightarrow> variable set" (* under-approximate variable names *)

definition FVE\<^sub>\<L> :: "'a wf_stat_sem_scheme \<Rightarrow> expr \<Rightarrow> variable set"
  where "FVE\<^sub>\<L> \<L> e = \<pi>\<^sub>V (FNE\<^sub>\<L> \<L> e)"

definition BVP\<^sub>\<L> :: "'a wf_stat_sem_scheme \<Rightarrow> chp \<Rightarrow> variable set"
  where "BVP\<^sub>\<L> \<L> \<alpha> = \<pi>\<^sub>V (BNP\<^sub>\<L> \<L> \<alpha>)"

definition CNP\<^sub>\<L> :: "'a wf_stat_sem_scheme \<Rightarrow> chp \<Rightarrow> comtar set"
  where "CNP\<^sub>\<L> \<L> \<alpha> = \<pi>\<^sub>C (BNP\<^sub>\<L> \<L> \<alpha>)"

definition CNV\<^sub>\<L> :: "stat_sem \<Rightarrow> vspace \<Rightarrow> comtar set"
  where "CNV\<^sub>\<L> \<L> Z = \<pi>\<^sub>T (FVV\<^sub>\<L> \<L> Z) \<times> \<Omega>"

definition FVN\<^sub>\<L> :: "stat_sem \<Rightarrow> vspace \<Rightarrow> bindr set"
  where "FVN\<^sub>\<L> \<L> Z = \<iota>\<^sub>V (FVV\<^sub>\<L> \<L> Z) \<union> \<iota>\<^sub>C (CNV\<^sub>\<L> \<L> Z)"


fun wf_fml :: "'a wf_stat_sem_scheme \<Rightarrow> fml \<Rightarrow> bool" and 
    wf_chp :: "'a wf_stat_sem_scheme \<Rightarrow> chp \<Rightarrow> bool"
  where
  "wf_fml \<L> (GPsymb b p Z \<Theta>) = (list_all wf_arg \<Theta> \<and> (b \<longrightarrow> Z = \<bottom>\<^sub>V \<and> list_all isQRarg \<Theta>))"
| "wf_fml \<L> (Geq \<theta>\<^sub>1 \<theta>\<^sub>2) = (wf_rtrm \<theta>\<^sub>1 \<and> wf_rtrm \<theta>\<^sub>2)"
| "wf_fml \<L> (Pref te\<^sub>1 te\<^sub>2) = (wf_ttrm te\<^sub>1 \<and> wf_ttrm te\<^sub>2)"
| "wf_fml \<L> (Not \<phi>) = (wf_fml \<L> \<phi>)"
| "wf_fml \<L> (And \<phi> \<psi>) = (wf_fml \<L> \<phi> \<and> wf_fml \<L> \<psi>)"
| "wf_fml \<L> (Exists z \<phi>) = (wf_fml \<L> \<phi>)"
| "wf_fml \<L> (Box \<alpha> \<psi>) = (wf_chp \<L> \<alpha> \<and> wf_fml \<L> \<psi>)"
| "wf_fml \<L> (AcBox \<alpha> A C \<psi>) = (wf_chp \<L> \<alpha> \<and> wf_fml \<L> A \<and> wf_fml \<L> C \<and> wf_fml \<L> \<psi> \<and> FVE\<^sub>\<L> \<L> (Efml A) \<inter> BVP\<^sub>\<L> \<L> \<alpha> \<subseteq> \<iota>\<^sub>T \<V>\<^sub>T )"
| "wf_fml \<L> (ChanIn \<theta> Y) = (wf_rtrm \<theta>)"

| "wf_chp \<L> (Chp a Z Y) = True"
| "wf_chp \<L> (x := \<theta>) = isQRpolynom \<theta>"
| "wf_chp \<L> (x := *) = True"
| "wf_chp \<L> (Test \<phi>) = isFOL\<^sub>R \<phi>"
| "wf_chp \<L> (Evolution x \<theta> \<phi>) = (isQRpolynom \<theta> \<and> isFOL\<^sub>R \<phi>)"
| "wf_chp \<L> (\<alpha> \<union>\<union> \<beta>) = (wf_chp \<L> \<alpha> \<and> wf_chp \<L> \<beta>)"
| "wf_chp \<L> (\<alpha> ;; \<beta>) = (wf_chp \<L> \<alpha> \<and> wf_chp \<L> \<beta>)"
| "wf_chp \<L> (Loop \<alpha>) = wf_chp \<L> \<alpha>"
| "wf_chp \<L> (Send ch h \<theta>) = isQRpolynom \<theta>"
| "wf_chp \<L> (Receive ch h x) = True"
| "wf_chp \<L> (Par \<alpha> \<beta>) = (wf_chp \<L> \<alpha> \<and> wf_chp \<L> \<beta> \<and> (BVP\<^sub>\<L> \<L> \<alpha> \<inter> BVP\<^sub>\<L> \<L> \<beta> \<subseteq> (\<iota>\<^sub>T \<V>\<^sub>T) \<union> \<V>\<^sub>\<mu>))"

lemma wf_Repeat: "wf_chp \<L> \<alpha> \<Longrightarrow> wf_chp \<L> (Repeat \<alpha> n)"
  by (induction n) (simp_all add: TT_def)

definition wf_inference :: "'a wf_stat_sem_scheme \<Rightarrow> inference \<Rightarrow> bool"
  where "wf_inference \<L> R = ((\<forall>k. k < length (fst R) \<longrightarrow> wf_fml \<L> ((fst R) ! k)) 
                                \<and> wf_fml \<L> (snd R))"



subsection \<open>Structural Induction\<close>

text \<open>The lemmas in this section provide induction principles for subsets of the syntax, which are
useful to prove properties that do not rely on the mutual inductive definition of the syntax.\<close>

text \<open>Induction principle for real terms\<close>
lemma rtrm_induct [case_names RVar RConst RFunc Number Plus Times ChanOf ValOf TimeOf LenT]:
  shows "(\<And>x. P (RVar x))
      \<Longrightarrow> (\<And>b c n. P (RConst b c n))
      \<Longrightarrow> (\<And>b f Z \<Theta>. P (RFunc b f Z \<Theta>))
      \<Longrightarrow> (\<And>r. P (Number r))
      \<Longrightarrow> (\<And>\<theta> \<eta>. P \<theta> \<Longrightarrow> P \<eta> \<Longrightarrow> P (Plus \<theta> \<eta>))
      \<Longrightarrow> (\<And>\<theta> \<eta>. P \<theta> \<Longrightarrow> P \<eta> \<Longrightarrow> P (Times \<theta> \<eta>))
      \<Longrightarrow> (\<And>te. P (ChanOf te))
      \<Longrightarrow> (\<And>te. P (ValOf te))
      \<Longrightarrow> (\<And>te. P (TimeOf te))
      \<Longrightarrow> (\<And>te. P (LenT te))
      \<Longrightarrow> P \<theta>" 
  by (induction \<theta>) (auto)

text \<open>Induction principle for trace terms\<close>
lemma ttrm_induct [case_names TVar TConst TFunc Empty ComItm Concat Proj Access]:
  shows "(\<And>h. P (TVar h))
    \<Longrightarrow> (\<And>c n. P (TConst c n))
    \<Longrightarrow> (\<And>f Z \<Theta>. P (TFunc f Z \<Theta>))
    \<Longrightarrow> (P Empty)
    \<Longrightarrow> (\<And>ch \<theta> \<eta>. P (ComItm ch \<theta> \<eta>))  
    \<Longrightarrow> (\<And>te\<^sub>1 te\<^sub>2. P te\<^sub>1 \<Longrightarrow> P te\<^sub>2 \<Longrightarrow> P (Concat te\<^sub>1 te\<^sub>2))
    \<Longrightarrow> (\<And>te Y. P te \<Longrightarrow> P (Proj te Y))
    \<Longrightarrow> (\<And>te \<theta>. P te \<Longrightarrow> P (Access te \<theta>))
    \<Longrightarrow> P te" 
  by (induction te) (auto)

fun args_to_rtrms :: "arg list \<Rightarrow> rtrm list"
  where
  "args_to_rtrms [] = []"
| "args_to_rtrms ((RArg \<theta>) # \<Theta>) = \<theta> # args_to_rtrms \<Theta>"
| "args_to_rtrms _ = undefined"

lemma RArg_inverse_to_rtrm: "list_all isQRarg \<Theta> \<Longrightarrow> \<Theta> = map RArg (args_to_rtrms \<Theta>)"
  apply (induction \<Theta>)
 apply simp
  using isQRarg.elims(2) by fastforce

lemma QRpolynom_induct0:
  assumes "\<And>x. P (RVar x)"
      and "\<And>c n. P (QRConst c n)"
      and "\<And>f \<Theta>. (\<And>\<theta>. \<theta> \<in> set \<Theta> \<Longrightarrow> Q (RArg \<theta>)) \<Longrightarrow> P (QRFunc f \<Theta>)"
      and "\<And>x. P (Number x)"
      and "\<And>\<theta> \<eta>. P \<theta> \<Longrightarrow> P \<eta> \<Longrightarrow> P (Plus \<theta> \<eta>)"
      and "\<And>\<theta> \<eta>. P \<theta> \<Longrightarrow> P \<eta> \<Longrightarrow> P (Times \<theta> \<eta>)"
      and "\<And>\<theta>. P \<theta> \<Longrightarrow> Q (RArg \<theta>)"
  shows "isQRpolynom \<theta> \<Longrightarrow> P \<theta>" 
    and "isQRarg e \<Longrightarrow> Q e"
using assms apply (induction \<theta> and e)
  unfolding QRConst_def   
    apply simp_all
  unfolding QRFunc_def by (metis RArg_inverse_to_rtrm in_set_conv_nth length_map list_all_length nth_map)

text \<open>Induction principle for pure real polynomials\<close>
lemma QRpolynom_induct [case_names IsQRPoly RVar QRConst QRFunc Number Plus Times]:
  shows "isQRpolynom \<theta>
    \<Longrightarrow> (\<And>x. P (RVar x))
    \<Longrightarrow> (\<And>c n. P (QRConst c n))
    \<Longrightarrow> (\<And>f \<Theta>. (\<And>\<theta>. \<theta> \<in> set \<Theta> \<Longrightarrow> P \<theta>) \<Longrightarrow> P (QRFunc f \<Theta>))
    \<Longrightarrow> (\<And>x. P (Number x)) 
    \<Longrightarrow> (\<And>\<theta> \<eta>. P \<theta> \<Longrightarrow> P \<eta> \<Longrightarrow> P (Plus \<theta> \<eta>))
    \<Longrightarrow> (\<And>\<theta> \<eta>. P \<theta> \<Longrightarrow> P \<eta> \<Longrightarrow> P (Times \<theta> \<eta>))
    \<Longrightarrow> P \<theta>" 
  apply (rule QRpolynom_induct0 [where Q="\<lambda>\<theta>. P (rarg \<theta>)"])
  by auto

text \<open>Induction principle for programs\<close>
lemma chp_induct [case_names Chp Assign Nondet Test Evolution Choice Compose Loop Send Receive Par]:
   "(\<And>a Z Y. P (Chp a Z Y)) 
    \<Longrightarrow> (\<And>x \<theta>. P (x := \<theta>))
    \<Longrightarrow> (\<And>x. P (x := *))
    \<Longrightarrow> (\<And>\<phi>. P (? \<phi>))
    \<Longrightarrow> (\<And>x \<theta> \<phi>. P (Evolution x \<theta> \<phi>))
    \<Longrightarrow> (\<And>\<alpha> \<beta>. P \<alpha> \<Longrightarrow> P \<beta> \<Longrightarrow> P (\<alpha> \<union>\<union> \<beta>))
    \<Longrightarrow> (\<And>\<alpha> \<beta>. P \<alpha> \<Longrightarrow> P \<beta> \<Longrightarrow> P (\<alpha> ;; \<beta>))
    \<Longrightarrow> (\<And>\<alpha>. P \<alpha> \<Longrightarrow> P (\<alpha>**))
    \<Longrightarrow> (\<And>ch h \<theta>. P (Send ch h \<theta>))
    \<Longrightarrow> (\<And>ch h x. P (Receive ch h x))
    \<Longrightarrow> (\<And>\<alpha> \<beta>. P \<alpha> \<Longrightarrow> P \<beta> \<Longrightarrow> P (\<alpha> par \<beta>))
    \<Longrightarrow> P \<alpha>"
  by (induction rule: chp.induct) (auto)

text \<open>Induction principle for formulas\<close>
lemma fml_induct [case_names GPsymb Geq Pref Not And Exists Box AcBox ChanIn]:
  "(\<And>b p Z \<Theta>. P (GPsymb b p Z \<Theta>))
  \<Longrightarrow> (\<And>\<theta> \<eta>. P (Geq \<theta> \<eta>))
  \<Longrightarrow> (\<And>\<theta> \<eta>. P (Pref \<theta> \<eta>))
  \<Longrightarrow> (\<And>\<phi>. P \<phi> \<Longrightarrow> P (Not \<phi>))
  \<Longrightarrow> (\<And>\<phi> \<psi>. P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (And \<phi> \<psi>))
  \<Longrightarrow> (\<And>z \<phi>. P \<phi> \<Longrightarrow> P (Exists z \<phi>))
  \<Longrightarrow> (\<And>\<alpha> \<phi>. P \<phi> \<Longrightarrow> P (Box \<alpha> \<phi>))
  \<Longrightarrow> (\<And>\<alpha> A C \<phi>. P C \<Longrightarrow> P \<phi> \<Longrightarrow> P (AcBox \<alpha> A C \<phi>))
  \<Longrightarrow> (\<And>ch Y. P (ChanIn ch Y))
  \<Longrightarrow> P \<phi>"
  by (induction rule: fml.induct) auto

lemma QRargs_contain_QRpolynoms: 
  "list_all isQRarg (map RArg \<Theta>) \<Longrightarrow> (\<And>\<theta>. \<theta> \<in> set \<Theta> \<Longrightarrow> isQRpolynom \<theta>)"
  by (metis in_set_conv_nth isQRarg.simps(1) length_map list_all_length nth_map)

text \<open>Induction principle for first-order real arithmetic\<close>
lemma FOL\<^sub>R_induct [case_names IsFOL\<^sub>R QRGPsymb Geq Not And Exists]:
  shows "isFOL\<^sub>R \<phi>
  \<Longrightarrow> (\<And>p \<Theta>. (\<And>\<theta>. \<theta> \<in> set \<Theta> \<Longrightarrow> isQRpolynom \<theta>) \<Longrightarrow> P (QRGPsymb p \<Theta>))
  \<Longrightarrow> (\<And>\<theta> \<eta>. isQRpolynom \<theta> \<Longrightarrow> isQRpolynom \<eta> \<Longrightarrow> P (Geq \<theta> \<eta>))                     
  \<Longrightarrow> (\<And>\<phi>. P \<phi> \<Longrightarrow> P (Not \<phi>))
  \<Longrightarrow> (\<And>\<phi> \<psi>. P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (And \<phi> \<psi>))
  \<Longrightarrow> (\<And>z \<phi>. P \<phi> \<Longrightarrow> P (Exists (Rv z) \<phi>))
  \<Longrightarrow> P \<phi>"
  apply (induction rule: fml_induct)
         apply simp_all
  unfolding QRGPsymb_def apply (metis QRargs_contain_QRpolynoms RArg_inverse_to_rtrm)
  by (metis isFOL\<^sub>R.simps(5,7) variable.exhaust)

text \<open>Pure real polynomials and first-order real arithmetic are themselves well-formed\<close>

lemma QRpolynom_is_wf_rtrm: 
  shows "isQRpolynom \<theta> \<Longrightarrow> wf_rtrm \<theta>"
    and "isQRarg e \<Longrightarrow> wf_arg e"
  apply (induction \<theta> and e)
  apply (simp_all add: QRConst_def)
  using list.pred_mono_strong by blast

lemma FOL\<^sub>R_is_wf_fml:
  assumes "isFOL\<^sub>R \<phi>"
  shows "wf_fml \<L> \<phi>"
  apply (induction \<phi> rule: FOL\<^sub>R_induct)
  using assms by (simp_all add: QRGPsymb_def QRpolynom_is_wf_rtrm list_all_length)



subsection \<open>Finiteness of the Syntactic Categories\<close>

lemma ident_finite: "finite allidents" by auto

lemma allrvars_cases: "\<V>\<^sub>R = alluvars \<union> alldvars" using rvar.exhaust by blast 

lemma uvar_finite: "finite alluvars"
  using finite_imageI[OF ident_finite, where h=\<open>\<lambda>x. RVarName x\<close>] by (simp add: full_SetCompr_eq) 

lemma dvar_finite: "finite alldvars"
  using finite_imageI[OF ident_finite, where h=\<open>\<lambda>x. DVarName x\<close>] by (simp add: full_SetCompr_eq) 

lemma rvar_finite [simp]: "finite \<V>\<^sub>R"
  by (metis allrvars_cases dvar_finite finite_Un uvar_finite)

lemma tvar_finite: "finite \<V>\<^sub>T"
  using finite_imageI[OF ident_finite, where h=\<open>\<lambda>h. TVarName h\<close>]
  by (metis ex_new_if_finite rangeI tvar.exhaust)

lemma allvars_finite: "finite \<V>"
proof -
  have "finite {Rv x| x. x \<in> \<V>\<^sub>R}" 
    using finite_imageI[OF rvar_finite, where h=\<open>\<lambda>x. Rv x\<close>] by (simp add: full_SetCompr_eq) 
  moreover have "finite {Tv h| h. h \<in> \<V>\<^sub>T}" 
    using finite_imageI[OF tvar_finite, where h=\<open>\<lambda>h. Tv h\<close>] by (simp add: full_SetCompr_eq) 
  ultimately have "finite ({Rv x | x. x \<in> \<V>\<^sub>R} \<union> {Tv h | h. h \<in> \<V>\<^sub>T})" using finite_Un by blast
  thus "finite allvars" using compose_allvars unfolding iota_rvars_def iota_tvars_def by argo
qed

lemma chan_finite: "finite allchans"
  using finite_imageI[OF ident_finite, where h=\<open>\<lambda>ch. ChanName ch\<close>]
  by (metis ex_new_if_finite rangeI chan.exhaust)




subsection \<open>Bindables\<close>


text \<open>Variables and channel names can be both bound. To treat this fact uniformly they are 
summarized as bindables.
In particular, variables can be bound by quantifiers and programs, and channel names can be bound by
the communication statements in programs.\<close>

definition allcomtar:: "comtar set"
  where "allcomtar \<equiv> UNIV"


fun flatten_comtar :: "comtar set \<Rightarrow> chan set"
  where "flatten_comtar Y = { ch. \<exists>h. (h, ch) \<in> Y }"

lemma pi_empty [simp]: shows "\<pi>\<^sub>V {} = {}" and "\<pi>\<^sub>C {} = {}" 
  by (simp_all add: pi_vars_def pi_comtar_def)

lemma pi_univ: shows "\<pi>\<^sub>C UNIV = allcomtar" and "\<pi>\<^sub>V UNIV = allvars"
  by (simp_all add: pi_comtar_def pi_vars_def allcomtar_def)

lemma pi_insert [simp, intro]: 
  shows "\<pi>\<^sub>V (insert (Bv z) U) = {z} \<union> \<pi>\<^sub>V U" and "\<pi>\<^sub>C (insert (Bc h ch) U) = {(h, ch)} \<union> \<pi>\<^sub>C U"
  by (auto simp add: pi_vars_def pi_comtar_def)

lemma pi_insert_other [simp]: 
  shows "\<pi>\<^sub>V (insert (Bc h ch) S) = \<pi>\<^sub>V S" and "\<pi>\<^sub>C (insert (Bv z) S) = \<pi>\<^sub>C S"
  by (simp_all add: pi_vars_def pi_comtar_def)

lemma iota_variable_singleton [simp]: "\<iota>\<^sub>V {z} = {Bv z}" by (simp add: iota_vars_def)
lemma iota_comtar_singleton [simp]: "\<iota>\<^sub>C {(h, ch)} = {Bc h ch}" using iota_comtar_def by auto

lemma iota_vars_image: "\<iota>\<^sub>V X = (\<lambda>z. Bv z) ` X"
  by (simp add: iota_vars_def image_def) (force)
lemma iota_comtar_image: "\<iota>\<^sub>C Y = (\<lambda>(h, ch). Bc h ch) ` Y" 
  by (simp add: iota_comtar_def image_def) (force)

lemma in_iota [simp, intro]: shows "Bv z \<in> \<iota>\<^sub>V X = (z \<in> X)" and "Bc h ch \<in> \<iota>\<^sub>C W = ((h, ch) \<in> W)"
  by (simp_all add: iota_vars_def iota_comtar_def)

lemma not_in_iota [simp, intro]: shows "Bc h ch \<notin> \<iota>\<^sub>V X" and "Bv z \<notin> \<iota>\<^sub>C W" 
  by (simp_all add: iota_vars_def iota_comtar_def)

abbreviation nobindrs :: "bindr set" where "nobindrs \<equiv> {}"
abbreviation allbindrs :: "bindr set" where "allbindrs \<equiv> \<iota>\<^sub>V \<V> \<union> \<iota>\<^sub>C allcomtar"

lemma \<pi>\<^sub>V_compl [simp]: "\<pi>\<^sub>V (-U) = -\<pi>\<^sub>V U" by (auto simp add: pi_vars_def)
lemma \<pi>\<^sub>C_compl [simp]: "\<pi>\<^sub>C (-U) = -\<pi>\<^sub>C U" by (auto simp add: pi_comtar_def)
lemma \<pi>\<^sub>V_dist_intersect [simp]: "\<pi>\<^sub>V (V \<inter> W) = \<pi>\<^sub>V V \<inter> \<pi>\<^sub>V W" by (auto simp add: pi_vars_def)
lemma \<pi>\<^sub>C_dist_intersect [simp]: "\<pi>\<^sub>C (V \<inter> W) = \<pi>\<^sub>C V \<inter> \<pi>\<^sub>C W" by (auto simp add: pi_comtar_def)
lemma \<pi>\<^sub>V_dist_union [simp]: "\<pi>\<^sub>V (V \<union> W) = \<pi>\<^sub>V V \<union> \<pi>\<^sub>V W" by (auto simp add: pi_vars_def)
lemma \<pi>\<^sub>C_dist_union [simp]: "\<pi>\<^sub>C (V \<union> W) = \<pi>\<^sub>C V \<union> \<pi>\<^sub>C W" by (auto simp add: pi_comtar_def)
lemma \<pi>\<^sub>V_inverse [simp]: "\<pi>\<^sub>V (\<iota>\<^sub>V V) = V" using pi_vars_def iota_vars_def by auto
lemma \<pi>\<^sub>C_inverse [simp]: "\<pi>\<^sub>C (\<iota>\<^sub>C W) = W" using pi_comtar_def iota_comtar_def by auto
lemma \<pi>\<^sub>V_anychans [simp]: "\<pi>\<^sub>V (\<iota>\<^sub>C X) = {}" using pi_vars_def iota_comtar_def by auto
lemma \<pi>\<^sub>C_anyvars [simp]: "\<pi>\<^sub>C (\<iota>\<^sub>V X) = {}" using pi_comtar_def iota_vars_def by auto

lemma iota_vars_dist_union [simp]: "\<iota>\<^sub>V (V \<union> W) = \<iota>\<^sub>V V \<union> \<iota>\<^sub>V W" by (auto simp add: iota_vars_def)
lemma iota_comtar_dist_union [simp]: "\<iota>\<^sub>C (V \<union> W) = \<iota>\<^sub>C V \<union> \<iota>\<^sub>C W" by (auto simp add: iota_comtar_def)

lemma \<pi>\<^sub>V_anychans_compl [simp]: "\<pi>\<^sub>V (-\<iota>\<^sub>C W) = \<V>" by auto 
lemma \<pi>\<^sub>C_anyvars_compl [simp]: "\<pi>\<^sub>C (-\<iota>\<^sub>V X) = (\<Union>h. {(h, ch) | ch. True})" by auto

lemma varbinders_compl [simp]: "-(\<iota>\<^sub>V \<V>) = \<iota>\<^sub>C allcomtar"
  by (auto simp add: iota_vars_def iota_comtar_def allcomtar_def) (meson bindr.exhaust)

lemma chanbinders_compl [simp]: "-(\<iota>\<^sub>C (\<Union>h. {(h, ch) | ch. True})) = \<iota>\<^sub>V \<V>"
  by (auto simp add: iota_vars_def iota_comtar_def) (meson bindr.exhaust)

lemma nobinders_compl [simp]: "-{} = allbindrs"
  using varbinders_compl by (auto simp add: iota_vars_def iota_comtar_def)

lemma pi_vars_Union [simp]: "\<pi>\<^sub>V (\<Union> X) = \<Union> (image \<pi>\<^sub>V X)"
  unfolding pi_vars_def by auto

lemma iota_vars_Union [simp]: "\<iota>\<^sub>V (\<Union> X) = \<Union> (image \<iota>\<^sub>V X)"
  unfolding iota_vars_def by auto

lemma iota_comtar_Union [simp]: "\<iota>\<^sub>C (\<Union> X) = \<Union> (image \<iota>\<^sub>C X)"
  unfolding iota_comtar_def by auto

lemma pi_rvars_dist_union [simp]: "\<pi>\<^sub>R (X \<union> V) = \<pi>\<^sub>R X \<union> \<pi>\<^sub>R V" by (auto simp add: pi_rvars_def)
lemma pi_rvars_dist_inter [simp]: "\<pi>\<^sub>R (X \<inter> V) = \<pi>\<^sub>R X \<inter> \<pi>\<^sub>R V" by (auto simp add: pi_rvars_def)
lemma pi_tvars_dist_union [simp]: "\<pi>\<^sub>T (X \<union> V) = \<pi>\<^sub>T X \<union> \<pi>\<^sub>T V" by (auto simp add: pi_tvars_def)
lemma pi_tvars_dist_inter [simp]: "\<pi>\<^sub>T (X \<inter> V) = \<pi>\<^sub>T X \<inter> \<pi>\<^sub>T V" by (auto simp add: pi_tvars_def)

lemma allcomtar_singleton_image [simp]: "allcomtar `` {h} = \<Omega>" unfolding allcomtar_def by blast
lemma image_insert_not_in: "h \<noteq> z \<Longrightarrow> insert (h, ch) S `` {z} = S `` {z}" by auto

lemma rvar_in_var_compl: "- \<iota>\<^sub>V (\<iota>\<^sub>R \<V>\<^sub>R) = \<iota>\<^sub>V (\<iota>\<^sub>T \<V>\<^sub>T) \<union> \<iota>\<^sub>C allcomtar"
  apply (auto simp add: iota_vars_def iota_comtar_def iota_rvars_def iota_tvars_def allcomtar_def)
  by (meson bindr.exhaust variable.exhaust)

lemma iota_pi_rvars_inv [simp]: "X \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R \<Longrightarrow> \<iota>\<^sub>R (\<pi>\<^sub>R X) = X"
  by (auto simp add: iota_rvars_def pi_rvars_def)

lemma iota_pi_vars_inv [simp]: "X \<subseteq> \<iota>\<^sub>V \<V> \<Longrightarrow> \<iota>\<^sub>V (\<pi>\<^sub>V X) = X"
  by (auto simp add: iota_vars_def pi_vars_def)


lemma only_vars_intersect: "X \<inter> \<iota>\<^sub>V \<V> = \<iota>\<^sub>V (\<pi>\<^sub>V X)" unfolding iota_vars_def pi_vars_def by blast

lemma iota_pi_vars_alternate: "\<iota>\<^sub>V X \<subseteq> Z = (X \<subseteq> \<pi>\<^sub>V Z)" by (auto simp add: iota_vars_def pi_vars_def)
lemma iota_pi_comtar_alternate: "\<iota>\<^sub>C X \<subseteq> Z = (X \<subseteq> \<pi>\<^sub>C Z)" by (auto simp add: iota_comtar_def pi_comtar_def)

lemma pi_vars_injective: "\<exists>Z. X = \<pi>\<^sub>V Z" by (auto simp add: pi_vars_def)

lemma tvars_rvars_disjoint_union: "X \<inter> \<iota>\<^sub>T \<V>\<^sub>T \<union> X \<inter> \<iota>\<^sub>R \<V>\<^sub>R = X" using rvars_compl by fast

lemma rvars_vars: "X \<subseteq> \<iota>\<^sub>V (\<iota>\<^sub>R \<V>\<^sub>R) \<Longrightarrow> \<pi>\<^sub>V X \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R" 
  by (auto simp add: iota_vars_def pi_vars_def)

lemma bindable_partition: "X = \<iota>\<^sub>V (\<pi>\<^sub>V X) \<union> \<iota>\<^sub>C (\<pi>\<^sub>C X)"
  unfolding iota_vars_def pi_vars_def iota_comtar_def pi_comtar_def
  apply auto
  by (metis bindr.exhaust)

lemma finite_rvars: "finite (X::rvar set)"
  using finite_subset rvar_finite subset_UNIV by blast
lemma finite_tvars: "finite (X::tvar set)"
  using finite_subset tvar_finite subset_UNIV by blast
lemma finite_variables: "finite (X::variable set)"
  using allvars_finite finite_subset top_greatest by blast
lemma finite_comtar: "finite (X::comtar set)"
  by (meson chan_finite finite_Prod_UNIV finite_tvars rev_finite_subset subset_UNIV)
lemma finite_chans: "finite (X::chan set)"
  using finite_subset chan_finite subset_UNIV by blast
lemma finite_partition: "finite (\<iota>\<^sub>V (\<pi>\<^sub>V X) \<union> \<iota>\<^sub>C (\<pi>\<^sub>C X))"
  by (simp add: finite_comtar finite_variables iota_comtar_image iota_vars_image)  
lemma finite_bindables: "finite (X::bindr set)"
  using bindable_partition finite_partition by metis
  
end