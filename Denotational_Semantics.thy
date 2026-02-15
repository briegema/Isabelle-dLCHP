theory "Denotational_Semantics" 
  imports
  Ordinary_Differential_Equations.ODE_Analysis
  "HOL-Analysis.Derivative"
  "Syntax"     
  "Domain"
  "Lib"       
  "HOL.String"
begin

section \<open>Denotational Semantics\<close>

text \<open>This section defines the denotational semantics of the Dynamic logic of Communicating Hybrid 
Programs.
  \<open>https://link.springer.com/chapter/10.1007/978-3-031-38499-8_6\<close>\<close>

(* Landau symbols in ODE_Analysis are in conflict with state access \<omega>(z) *)
no_notation smallomega_at_top (\<open>(\<open>indent=2 notation=\<open>mixfix smallomega\<close>\<close>\<omega>'(_'))\<close>)

subsection \<open>Traces\<close>

record comevent =
  along :: chan
  val :: real
  stamp :: real

record recevent =
  comevent +
  recvar :: tvar

definition mkevent :: "chan \<Rightarrow> real \<Rightarrow> real \<Rightarrow> comevent"
  where "mkevent ch d s = \<lparr> along = ch, val = d, stamp = s \<rparr>"

definition mkrecevent :: "tvar \<Rightarrow> chan \<Rightarrow> real \<Rightarrow> real \<Rightarrow> recevent"
  where "mkrecevent h ch d s = \<lparr> along = ch, val = d, stamp = s, recvar = h \<rparr>"

text \<open>The type trace_scheme enables polymorphic definitions for either type of trace based on the 
polymorphism of records.\<close>
type_synonym 'a trace_scheme = "('a comevent_scheme) list"
type_synonym trace = "comevent list"
type_synonym rectrace = "recevent list"

text \<open>The projection tfilter can be used on traces and rec_traces due to polymorphism of 
trace_scheme. It returns the subtrace obtained by removing all events whose channel name is not in Y.\<close>
definition tfilter :: "'a trace_scheme \<Rightarrow> chan set \<Rightarrow> 'a trace_scheme" (infixr "\<down>" 75) 
  where "tfilter \<tau> Y = filter (\<lambda>\<rho>. along \<rho> \<in> Y) \<tau>"

text \<open>The subtrace obtained by removing all events whose recorder-channel pair is not in Y.\<close>
definition rec_tfilter :: "rectrace \<Rightarrow> comtar set \<Rightarrow> rectrace" (infixr "\<Down>" 75) 
  where "rec_tfilter \<tau> Y = filter (\<lambda>\<rho>. (recvar \<rho>, along \<rho>) \<in> Y) \<tau>"

definition eflat :: "recevent \<Rightarrow> comevent"
  where "eflat \<rho> = mkevent (along \<rho>) (val \<rho>) (stamp \<rho>)"

definition tflat :: "rectrace \<Rightarrow> trace"
  where "tflat \<tau> = map eflat \<tau>"

definition addrece :: "comevent \<Rightarrow> tvar \<Rightarrow> recevent"
  where "addrece \<rho> h = mkrecevent h (along \<rho>) (val \<rho>) (stamp \<rho>)"

definition addrec :: "trace \<Rightarrow> tvar \<Rightarrow> rectrace"
  where "addrec \<tau> h = map (\<lambda>\<rho>. addrece \<rho> h) \<tau>"

text \<open>The subtrace recorded by trace variable h.\<close>
definition byrec :: "rectrace \<Rightarrow> tvar \<Rightarrow> trace" where
  "byrec \<tau> h = tflat (filter (\<lambda>\<rho>. recvar \<rho> = h) \<tau>)"

text \<open>All channel names of a trace.\<close>
fun tchans :: "'a trace_scheme \<Rightarrow> chan set" where
  "tchans [] = {}"
| "tchans (\<rho> # \<tau>) = {along \<rho>} \<union> tchans \<tau>"

text \<open>All recorders of a trace.\<close>
fun trecs :: "rectrace \<Rightarrow> tvar set" where
  "trecs [] = {}"
| "trecs (\<rho> # \<tau>) = {recvar \<rho>} \<union> trecs \<tau>"



paragraph \<open>Properties of Event Construction\<close>

lemma along_mkrecevent [simp, intro]: "along (mkrecevent h ch d s) = ch" by (simp add: mkrecevent_def)
lemma val_mkrecevent [simp, intro]: "val (mkrecevent h ch d s) = d" by (simp add: mkrecevent_def)
lemma stamp_mkrecevent [simp, intro]: "stamp (mkrecevent h ch d s) = s" by (simp add: mkrecevent_def)
lemma recvar_mkrecevent [simp, intro]: "recvar (mkrecevent h ch d s) = h" by (simp add: mkrecevent_def)

lemma along_mkevent [simp, intro]: "along (mkevent ch d s) = ch" by (simp add: mkevent_def)
lemma val_mkevent [simp, intro]: "val (mkevent ch d s) = d" by (simp add: mkevent_def)
lemma stamp_mkevent [simp, intro]: "stamp (mkevent ch d s) = s" by (simp add: mkevent_def)

lemma mkevent_recvar_update [simp]: "mkrecevent h\<^sub>0 ch d s \<lparr>recvar := h\<rparr> = mkrecevent h ch d s"
  by (simp add: mkevent_def)



paragraph \<open>Properties of Flattening Traces and Adding Recorders\<close>

lemma along_eflat [simp]: "along (eflat \<rho>) = along \<rho>" by (simp add: eflat_def)
lemma val_eflat [simp]: "val (eflat \<rho>) = val \<rho>" by (simp add: eflat_def)
lemma stamp_eflat [simp]: "stamp (eflat \<rho>) = stamp \<rho>" by (simp add: eflat_def)

lemma eflat_mkrecevent [simp]: "eflat (mkrecevent h ch d s) = mkevent ch d s" 
  by (simp add: eflat_def)
lemma eflat_addrec [simp]: "eflat (addrece \<rho> h) = \<rho>" by (simp add: addrece_def)

lemma tflat_empty [simp]: "tflat [] = []" by (simp add: tflat_def)
lemma tflat_dist_cons [simp, intro]: "tflat (\<rho> # \<tau>) = eflat \<rho> # tflat \<tau>" by (simp add: tflat_def)
lemma tflat_dist_app [simp, intro]: "tflat (\<tau>\<^sub>1 @ \<tau>\<^sub>2) = tflat \<tau>\<^sub>1 @ tflat \<tau>\<^sub>2" by (simp add: tflat_def)

lemma addrec_empty [simp]: "addrec [] h = []" by (simp add: addrec_def)
lemma addrec_dist_cons [simp, intro]: "addrec (\<rho> # \<tau>) h = addrece \<rho> h # addrec \<tau> h" 
  by (simp add: addrec_def)
lemma addrec_dist_app [simp, intro]: "addrec (\<tau>\<^sub>1 @ \<tau>\<^sub>2) h = addrec \<tau>\<^sub>1 h @ addrec \<tau>\<^sub>2 h" 
  by (simp add: addrec_def)

lemma addrec_empty_conv [simp]: "addrec \<tau> h = [] \<Longrightarrow> \<tau> = []" by (simp add: addrec_def)

lemma addrec_tfilter_commute [simp]: "addrec (\<tau> \<down> Y) h = (addrec \<tau> h) \<down> Y"
  apply (induction \<tau>)
  by (simp_all add: addrec_def tfilter_def addrece_def)

lemma recvar_addrece [simp]: "recvar (addrece \<rho> h) = h" by (simp add: addrece_def)

lemma byrec_addrec [simp]: "byrec (addrec \<tau> h) h = \<tau>"
  apply (induction \<tau>)
  by (simp_all add: byrec_def)

lemma tflat_inv_addrec: "tflat (addrec \<tau> h) = \<tau>" 
  by (induction \<tau>) (simp_all)

lemma length_tflat [simp]: "length (tflat \<tau>) = length \<tau>" by (simp add: tflat_def)



paragraph \<open>Properties of Filtering Traces by Channels\<close>

lemma tfilter_empty [simp]: "[] \<down> C = []" by (simp add: tfilter_def)
lemma rec_tfilter_empty [simp]: "[] \<Down> C = []" by (simp add: rec_tfilter_def)

lemma tfilter_allchans [simp]: "\<tau> \<down> \<Omega> = \<tau>" by (simp add: tfilter_def)
lemma rec_tfilter_allchans [simp]: "\<tau> \<Down> (\<V>\<^sub>T \<times> \<Omega>) = \<tau>" by (simp add: rec_tfilter_def)

lemma tfilter_nochans [simp]: "\<tau> \<down> {} = []" by (simp add: tfilter_def)
lemma rec_tfilter_nocomtars [simp]: "\<tau> \<Down> {} = []" by (simp add: rec_tfilter_def)

lemma tfilter_emptyI: "(\<And>ch. ch \<in> C \<Longrightarrow> (\<tau>::('a trace_scheme)) \<down> {ch} = []) \<Longrightarrow> \<tau> \<down> C = []"
  apply (induction \<tau>)
   apply simp
  apply (simp add: tfilter_def) by (metis list.simps(3))

lemma rec_tfilter_emptyI: "(\<And>h ch. (h, ch) \<in> C \<Longrightarrow> \<tau> \<Down> {(h,ch)} = []) \<Longrightarrow> \<tau> \<Down> C = []"
  apply (induction \<tau>)
   apply simp
  apply (simp add: rec_tfilter_def)
  by (metis (lifting) list.simps(3))

(* directly entails (\<tau> \<down> C) \<down> Y = \<tau> \<down> (C \<inter> Y) *)
lemma tfilter_trans: "\<tau>' = \<tau> \<down> C \<Longrightarrow> \<tau>'' = \<tau>' \<down> Y \<Longrightarrow> \<tau>'' = \<tau> \<down> (C \<inter> Y)"
  apply (induction \<tau>)
  unfolding tfilter_def by auto

lemma rec_tfilter_trans: "\<tau>' = \<tau> \<Down> C \<Longrightarrow> \<tau>'' = \<tau>' \<Down> Y \<Longrightarrow> \<tau>'' = \<tau> \<Down> (C \<inter> Y)"
  apply (induction \<tau>)
  unfolding rec_tfilter_def by auto

lemma tfilter_dist_inter [simp]: "(\<tau> \<down> C) \<down> Y = \<tau> \<down> (C \<inter> Y)" by (simp add: tfilter_trans)
lemma rec_tfilter_dist_inter [simp]: "(\<tau> \<Down> C) \<Down> Y = \<tau> \<Down> (C \<inter> Y)" by (simp add: rec_tfilter_trans)

lemma tfilter_dist_cons: "(\<rho> # \<tau>) \<down> Y = (if along \<rho> \<in> Y then [\<rho>] else []) @ \<tau> \<down> Y" 
  by (simp add: tfilter_def)
lemma tfilter_dist_app [simp]: "(\<tau>\<^sub>1 @ \<tau>\<^sub>2) \<down> Y = \<tau>\<^sub>1 \<down> Y @ \<tau>\<^sub>2 \<down> Y"  by (simp add: tfilter_def)

lemma rec_tfilter_dist_cons: "(\<rho> # \<tau>) \<Down> Y = (if (recvar \<rho>, along \<rho>) \<in> Y then \<rho> # (\<tau> \<Down> Y) else \<tau> \<Down> Y)"
  by (simp add: rec_tfilter_def)

lemma tfilter_hd_in [simp]: "along \<rho> \<in> C \<Longrightarrow> (\<rho> # \<tau>) \<down> C = \<rho> # \<tau> \<down> C" by (simp add: tfilter_def)
lemma tfilter_hd_not_in [simp]: "along \<rho> \<notin> C \<Longrightarrow> (\<rho> # \<tau>) \<down> C = \<tau> \<down> C" by (simp add: tfilter_def)

lemma tfilter_empty_hd_conv: "(\<rho> # \<tau>) \<down> C = [] \<Longrightarrow> along \<rho> \<notin> C" using tfilter_def by auto
lemma tfilter_empty_tl_conv: "(\<rho> # \<tau>) \<down> Y = [] \<Longrightarrow> \<tau> \<down> Y = []"  
  using tfilter_hd_not_in tfilter_empty_hd_conv by metis             

lemma tfilter_empty_antimon: "C \<subseteq> Y \<Longrightarrow> \<tau> \<down> Y = [] \<Longrightarrow> \<tau> \<down> C = []"
  by (induction \<tau>) (auto simp add: tfilter_dist_cons)

lemma tfilter_cong_antimon: "\<rho> \<down> Y = \<tau> \<down> Y \<Longrightarrow> C \<subseteq> Y \<Longrightarrow> \<rho> \<down> C = \<tau> \<down> C" 
  by (metis Int_absorb1 tfilter_dist_inter)

lemma rec_tfilter_cong_antimon: "\<rho> \<Down> Y = \<tau> \<Down> Y \<Longrightarrow> C \<subseteq> Y \<Longrightarrow> \<rho> \<Down> C = \<tau> \<Down> C" 
  by (metis Int_absorb1 rec_tfilter_dist_inter)

lemma junkfree_prefix_junkfree: "\<tau>' \<preceq> \<tau> \<Longrightarrow> \<tau> \<down> C = \<tau> \<Longrightarrow> \<tau>' \<down> C = \<tau>'"
  apply (induction \<tau>' arbitrary: \<tau>)
   apply simp
  apply (simp add: prefix_def tfilter_def)
  by (metis filter.simps(2) filter_eq_Cons_iff list.sel(3))

lemma events_tfilter_union [simp]: "set (\<tau> \<down> (C \<union> D)) = set (\<tau> \<down> C) \<union> set (\<tau> \<down> D)"
  unfolding tfilter_def by auto

lemma tfilter_idem_tchans_overapprox: "\<tau> \<down> Y = \<tau> \<Longrightarrow> tchans \<tau> \<subseteq> Y" 
  apply (induction \<tau>) 
   apply simp_all        
  by (metis  Cons_eq_filterD filter.simps(2) list.sel(3) tfilter_def)

lemma in_tchans_proj_non_empty_step: 
  "(ch \<in> tchans \<tau> \<Longrightarrow> \<tau> \<down> {ch} \<noteq> []) \<Longrightarrow> ch \<in> tchans (\<rho> # \<tau>) \<Longrightarrow> (\<rho> # \<tau>) \<down> {ch} \<noteq> []"
  apply (cases "along \<rho> = ch")
   apply (meson singletonI tfilter_empty_hd_conv)
  by (metis insert_iff insert_is_Un tchans.simps(2) tfilter_empty_tl_conv)

lemma in_tchans_proj_non_empty: "ch \<in> tchans \<tau> \<Longrightarrow> \<tau> \<down> {ch} \<noteq> []"
  apply (induction \<tau>)
   apply simp
  using in_tchans_proj_non_empty_step by blast

lemma non_emty_proj_in_tchans: "\<tau> \<down> {ch} \<noteq> [] \<Longrightarrow> ch \<in> tchans \<tau>"
  apply (induction \<tau>)
   apply simp
  by (metis Un_iff tfilter_hd_not_in singletonD tchans.simps(2))

(* lemma trecs_proj_step: "trecs (\<tau> \<down> Y) \<subseteq> trecs \<tau> \<Longrightarrow> trecs ((\<rho> # \<tau>) \<down> Y) \<subseteq> trecs (\<rho> # \<tau>)"
  apply (cases "along \<rho> \<in> Y"; rule)
   apply (metis Un_iff tfilter_hd_in in_mono trecs.simps(2))
  by (metis Un_iff tfilter_hd_not_in in_mono trecs.simps(2))

lemma trecs_proj: "trecs (\<tau> \<down> Y) \<subseteq> trecs \<tau>"
  apply (induction \<tau>) apply auto[1]
  using trecs_proj_step by blast *)

lemma obspref_proj_cong: "(\<tau>', \<omega>') \<sqsubseteq> (\<tau>, \<omega>) \<Longrightarrow> obspref (\<tau>' \<down> C, \<omega>') (\<tau> \<down> C, \<omega>)"
  using obspref_alt tfilter_dist_app prefix_def by metis



paragraph \<open>Properties of Filtering Traces by Recorders\<close>

lemma byrec_empty [simp]: "byrec [] h = []" by (simp add: byrec_def) 
lemma byrec_dist_cons: "byrec (\<rho> # \<tau>) h = (if recvar \<rho> = h then eflat \<rho> # byrec \<tau> h else byrec \<tau> h)"
  by (simp add: byrec_def)
lemma byrec_dist_app [simp]: "byrec (\<tau>\<^sub>1 @ \<tau>\<^sub>2) h = byrec \<tau>\<^sub>1 h @ byrec \<tau>\<^sub>2 h" by (simp add: byrec_def) 

lemma byrec_hd_in [simp]: "recvar \<rho> = h \<Longrightarrow> byrec (\<rho> # \<tau>) h = eflat \<rho> # byrec \<tau> h" 
  by (simp add: byrec_def)
lemma byrec_hd_not_in [simp]: "recvar \<rho> \<noteq> h \<Longrightarrow> byrec (\<rho> # \<tau>) h = byrec \<tau> h" by (simp add: byrec_def)

lemma byrec_tfilter_commute: "byrec \<tau> h \<down> Y = byrec (\<tau> \<down> Y) h" 
  apply (induction \<tau>)
  by (simp_all add: byrec_def tfilter_def)

lemma tchans_byrec_overapprox: "tchans (byrec \<tau> h) \<subseteq> tchans \<tau>"
  by (induction \<tau>) (auto simp add: byrec_def tflat_def)

lemma byrec_rec_tfilter_commute: "byrec (rec_tfilter \<tau> Y) h = tfilter (byrec \<tau> h) (Y `` {h})"
  apply (induction \<tau>)
  by (simp_all add: rec_tfilter_dist_cons byrec_dist_cons tflat_def)
  
lemma byrec_mkevent_success [simp]: "byrec [mkrecevent h ch d s] h = [mkevent ch d s]"
  by (simp add: byrec_def)

lemma filter_in_empty_byrec_empty: "byrec \<tau> h = [] \<Longrightarrow> byrec (\<tau> \<down> Y) h = []"
  by (metis byrec_tfilter_commute tfilter_empty)

lemma byrec_in_empty_filter_empty: "\<tau> \<down> Y = [] \<Longrightarrow> (byrec \<tau> h) \<down> Y = []"
  by (metis byrec_tfilter_commute byrec_empty)

lemma tfilter_cong_byrec_antimon: "C \<subseteq> Y \<Longrightarrow> \<rho> \<down> Y = \<tau> \<down> Y \<Longrightarrow> byrec \<rho> h \<down> C = byrec \<tau> h \<down> C"
  using byrec_tfilter_commute tfilter_cong_antimon by metis

lemma trecs_byrec: "(trecs \<tau> \<subseteq> {h}) \<Longrightarrow> (byrec \<tau> h = tflat \<tau>)"
  by (induction \<tau>) (auto)

lemma trecs_equiv_byrec: "h \<in> trecs \<tau>  = (byrec \<tau> h \<noteq> [])"
  apply (induction \<tau>)
  using byrec_def by auto

lemma trecs_byrec_trans: "byrec \<tau> h \<noteq> [] \<Longrightarrow> trecs \<tau> \<subseteq> X \<Longrightarrow> {h} \<subseteq> X"
  using trecs_equiv_byrec by blast

lemma length_byrec_bound: "length (byrec \<tau> h) \<le> length \<tau>"
  apply (induction \<tau>)
  by (simp_all add: byrec_dist_cons)

lemma recvar_hd_byrec_eq_tflat: "byrec (\<rho> # \<tau>) h = tflat (\<rho> # \<tau>) \<Longrightarrow> recvar \<rho> = h"
proof (rule ccontr)
  assume "recvar \<rho> \<noteq> h"
  moreover assume "byrec (\<rho> # \<tau>) h = tflat (\<rho> # \<tau>)"
  ultimately have "length (byrec \<tau> h) = length \<tau> + 1" by simp
  thus False using length_byrec_bound by (metis Suc_eq_plus1 Suc_n_not_le_n)
qed

(* urec = unique recorder *)
lemma urec_byrec_other: "h0 \<noteq> h \<Longrightarrow> byrec \<tau> h = tflat \<tau> \<Longrightarrow> byrec \<tau> h0 = []"
proof (induction \<tau>)
  case Nil
  then show ?case by simp
next
  case (Cons \<rho> \<tau>)
  hence "recvar \<rho> = h" using Cons.prems(2) recvar_hd_byrec_eq_tflat by blast
  thus ?case using Cons.IH Cons.prems(1,2) by auto
qed

lemma addrece_eflat [simp, intro]: "recvar \<rho> = h \<Longrightarrow> addrece (eflat \<rho>) h = \<rho>"
  by (simp add: addrece_def)

(* urec = unique recorder *)
lemma addrec_inv_tflat_urec: "byrec \<tau> h = tflat \<tau> \<Longrightarrow> addrec (tflat \<tau>) h = \<tau>"
  apply (induction \<tau>)               
   apply (simp_all add: byrec_dist_cons)
  by (metis addrece_eflat byrec_hd_not_in list.simps(1) recvar_hd_byrec_eq_tflat tflat_dist_cons)

lemma byrec_eq_tflat_urec: "byrec \<tau> h = tflat \<tau> \<Longrightarrow> trecs \<tau> \<subseteq> {h}"
  by (metis urec_byrec_other insert_iff subsetI trecs_equiv_byrec)

lemma addrec_urec_tflat: "byrec \<tau> h = tflat \<tau> \<Longrightarrow> addrec (tflat \<tau>) h = \<tau>"
  by (simp add: byrec_eq_tflat_urec addrec_inv_tflat_urec)



paragraph \<open>Misc\<close>

lemma tflat_mono_prefix: "\<tau>' \<preceq> \<tau> \<Longrightarrow> tflat \<tau>' \<preceq> tflat \<tau>"
  by (simp add: tflat_def map_mono_prefix)

lemma byrec_mono_prefix: "\<tau>' \<preceq> \<tau> \<Longrightarrow> byrec \<tau>' h \<preceq> byrec \<tau> h"
  by (simp add: byrec_def filter_mono_prefix tflat_mono_prefix)

lemma tfilter_mono_prefix: "\<tau>' \<preceq> \<tau> \<Longrightarrow> \<tau>' \<down> C \<preceq> \<tau> \<down> C"
  by (simp add: tfilter_def filter_mono_prefix)

lemma rec_tfilter_empty_byrecI: "(\<And>h. byrec \<tau> h \<down> Y `` {h} = []) \<Longrightarrow> \<tau> \<Down> Y = []"
  by (metis UNIV_I byrec_hd_in byrec_rec_tfilter_commute tchans.cases tfilter_allchans tfilter_empty_hd_conv)



subsection \<open>States\<close>

text \<open>States for each base sort\<close>
type_synonym rstate = "rvar \<Rightarrow> real"
type_synonym tstate = "tvar \<Rightarrow> trace"

text \<open>General states as sum of the states for the base sorts\<close>
record state =
  stR :: rstate
  stT :: tstate

text \<open>States with adjoint NonFin to represent unfinished computation\<close>
type_synonym statebot = "state reachedstate"

(* lifts a state transformation to a transformation on states with bot *)
fun botify :: "(state \<Rightarrow> state) \<Rightarrow> statebot \<Rightarrow> statebot" where
  "botify f NonFin = NonFin"
| "botify f (Fin \<omega>) = Fin (f \<omega>)"

type_synonym solution = "real \<Rightarrow> state"



paragraph \<open>Values as the Sum of Reals, Traces, and Booleans\<close>

datatype vals = Rp (rval: real) | Tp (tval: trace) (* term values *)
datatype evals = Rs real | Ts trace | Bs bool (* expression values *)

fun to_evals :: "vals \<Rightarrow> evals" where
  "to_evals (Rp r) = Rs r"
| "to_evals (Tp \<tau>) = Ts \<tau>"

text \<open>Point-wise access to states\<close>
fun byvar :: "state \<Rightarrow> variable \<Rightarrow> vals" (infixl "$$" 70) where
  "byvar \<nu> (Rv z) = Rp (stR \<nu> z)" |
  "byvar \<nu> (Tv z) = Tp (stT \<nu> z)"

definition sorteq :: "variable \<Rightarrow> vals \<Rightarrow> bool" 
  where "sorteq z d \<longleftrightarrow> isRv z \<and> (\<exists>d'. d = Rp d') \<or> isTv z \<and> (\<exists>d'. d = Tp d')"

lemma rsorteq [simp, intro]: "sorteq (Rv x) (Rp d)" by (simp add: sorteq_def)
lemma tsorteq [simp, intro]: "sorteq (Tv x) (Tp d)" by (simp add: sorteq_def)

lemma sorteq_self_val [simp]: "sorteq z (\<omega> $$ z)"
  apply (cases z)
  by (auto simp add: sorteq_def)



paragraph \<open>Intro Rules for State Equality\<close>

lemma state_eq_by_sortI: "stR \<nu> = stR \<omega> \<Longrightarrow> stT \<nu> = stT \<omega> \<Longrightarrow> (\<nu>::state) = \<omega>" by simp

lemma allRv_eq_stR: "(\<forall>x. \<nu> $$ (Rv x) = \<omega> $$ (Rv x)) = (stR \<nu> = stR \<omega>)" by auto
lemma allTv_eq_stT: "(\<forall>x. \<nu> $$ (Tv x) = \<omega> $$ (Tv x)) = (stT \<nu> = stT \<omega>)" by auto

lemma state_eqI: "(\<And>z. \<nu> $$ z = \<omega> $$ z) \<Longrightarrow> \<nu> = \<omega>" 
  apply (rule state_eq_by_sortI)
  using allRv_eq_stR allTv_eq_stT by blast+

lemma state_eq: "(\<forall>z. \<nu> $$ z = \<omega> $$ z) = (\<nu> = \<omega>)" using state_eqI by auto

lemma rstate_eqI: "(\<And>x::rvar. \<nu> x = \<omega> x ) \<Longrightarrow> \<nu> = \<omega>" by presburger
lemma tstate_eqI: "(\<And>h::tvar. \<nu> h = \<omega> h ) \<Longrightarrow> \<nu> = \<omega>" by presburger

lemma stR_cong_stT: "\<nu>\<lparr>stT := \<kappa>\<rparr> = \<omega>\<lparr>stT := \<o>\<rparr> \<Longrightarrow> stR \<nu> = stR \<omega>" 
  by (metis state.simps(1,5) state.surjective)
lemma stT_cong_stR: "\<nu>\<lparr>stR := \<kappa>\<rparr> = \<omega>\<lparr>stR := \<o>\<rparr> \<Longrightarrow> stT \<nu> = stT \<omega>"
  by (metis state.simps(2,4) state.surjective)



paragraph \<open>State Update\<close>

definition rrepv :: "state \<Rightarrow> rvar \<Rightarrow> real \<Rightarrow> state"
  where "rrepv \<nu> x d = \<nu> \<lparr> stR := (fun_upd (stR \<nu>) x d) \<rparr>"

definition trepv :: "state \<Rightarrow> tvar \<Rightarrow> trace \<Rightarrow> state"
  where "trepv \<nu> h d = \<nu> \<lparr> stT := (fun_upd (stT \<nu>) h d) \<rparr>"

definition trepv_sol :: "solution \<Rightarrow> tvar \<Rightarrow> trace \<Rightarrow> solution"
  where "trepv_sol F h d = (\<lambda>\<zeta>. trepv (F(\<zeta>)) h d)"

abbreviation rrepvbot :: "statebot \<Rightarrow> rvar \<Rightarrow> real \<Rightarrow> statebot"
  where "rrepvbot \<nu> x d \<equiv> botify (\<lambda>\<nu>. rrepv \<nu> x d) \<nu>"

abbreviation trepvbot :: "statebot \<Rightarrow> tvar \<Rightarrow> trace \<Rightarrow> statebot"
  where "trepvbot \<nu> h \<tau> \<equiv> botify (\<lambda>\<nu>. trepv \<nu> h \<tau>) \<nu>"

fun upds :: "state \<Rightarrow> variable \<Rightarrow> vals \<Rightarrow> state" where
  "upds \<nu> (Rv x) (Rp d) = rrepv \<nu> x d"
| "upds \<nu> (Tv h) (Tp d) = trepv \<nu> h d"
| "upds _ _ _ = undefined"

abbreviation updsbot :: "statebot \<Rightarrow> variable \<Rightarrow> vals \<Rightarrow> statebot"
  where "updsbot \<nu> z d \<equiv> botify (\<lambda>\<nu>. upds \<nu> z d) \<nu>"

lemma updsbot_real [simp]: "updsbot \<nu> (Rv x) (Rp d) = rrepvbot \<nu> x d" by (cases \<nu>) (simp_all)
lemma updsbot_trace [simp]: "updsbot \<nu> (Tv h) (Tp d) = trepvbot \<nu> h d" by (cases \<nu>) (simp_all)

lemma rrepv_def_correct: "rrepv \<nu> x d = \<nu> \<lparr> stR := (\<lambda>y. if x = y then d else ((stR \<nu>) y)) \<rparr>"
  unfolding rrepv_def using fun_upd_def by metis

(* Helps proving if access is to any variable type, e.g. Vagree *)
lemma rrepv_access [simp]: "(rrepv \<omega> x d) $$ z = (if (Rv x = z) then (Rp d) else \<omega> $$ z)"
  by (cases z) (simp_all add: rrepv_def_correct)

(* Helps proving if access is to specific real var, e.g. assigneq_axiom *)
lemma rrepv_stR_access [simp]: "stR (rrepv \<omega> x d) y = (if x = y then d else stR \<omega> y)"
  by (simp_all add: rrepv_def_correct)

lemma rrepv_self [simp]: "rrepv \<omega> x (stR \<omega> x) = \<omega>"
  by (simp add: rrepv_def)

lemma trepv_def_correct: "trepv \<nu> h d = \<nu> \<lparr> stT := (\<lambda>y. if h = y then d else ((stT \<nu>) y)) \<rparr>"
  unfolding trepv_def using fun_upd_def  by metis

lemma trepv_access [simp]: "(trepv \<omega> h d) $$ z = (if (Tv h = z) then (Tp d) else \<omega> $$ z)"
  by (cases z) (simp_all add: trepv_def_correct)

lemma trepv_stT_access [simp]: "stT (trepv \<omega> h0 d) h = (if h0 = h then d else stT \<omega> h)"
  by (simp_all add: trepv_def_correct)

lemma trepv_self [simp]: "trepv \<omega> h (stT \<omega> h) = \<omega>"
  by (simp add: trepv_def)

lemma stR_trepv [simp]: "stR (trepv \<omega> h \<tau>) = stR \<omega>" by (simp_all add: trepv_def_correct)
lemma stT_rrepv [simp]: "stT (rrepv \<omega> x d) = stT \<omega>" by (simp_all add: rrepv_def_correct)

lemma upds_access [simp]: "sorteq z d \<Longrightarrow> (upds \<omega> z d) $$ y = (if y = z then d else \<omega> $$ y)"
  unfolding sorteq_def by fastforce

lemma stR_upds_other [simp]: "sorteq z d \<Longrightarrow> z \<noteq> (Rv x) \<Longrightarrow> stR (upds \<nu> z d) x = stR \<nu> x"
  using sorteq_def by fastforce

lemma stT_upds_other [simp]: "sorteq z d \<Longrightarrow> z \<noteq> (Tv h) \<Longrightarrow> stT (upds \<nu> z d) h = stT \<nu> h"
  using sorteq_def by fastforce

lemma upds_self [simp]: "sorteq z d \<Longrightarrow> (upds \<omega> z (\<omega> $$ z)) = \<omega>"
  unfolding sorteq_def by fastforce

lemma rrepv_trepv_commute: "rrepv (trepv \<nu> h \<tau>) x d = trepv (rrepv \<nu> x d) h \<tau>"
  by (simp add: rrepv_def trepv_def)

lemma upds_commute_on_disjoint_vars: "x \<noteq> y \<Longrightarrow> sorteq x d\<^sub>1 \<Longrightarrow> sorteq y d\<^sub>2 
    \<Longrightarrow> upds (upds \<nu> x d\<^sub>1) y d\<^sub>2 = upds (upds \<nu> y d\<^sub>2) x d\<^sub>1"
  using state_eqI upds_access by presburger

lemma rrepv_idem [simp]: "rrepv (rrepv \<nu> x d) x d' = rrepv \<nu> x d'" by (simp add: rrepv_def)
lemma trepv_idem [simp]: "trepv (trepv \<nu> h \<tau>) h \<tau>' = trepv \<nu> h \<tau>'" by (simp add: trepv_def)
lemma upds_idem [simp]: "sorteq z d \<Longrightarrow> sorteq z d' \<Longrightarrow> upds (upds \<nu> z d) z d' = upds \<nu> z d'"
  apply (cases z) using sorteq_def by force+



paragraph \<open>State-trace Operations\<close>

definition sttconc :: "state \<Rightarrow> rectrace \<Rightarrow> state" (infixr "@@" 75)
  where "\<nu> @@ \<tau> = \<nu> \<lparr> stT := \<lambda>h. (stT \<nu>) h @ (byrec \<tau> h) \<rparr>"

lemma sttconc_empty [simp]: "\<nu> @@ [] = \<nu>" using sttconc_def by simp

lemma sttconc_dist_app: "\<nu> @@ (\<tau>\<^sub>1 @ \<tau>\<^sub>2) = (\<nu> @@ \<tau>\<^sub>1) @@ \<tau>\<^sub>2" using sttconc_def by simp

lemma stR_sttconc [simp]: "stR (\<nu> @@ \<tau>) = stR \<nu>" by (simp add: sttconc_def)

lemma stT_sttconc_dist: "stT (\<nu> @@ \<tau>) = (\<lambda>h. stT \<nu> h @ byrec \<tau> h)"
  by (simp add: sttconc_def)

lemma stT_sttconc_dist_access: "stT (\<nu> @@ \<tau>) h = (stT \<nu> h) @ (byrec \<tau> h)"
  by (simp add: sttconc_def)

lemma sttconc_dist_cons: "\<nu> @@ (\<rho> # \<tau>) = (\<nu> @@ [\<rho>]) @@ \<tau>"
  by (metis append.left_neutral append_Cons sttconc_dist_app)

(* argument order allows to obtain "state \<Rightarrow> state" function *)
definition stt_rmsuffix :: "rectrace \<Rightarrow> (state \<Rightarrow> state)" 
  where "stt_rmsuffix \<tau> \<nu> = \<nu> \<lparr> stT := \<lambda>h. rmsuffix ((stT \<nu>) h) (byrec \<tau> h) \<rparr>" 

definition is_stt_suffix :: "state \<Rightarrow> rectrace \<Rightarrow> bool"
  where "is_stt_suffix \<nu> \<tau> \<longleftrightarrow> (\<forall>h. \<exists>\<tau>\<^sub>h. (stT \<nu>) h = \<tau>\<^sub>h @ (byrec \<tau> h))"

lemma stT_stt_rmsuffix_correct: "stT (stt_rmsuffix \<tau> (\<nu> @@ \<tau>)) = stT \<nu>"
  by (auto simp add: stt_rmsuffix_def sttconc_def rmsuffix_correct)

lemma stt_rmsuffix_correct_rev: "is_stt_suffix \<nu> \<tau> \<Longrightarrow> sttconc (stt_rmsuffix \<tau> \<nu>) \<tau> = \<nu>"
  apply (rule state_eq_by_sortI) 
   apply (simp add: stt_rmsuffix_def sttconc_def)+
  by (metis (no_types, lifting) ext is_stt_suffix_def rmsuffix_correct)

lemma stR_stt_rmsuffix: "stR \<nu> = stR \<omega> \<Longrightarrow> stR (stt_rmsuffix \<tau> \<nu>) = stR \<nu>"
  by (simp add: stt_rmsuffix_def)

lemma stT_sttconc_addrec: "stT \<nu> h @ byrec (addrec \<tau> h\<^sub>0) h = stT (trepv \<nu> h\<^sub>0 (stT \<nu> h\<^sub>0 @ \<tau>)) h"
  apply (cases "h = h\<^sub>0")
   apply simp_all
  by (metis byrec_addrec urec_byrec_other tflat_inv_addrec)

lemma sttconc_addrec: "\<nu> @@ (addrec \<tau> h) = trepv \<nu> h ((stT \<nu>) h @ \<tau>)"
  apply (rule state_eq_by_sortI)
  by (auto simp add: sttconc_def stT_sttconc_addrec)


lemma stT_sttconc_neq_iff_byrec: "stT (\<nu> @@ \<tau>) h \<noteq> stT \<nu> h = (byrec \<tau> h \<noteq> [])"
  by (simp add: sttconc_def)



paragraph \<open>Filtering States\<close>

definition tsfilter :: "tstate \<Rightarrow> comtar set \<Rightarrow> tstate"
  where "tsfilter \<nu> W \<equiv> (\<lambda>h. \<nu> h \<down> (W `` {h}))"

definition sfilter :: "state \<Rightarrow> comtar set \<Rightarrow> state"
  where "sfilter \<nu> W = \<nu> \<lparr> stT := tsfilter (stT \<nu>) W \<rparr>"
                                      
lemma stT_sfilterI: 
  "(\<And>h. tsfilter (stT \<nu>) W h = tsfilter (stT \<omega>) W h) \<Longrightarrow> stT (sfilter \<nu> W) = stT (sfilter \<omega> W)"
  by (simp add: sfilter_def tsfilter_def)

lemma stR_sfilter [simp]: "stR (sfilter \<nu> W) = stR \<nu>" by (simp add: sfilter_def)
lemma stT_sfilter [simp]: "stT (sfilter \<nu> W) = tsfilter (stT \<nu>) W" by (simp add: sfilter_def)

lemma tsfilter_all [simp]: "tsfilter \<nu> allcomtar = \<nu>" by (simp add: tsfilter_def)
lemma sfilter_all [simp]: "sfilter \<nu> allcomtar = \<nu>" by (simp add: sfilter_def)

(* not a simp rule to enable lemmas about tsfilter *)
lemma tsfilter_access: "tsfilter \<nu> W h = (\<nu> h) \<down> (W `` {h})"
  by (simp add: sfilter_def tsfilter_def)

lemma tsfilter_insert_access_other: "h \<noteq> z \<Longrightarrow> tsfilter \<nu> (insert (h, ch) W) z = tsfilter \<nu> W z"
  by (simp add: tsfilter_def image_insert_not_in)

lemma tsfilter_singleton [simp]: "tsfilter \<nu> ({(h, ch)}) h = \<nu> h \<down> {ch}"
  by (simp add: tsfilter_def Image_def)

lemma tsfilter_trans [trans]: "\<nu>' = tsfilter (tsfilter \<nu> W) U \<Longrightarrow> \<nu>' = tsfilter \<nu> (W \<inter> U)"
  by (simp add: tsfilter_def singleton_image_inter Collect_conj_eq)

lemma sfilter_trans [trans]: "\<nu>' = sfilter (sfilter \<nu> W) U \<Longrightarrow> \<nu>' = sfilter \<nu> (W \<inter> U)"
  by (simp add: tsfilter_trans)

lemma tsfilter_antimon: "W \<subseteq> U \<Longrightarrow> tsfilter \<nu> U h = tsfilter \<omega> U h 
    \<Longrightarrow> tsfilter \<nu> W h = tsfilter \<omega> W h"
  unfolding tsfilter_def                       
  by (metis inf.absorb_iff2 tsfilter_def tsfilter_trans)
                                              
lemma sfilter_antimon: "W \<subseteq> U \<Longrightarrow> sfilter \<nu> U = sfilter \<omega> U \<Longrightarrow> sfilter \<nu> W = sfilter \<omega> W"
  apply (rule state_eq_by_sortI)
   apply (simp add: sfilter_def) using stR_cong_stT apply force
    by (rule stT_sfilterI) (metis stT_sfilter tsfilter_antimon)

lemma sfilter_eq_stT_E: "sfilter \<nu> Y = sfilter \<omega> Y \<Longrightarrow> stT \<nu> h \<down> Y `` {h} = stT \<omega> h \<down> Y `` {h}"
  by (metis stT_sfilter tsfilter_access)

lemma sfilter_eq_stR_E: "sfilter \<nu> X = sfilter \<omega> X \<Longrightarrow> stR \<nu> = stR \<omega>"
  by (metis stR_sfilter)

lemma sfilter_dist_sttconc_byvar: "(sfilter (\<nu> @@ \<tau>) W) $$ z = (sfilter \<nu> W @@ rec_tfilter \<tau> W) $$ z"
  apply (cases z)                                                                   
   apply simp
  by (simp add: tsfilter_def byrec_rec_tfilter_commute stT_sttconc_dist_access)
 
lemma sfilter_dist_sttconc: "sfilter (\<nu> @@ \<tau>) W = (sfilter \<nu> W) @@ (rec_tfilter \<tau> W)"
  apply (rule state_eqI)
  using sfilter_dist_sttconc_byvar by simp

lemma tsfilter_eq_singleton_compl_access_other:
  "tsfilter \<nu> (-{(h, ch)}) = tsfilter \<omega> (-{(h, ch)}) \<Longrightarrow> z \<in> -{h} \<Longrightarrow> \<nu> z = \<omega> z"
  unfolding tsfilter_def apply simp
  by (metis (no_types, opaque_lifting) singleton_compl_image_other tfilter_allchans)



paragraph \<open>Merging States\<close>

text \<open>Left-merge the states \<nu> and \<omega> according to the variable set X\<close>
definition lmerge :: "state \<Rightarrow> state \<Rightarrow> variable set \<Rightarrow> state"
  where "lmerge \<nu> \<omega> X = \<lparr> stR = \<lambda>x. if x \<in> \<pi>\<^sub>R X then stR \<nu> x else stR \<omega> x,
                          stT = \<lambda>x. if x \<in> \<pi>\<^sub>T X then stT \<nu> x else stT \<omega> x \<rparr>"

lemma lmerge_access [simp]: "(lmerge \<nu> \<omega> X) $$ z = (if z \<in> X then \<nu> $$ z else \<omega> $$ z)"
  apply (cases z)
  by (simp_all add: lmerge_def)

fun lmergebot :: "statebot \<Rightarrow> statebot \<Rightarrow> variable set \<Rightarrow> statebot"
  where
  "lmergebot (Fin \<omega>\<^sub>1) (Fin \<omega>\<^sub>2) X = Fin (lmerge \<omega>\<^sub>1 \<omega>\<^sub>2 X)"
| "lmergebot _ _ X = NonFin"

lemma lmergebot_fin: "(Fin \<omega> = lmergebot (Fin \<omega>\<^sub>\<alpha>) (Fin \<omega>\<^sub>\<beta>) X) = (\<omega> = lmerge \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> X)" by simp

lemma lmergebot_Exists_Fin: "(Fin \<omega>) = lmergebot \<omega>\<^sub>1 \<omega>\<^sub>2 X \<Longrightarrow> \<exists>\<omega>\<^sub>1' \<omega>\<^sub>2'. \<omega>\<^sub>1 = Fin \<omega>\<^sub>1' \<and> \<omega>\<^sub>2 = Fin \<omega>\<^sub>2'"
  by (metis lmergebot.elims)

lemma lmergebot_NonFin [simp]: "NonFin = lmergebot \<omega>\<^sub>1 \<omega>\<^sub>2 X = (\<omega>\<^sub>1 = NonFin \<or> \<omega>\<^sub>2 = NonFin)"
  by (metis lmergebot.elims reachedstate.discI)

definition to_state :: "(variable \<Rightarrow> vals) \<Rightarrow> state"
  where "to_state \<nu> = \<lparr> stR = (\<lambda>x. case \<nu> (Rv x) of Rp d \<Rightarrow> d | Tp \<tau> \<Rightarrow> 0), 
                        stT = (\<lambda>h. case \<nu> (Tv h) of Rp d \<Rightarrow> [] | Tp \<tau> \<Rightarrow> \<tau>) \<rparr>"

definition lmergea :: "state \<Rightarrow> state \<Rightarrow> bindr set \<Rightarrow> state"
  where "lmergea \<nu> \<omega> Z = \<lparr> stR = \<lambda>x. if x \<in> \<pi>\<^sub>R (\<pi>\<^sub>V Z) then stR (sfilter \<nu> (\<pi>\<^sub>C Z)) x else stR (sfilter \<omega> (-\<pi>\<^sub>C Z)) x,
                          stT = \<lambda>x. if x \<in> \<pi>\<^sub>T (\<pi>\<^sub>V Z) then stT (sfilter \<nu> (\<pi>\<^sub>C Z)) x else stT (sfilter \<omega> (-\<pi>\<^sub>C Z)) x \<rparr>"


fun state_join :: "statebot \<Rightarrow> state \<Rightarrow> state" (infixr "\<squnion>" 60)
  where
  "state_join (Fin \<omega>) \<nu> = \<omega>"
| "state_join NonFin \<nu> = \<nu>"



subsection \<open>Agreement and Variation of States\<close>

definition eqon :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "eqon \<nu> \<omega> X \<equiv> (\<forall>z. z\<in>X \<longrightarrow> \<nu>(z) = \<omega>(z))"

definition Vagree :: "state \<Rightarrow> state \<Rightarrow> variable set \<Rightarrow> bool"
  where "Vagree \<nu> \<omega> V \<equiv> (\<forall>z. z\<in>V \<longrightarrow> \<nu> $$ z = \<omega> $$ z)"

definition VCagree :: "state \<Rightarrow> state \<Rightarrow> bindr set \<Rightarrow> bool"
  where "VCagree \<nu> \<omega> U \<equiv> Vagree (sfilter \<nu> (\<pi>\<^sub>C U)) (sfilter \<omega> (\<pi>\<^sub>C U)) (\<pi>\<^sub>V U)"

definition Uvariation :: "state \<Rightarrow> state \<Rightarrow> bindr set \<Rightarrow> bool"
  where "Uvariation \<nu> \<nu>' U \<equiv> VCagree \<nu> \<nu>' (-U)"

lemma VagreeI: "(\<And>z. z \<in> X \<Longrightarrow> \<nu> $$ z = \<omega> $$ z) \<Longrightarrow> Vagree \<nu> \<omega> X" 
  by (simp add: Vagree_def)

lemma byvar_by_sortI: "eqon (stR \<nu>) (stR \<omega>) (\<pi>\<^sub>R X) \<Longrightarrow> eqon (stT \<nu>) (stT \<omega>) (\<pi>\<^sub>T X) \<Longrightarrow> z \<in> X \<Longrightarrow> \<nu> $$ z = \<omega> $$ z"
  by (cases z) (simp_all add: eqon_def)

lemma Vagree_by_sortI: "eqon (stR \<nu>) (stR \<omega>) (\<pi>\<^sub>R X) \<Longrightarrow> eqon (stT \<nu>) (stT \<omega>) (\<pi>\<^sub>T X) \<Longrightarrow> Vagree \<nu> \<omega> X"
  by (simp add: Vagree_def byvar_by_sortI)

lemma Vagree_stR_E: "Vagree \<nu> \<omega> X \<Longrightarrow> eqon (stR \<nu>) (stR \<omega>) (\<pi>\<^sub>R X)"
  by (auto simp add: Vagree_def eqon_def)

lemma Vagree_stT_E: "Vagree \<nu> \<omega> X \<Longrightarrow> eqon (stT \<nu>) (stT \<omega>) (\<pi>\<^sub>T X)"
  by (auto simp add: Vagree_def eqon_def)

lemma Vagree_eqon: "Vagree \<nu> \<omega> X = (eqon (stR \<nu>) (stR \<omega>) (\<pi>\<^sub>R X) \<and> eqon (stT \<nu>) (stT \<omega>) (\<pi>\<^sub>T X))"
  apply rule
  using Vagree_stR_E Vagree_stT_E apply simp
  by (rule Vagree_by_sortI) (simp_all)

lemma VCagree_stR_E: "VCagree \<nu> \<omega> U \<Longrightarrow> eqon (stR \<nu>) (stR \<omega>) (\<pi>\<^sub>R (\<pi>\<^sub>V U))" 
  unfolding VCagree_def by (drule Vagree_stR_E) (simp)

lemma VCagree_stT_E: "VCagree \<nu> \<omega> U \<Longrightarrow> eqon (tsfilter (stT \<nu>) (\<pi>\<^sub>C U)) (tsfilter (stT \<omega>) (\<pi>\<^sub>C U)) (\<pi>\<^sub>T (\<pi>\<^sub>V U))"
  unfolding VCagree_def by (drule Vagree_stT_E) (simp)

lemma Uvariation_Vagree [simp]: "Uvariation \<nu> \<nu>' (\<iota>\<^sub>V (-V)) = Vagree \<nu> \<nu>' V"
  unfolding Uvariation_def VCagree_def Vagree_def using allcomtar_def sfilter_all by auto

lemma Uvariation_VCagree [simp]: "Uvariation \<nu> \<nu>' (-U) = VCagree \<nu> \<nu>' U"
  using Uvariation_def by force

lemma tsfilter_eqon_cong: "eqon (tsfilter \<nu> Y) (tsfilter \<omega> Y) X \<Longrightarrow> eqon (tsfilter \<nu> (Y \<inter> S)) (tsfilter \<omega> (Y \<inter> S)) X"
  using tsfilter_trans by (simp add: eqon_def tsfilter_access)
                                                 
lemma Vagree_sfilter_cong_inter: "Vagree (sfilter \<nu> Y) (sfilter \<omega> Y) X \<Longrightarrow> Vagree (sfilter \<nu> (Y \<inter> S)) (sfilter \<omega> (Y \<inter> S)) X"
  apply (rule Vagree_by_sortI)
  using Vagree_stR_E apply fastforce
  using Vagree_stT_E tsfilter_eqon_cong by fastforce

lemma Vagree_sfilter_cong: "Vagree \<nu> \<omega> X \<Longrightarrow> Vagree (sfilter \<nu> W) (sfilter \<omega> W) X"
  by (metis Vagree_sfilter_cong_inter sfilter_all sfilter_trans)



paragraph \<open>Agreement is an Equivalence Relation\<close>

lemma eqon_refl [simp, intro]: "eqon \<nu> \<nu> X" by (simp add: eqon_def)
lemma eqon_symb [sym]: "eqon \<nu> \<omega> X \<Longrightarrow> eqon \<omega> \<nu> X" by (simp add: eqon_def)
lemma eqon_trans [sym]: "eqon \<nu> \<kappa> X \<Longrightarrow> eqon \<kappa> \<omega> X \<Longrightarrow> eqon \<nu> \<omega> X" by (simp add: eqon_def)

lemma eqon_empty [simp]: "eqon \<nu> \<nu>' {}" by (simp add: eqon_def)

(* Vagree is an equivalence relation *)
lemma Vagree_refl [simp, intro]: "Vagree \<nu> \<nu> V" by (simp add: Vagree_def)
lemma Vagree_sym: "Vagree \<nu> \<nu>' V = Vagree \<nu>' \<nu> V" by (auto simp add: Vagree_def)
lemma Vagree_sym_rel [sym]: "Vagree \<nu> \<nu>' V \<Longrightarrow> Vagree \<nu>' \<nu> V" by (simp add: Vagree_sym)
lemma Vagree_trans [trans]: "Vagree \<nu> \<nu>' V \<Longrightarrow> Vagree \<nu>' \<nu>'' W \<Longrightarrow> Vagree \<nu> \<nu>'' (V\<inter>W)" 
  by (simp add: Vagree_def)

lemma Vagree_only_trans [trans]: "Vagree \<nu> \<nu>' V \<Longrightarrow> Vagree \<nu>' \<nu>'' V \<Longrightarrow> Vagree \<nu> \<nu>'' V"
  by (simp add: Vagree_def)

(* VCagree is an equivalence relation *)
lemma VCagree_refl [simp, intro]: "VCagree \<nu> \<nu> U" by (simp add: VCagree_def) 
lemma VCagree_sym: "VCagree \<nu> \<nu>' U = VCagree \<nu>' \<nu> U" by (simp add: VCagree_def Vagree_sym)
lemma VCagree_sym_rel [sym]: "VCagree \<nu> \<nu>' V \<Longrightarrow> VCagree \<nu>' \<nu> V"
  using VCagree_sym by simp
lemma VCagree_trans [trans]: "VCagree \<nu> \<nu>' U \<Longrightarrow> VCagree \<nu>' \<nu>'' U \<Longrightarrow> VCagree \<nu> \<nu>'' U" 
  by (simp add: VCagree_def Vagree_def) 



paragraph \<open>Set-Theoretic Properties of Agreement\<close>

lemma Vagree_empty [simp]: "Vagree \<nu> \<nu>' {}" by (simp add: Vagree_def)
lemma VCagree_empty [simp]: "VCagree \<nu> \<nu>' {}" by (simp add: VCagree_def)

lemma Vagree_univ [simp]: "Vagree \<nu> \<nu>' \<V> = (\<nu>=\<nu>')"  by (auto simp add: state_eqI Vagree_def)
lemma VCagree_univ [simp]: "VCagree \<nu> \<nu>' allbindrs = (\<nu>=\<nu>')" by (simp add: VCagree_def)

lemma Vagree_union [trans]: "Vagree \<nu> \<nu>' V \<Longrightarrow> Vagree \<nu> \<nu>' W \<Longrightarrow> Vagree \<nu> \<nu>' (V\<union>W)"
  by (simp add: Vagree_def)

lemma VCagree_union [trans]: "\<pi>\<^sub>C V = \<pi>\<^sub>C W \<Longrightarrow> VCagree \<nu> \<nu>' V \<Longrightarrow> VCagree \<nu> \<nu>' W \<Longrightarrow> VCagree \<nu> \<nu>' (V\<union>W)"
  by (simp add: VCagree_def Vagree_union)

lemma VCagree_union_rev: "VCagree \<nu> \<nu>' (V\<union>W) \<Longrightarrow> VCagree \<nu> \<nu>' V \<and> VCagree \<nu> \<nu>' W"
  apply (simp add: VCagree_def)
  by (metis Un_Int_eq(1,2) Vagree_def Vagree_sfilter_cong_inter unfold_simps(1))

lemma Vagree_antimon [simp]: "Vagree \<nu> \<nu>' V \<Longrightarrow> W \<subseteq> V \<Longrightarrow> Vagree \<nu> \<nu>' W"
  using Vagree_def by auto

lemma VCagree_inter: "VCagree \<nu> \<nu>' U \<Longrightarrow> VCagree \<nu> \<nu>' (W \<inter> U)"
  using Vagree_sfilter_cong_inter by (simp add: VCagree_def Vagree_def inf_commute)

lemma VCagree_or: "VCagree \<nu> \<nu>' W \<or> VCagree \<nu> \<nu>' U \<longrightarrow> VCagree \<nu> \<nu>' (W \<inter> U)"
  by (metis VCagree_inter inf.commute)

lemma VCagree_antimon [simp]: "VCagree \<nu> \<nu>' U \<Longrightarrow> W \<subseteq> U \<Longrightarrow> VCagree \<nu> \<nu>' W"
  using VCagree_inter inf.absorb_iff1 by metis
 
lemma Vagree_add: "\<nu> $$ z = \<nu>' $$ z \<Longrightarrow> Vagree \<nu> \<nu>' X \<Longrightarrow> Vagree \<nu> \<nu>' (X \<union> {z})"
  by (simp add: Vagree_def)

lemma VCagree_add_var: "\<nu> $$ z = \<nu>' $$ z \<Longrightarrow> VCagree \<nu> \<nu>' U \<Longrightarrow> VCagree \<nu> \<nu>' (U \<union> (\<iota>\<^sub>V {z}))"
  unfolding VCagree_def apply simp
  by (metis Un_commute Vagree_add Vagree_empty Vagree_sfilter_cong Vagree_union insert_is_Un)
  
lemma Vagree_and [simp]: "Vagree \<nu> \<nu>' V \<and> Vagree \<nu> \<nu>' W \<longleftrightarrow> Vagree \<nu> \<nu>' (V\<union>W)"
  by (auto simp add: Vagree_def)

lemma Vagree_or: "Vagree \<nu> \<nu>' V \<or> Vagree \<nu> \<nu>' W \<longrightarrow> Vagree \<nu> \<nu>' (V\<inter>W)"
  by (auto simp add: Vagree_def)

lemma Vagree_allrvars: "Vagree \<nu> \<omega> (\<iota>\<^sub>R \<V>\<^sub>R) = (stR \<nu> = stR \<omega>)"
  unfolding Vagree_def iota_rvars_def by fastforce

lemma Vagree_alltvars: "Vagree \<nu> \<omega> (\<iota>\<^sub>T \<V>\<^sub>T) = (stT \<nu> = stT \<omega>)"
  unfolding Vagree_def iota_tvars_def by fastforce


lemma Vagree_T_onlyE: "Vagree \<nu> \<omega> (\<iota>\<^sub>T X) \<Longrightarrow> eqon (stT \<nu>) (stT \<omega>) X" 
  using Vagree_stT_E unfolding iota_tvars_def pi_tvars_def by fastforce
                                    
lemma Vagree_sfilter_singleton_compl: "Vagree (sfilter \<nu> (-{(h, ch)})) \<nu> (\<iota>\<^sub>T (-{h}))" 
  apply (rule Vagree_by_sortI)
  by (simp_all add: eqon_def tsfilter_def singleton_compl_image_other iota_tvars_def)



lemma Vagree_eq: "Vagree \<nu> \<omega> V \<Longrightarrow> V = W \<Longrightarrow> Vagree \<nu> \<omega> W" by blast

lemma Vagree_trans_antimon [trans]: "Vagree \<nu> \<nu>' V \<Longrightarrow> Vagree \<nu>' \<nu>'' W \<Longrightarrow> X\<subseteq>V\<inter>W \<Longrightarrow> Vagree \<nu> \<nu>'' X"
  using Vagree_trans Vagree_antimon by blast

lemma Vagree_trans_eq [trans]: "Vagree \<nu> \<nu>' V \<Longrightarrow> Vagree \<nu>' \<nu>'' W \<Longrightarrow> X = V\<inter>W \<Longrightarrow> Vagree \<nu> \<nu>'' X"
  using Vagree_trans by simp

lemma Vagree_union_antimon: "Vagree \<nu> \<nu>' V \<Longrightarrow> Vagree \<nu> \<nu>' W \<Longrightarrow> X \<subseteq> V\<union>W \<Longrightarrow> Vagree \<nu> \<nu>' X"
  using Vagree_union Vagree_antimon by blast



paragraph \<open>Agreement and operations on state\<close>

lemma Vagree_rrepv: "Vagree \<omega> (rrepv \<omega> x d) (-{Rv x})"
  apply (rule Vagree_by_sortI)
  by (auto simp add: eqon_def rrepv_def)

lemma Vagree_trepv: "Vagree \<omega> (trepv \<omega> x d) (-{Tv x})"
  apply (rule Vagree_by_sortI)
  by (auto simp add: eqon_def trepv_def)

lemma Vagree_upds: "sorteq z d \<Longrightarrow> Vagree \<omega> (upds \<omega> z d) (-{z})"
  apply (cases z)
  apply (metis Vagree_rrepv upds.simps(1) sorteq_def variable.distinct(1))
  by (metis Vagree_trepv upds.simps(2) sorteq_def variable.distinct(1))

lemma VCagree_repv: "VCagree \<omega> (rrepv \<omega> x d) (-\<iota>\<^sub>V {Rv x})"
  using VCagree_def Vagree_sfilter_cong Vagree_rrepv \<pi>\<^sub>V_compl \<pi>\<^sub>V_inverse by presburger

lemma VCagree_trepv: "VCagree \<omega> (trepv \<omega> h \<tau>) (-\<iota>\<^sub>V {Tv h})"
  using VCagree_def Vagree_sfilter_cong Vagree_trepv \<pi>\<^sub>V_compl \<pi>\<^sub>V_inverse by presburger

lemma VCagree_upds: "sorteq z d \<Longrightarrow> VCagree \<omega> (upds \<omega> z d) (-\<iota>\<^sub>V {z})"
  using VCagree_def Vagree_sfilter_cong Vagree_upds \<pi>\<^sub>V_compl \<pi>\<^sub>V_inverse by presburger

lemma Vagree_single_upds: "Vagree \<nu> \<omega> (-{z}) = (upds \<nu> z (\<omega> $$ z) = \<omega>)"
  apply (auto simp add: Vagree_def state_eqI)
  by (metis sorteq_self_val upds_access)

lemma Vagree_self_sttconc_on_rvars [simp]: "Vagree \<nu> (\<nu> @@ \<tau>) (\<iota>\<^sub>R V)"
  apply (rule Vagree_by_sortI)
  by (simp_all add: eqon_def sttconc_def iota_rvars_def)
  
lemma Vagree_sttconc_on_rvars [simp]: "Vagree \<nu> (\<omega> @@ \<tau>) (\<iota>\<^sub>R V) = Vagree \<nu> \<omega> (\<iota>\<^sub>R V)"
  using Vagree_only_trans Vagree_self_sttconc_on_rvars Vagree_sym by blast

lemma Vagree_sttconc_cong: "Vagree \<nu> \<omega> X \<Longrightarrow> Vagree (\<nu> @@ \<tau>) (\<omega> @@ \<tau>) X"
  apply (rule Vagree_by_sortI)
  by (auto simp add: Vagree_def eqon_def sttconc_def)

lemma Vagree_sfilter_onR: "Vagree \<nu> (sfilter \<nu> Y) (\<iota>\<^sub>R \<V>\<^sub>R)"
  by (rule Vagree_by_sortI) (simp_all)

lemma sfilter_singleton_compl_Vagree: 
  "sfilter \<nu> (-{(h, ch)}) = sfilter \<omega> (-{(h, ch)}) \<Longrightarrow> Vagree \<nu> \<omega> (-{Tv h})"
  apply (rule Vagree_by_sortI)
   apply (metis eqon_refl stR_sfilter)
  unfolding eqon_def apply simp
  using tsfilter_eq_singleton_compl_access_other stT_sfilter 
  by (metis Compl_iff singleton_iff)



paragraph \<open>Properties of Variation\<close>

lemma Uvariation_empty [simp]: "Uvariation \<nu> \<nu>' nobindrs = (\<nu>=\<nu>')"
  unfolding Uvariation_def VCagree_def by (simp add: pi_univ)

lemma Uvariation_univ [simp]: "Uvariation \<nu> \<nu>' allbindrs"
  by (auto simp add: Uvariation_def VCagree_def)

lemma Uvariation_refl [simp]: "Uvariation \<nu> \<nu> V"
  by (auto simp add: Uvariation_def)

lemma Uvariation_sym: "Uvariation \<omega> \<nu> U = Uvariation \<nu> \<omega> U"
  using Uvariation_def VCagree_def Vagree_sym_rel by blast

lemma Uvariation_sym_rel [sym]: "Uvariation \<omega> \<nu> U \<Longrightarrow> Uvariation \<nu> \<omega> U"
  using Uvariation_sym by auto



paragraph \<open>Lifting of Agreement\<close>

definition Vagreebot :: "statebot \<Rightarrow> statebot \<Rightarrow> variable set \<Rightarrow> bool"
  where "Vagreebot \<nu> \<nu>' U \<equiv> (\<nu> = NonFin \<and> \<nu>' = NonFin) \<or> 
        (\<exists>\<omega> \<omega>'. \<nu> = Fin \<omega> \<and> \<nu>' = Fin \<omega>' \<and> Vagree \<omega> \<omega>' U)"

lemma Vagreebot_only_Fin: "Vagreebot (Fin \<nu>) (Fin \<nu>') X = Vagree \<nu> \<nu>' X"
  using Vagreebot_def by blast

lemma Vagreebot_trans: "Vagreebot \<omega> \<omega>' V \<Longrightarrow> Vagreebot \<omega>' \<omega>'' W \<Longrightarrow> Vagreebot \<omega> \<omega>'' (V\<inter>W)"
  unfolding Vagreebot_def Vagree_def by auto

lemma Vagreebot_NonFin [simp, intro]: 
  shows "Vagreebot NonFin NonFin X" 
    and "\<not> Vagreebot (Fin \<omega>) NonFin X" 
    and "\<not> Vagreebot NonFin (Fin \<omega>) X"
  using Vagreebot_def by simp_all

lemma Vagreebot_sym: "Vagreebot (Fin \<nu>) (Fin \<omega>) X = Vagreebot (Fin \<omega>) (Fin \<nu>) X"
  unfolding Vagreebot_def using Vagree_sym by blast

lemma Vagreebot_sym_rel [sym]: "Vagreebot (Fin \<nu>) (Fin \<omega>) X \<Longrightarrow> Vagreebot (Fin \<omega>) (Fin \<nu>) X"
  by (simp add: Vagreebot_sym)

lemma Vagreebot_snd_NonFin: "Vagreebot (Fin \<nu>) \<omega> X \<Longrightarrow> \<exists>\<omega>'. \<omega> = Fin \<omega>'"
  by (auto simp add: Vagreebot_def)



subsection \<open>Interpretations\<close>

text \<open>This section defines interpretations as a type\<close>

type_synonym chp_domain = "(state, recevent) domain"

paragraph \<open>Denotational Static Semantics\<close>


text \<open>The denotational static semantics defines notions of free (variable and channel) names and bound 
names for denotations rather than for syntactical objects. The denotations of expressions are 
evaluation functions from state to value and the denotation of a program is a set of computations.\<close>

text \<open>Free names of the evaluation function \<open>E\<close>\<close>
definition FNF :: "(state \<Rightarrow> 'a) \<Rightarrow> bindr set"
  where "FNF E = {b. \<exists>\<nu>.\<exists>\<omega>. VCagree \<nu> \<omega> (-{b}) \<and> \<not>(E \<nu> = E \<omega>)}"

text \<open>Free variables of the denotation \<open>D\<close>, i.e. variables whose value can force different behavior\<close>
definition FVD :: "chp_domain set \<Rightarrow> variable set"
  where "FVD D = {z. \<exists>\<nu>\<^sub>1 \<nu>\<^sub>2 \<tau>\<^sub>1 \<omega>\<^sub>1. (Vagree \<nu>\<^sub>1 \<nu>\<^sub>2 (-{z})) \<and> (\<nu>\<^sub>1, \<tau>\<^sub>1, \<omega>\<^sub>1) \<in> D 
    \<and> \<not>(\<exists>\<tau>\<^sub>2 \<omega>\<^sub>2. (\<nu>\<^sub>2, \<tau>\<^sub>2, \<omega>\<^sub>2) \<in> D \<and> \<tau>\<^sub>1 = \<tau>\<^sub>2 \<and> (Vagreebot \<omega>\<^sub>1 \<omega>\<^sub>2 (-{z})))}"


fun bclose :: "bindr \<Rightarrow> bindr set"
  where 
  "bclose (Bv (Rv x)) = {Bv (Rv x)}"
| "bclose (Bv (Tv h)) = {Bv (Tv h)} \<union> {Bc h ch | ch. True}"
| "bclose (Bc h ch) = {Bc h ch, Bv (Tv h)}"

text \<open>Bound names of the denotation \<open>D\<close>\<close>
definition BND :: "chp_domain set \<Rightarrow> bindr set"
  where "BND D = {b. \<exists>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> D \<and> \<not>(VCagree \<nu> ((\<omega> \<squnion> \<nu>) @@ \<tau>) (bclose b))}"


text \<open>Variables bound by the denotation \<open>D\<close> form the initial to the final state\<close>
definition DiffD :: "chp_domain set \<Rightarrow> variable set"
  where "DiffD D = {z. \<exists>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, Fin \<omega>) \<in> D \<and> \<omega> $$ z \<noteq> \<nu> $$ z}"



paragraph \<open>Computational Domain of CHPs\<close>

text \<open>Denotations of programs are prefix-closed and total, only depend on the real state, and trace 
variables do not change from the initial to the final state.\<close>
definition is_denotation :: "chp_domain set \<Rightarrow> bool"
  where "is_denotation D \<equiv> pc D \<and> total D \<and> FVD D \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R \<and> DiffD D \<subseteq> -(\<iota>\<^sub>T \<V>\<^sub>T)"


text \<open>A program symbol a(Y, Z) synchronizes on the channels Y (which implies that it at most writes
the channels Y) and it only writes the variables Z\<close>
definition bound_effect :: "chp_domain set \<Rightarrow> bindr set \<Rightarrow> bool"
  where "bound_effect D Z = (BND D \<subseteq> Z)"

lemma leastComp_BVD: "DiffD \<bottom>\<^sub>\<D> \<subseteq> -(\<iota>\<^sub>T \<V>\<^sub>T)"
  by (simp add: DiffD_def)

lemma leastComp_FVD: "FVD \<bottom>\<^sub>\<D> \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R"
  by (simp add: FVD_def)

lemma leastComp_is_denotation [simp, intro]: "is_denotation \<bottom>\<^sub>\<D>"
  using is_denotation_def leastComp_pc leastComp_total leastComp_BVD leastComp_FVD by blast

lemma leastComp_is_bound_effect [simp, intro]: "bound_effect \<bottom>\<^sub>\<D> Z"
  using leastComp_is_denotation by (auto simp add: bound_effect_def BND_def FVD_def)

lemma FVD_leastComp_bound: "FVD \<bottom>\<^sub>\<D> \<subseteq> \<iota>\<^sub>R X"
  by (simp add: FVD_def)



paragraph \<open>Interpretation of Predicationals\<close>

text \<open>Predicates with spaces p(Z)(\<Theta>) generalize the notion of predicate p(\<Theta>), which depends on the 
arguments \<Theta>, with a symbolic space of names Z on which the evaluation of p(Z)(\<Theta>) additionally depends. 
That is, p(Z)(\<Theta>) evaluates equally over two states if the arguments \<Theta> receive the same values in 
these states and if the states coincide when restricted to the names Z.\<close>

type_synonym 'a pinterp_raw = "variable set \<Rightarrow> (state \<Rightarrow> vals list \<Rightarrow> 'a)"

definition is_pinterp :: "'a pinterp_raw \<Rightarrow> bool"
  where "is_pinterp I = (\<forall>Z. FNF (I (\<pi>\<^sub>V Z)) \<inter> \<iota>\<^sub>V \<V> \<subseteq> Z)"

definition dflt_pinterp_raw :: "'a pinterp_raw" 
    where "dflt_pinterp_raw = (\<lambda>_ _ _. (SOME d. True))"

lemma dflt_is_pinterp [simp, intro]: "is_pinterp dflt_pinterp_raw" 
  unfolding is_pinterp_def dflt_pinterp_raw_def FNF_def by simp

typedef 'a pinterp = "{I:: 'a pinterp_raw. is_pinterp I}"
  morphisms PInterp well_PInterp
  by auto

setup_lifting type_definition_pinterp

lift_definition mkpinterp :: "'a pinterp_raw \<Rightarrow> 'a pinterp"
  is "\<lambda>I. (if is_pinterp I then I else dflt_pinterp_raw)"
  by auto


definition fullspace :: "bindr set \<Rightarrow> variable set"
  where "fullspace U = \<pi>\<^sub>V U - { Tv h | h. \<pi>\<^sub>C U `` {h} \<noteq> \<Omega>}"

lemma access_mkpinterp [simp]: "PInterp (mkpinterp I) = (if is_pinterp I then I else dflt_pinterp_raw)"
  by (transfer, simp)

lemma PInterp_correct [simp, intro]: "is_pinterp (PInterp I)"
  by (transfer, simp)     

(* Predicates that are not state-dependent *)
lift_definition Pred :: "'a pinterp \<Rightarrow> (vals list \<Rightarrow> 'a)"
  is "\<lambda>I. \<lambda>d. I {} (SOME \<nu>. True) d" .

lemma Pred_mkpinterp: "Pred (mkpinterp I) = (if is_pinterp I 
  then I {} (SOME \<nu>. True) else dflt_pinterp_raw {} (SOME \<nu>. True))"
  by (transfer, simp)

lemma Pred_correct [simp]: "is_pinterp (\<lambda>_ _. Pred I)"
  apply transfer unfolding is_pinterp_def FNF_def by blast

definition QRPred :: "'a pinterp \<Rightarrow> (real list \<Rightarrow> 'a)"
  where "QRPred I = (\<lambda>d. Pred I (map Rp d))"

lifting_update pinterp.lifting
lifting_forget pinterp.lifting

definition dflt_pinterp :: "'a pinterp"
  where "dflt_pinterp = mkpinterp dflt_pinterp_raw"





paragraph \<open>Interpretation of Channel and Variable Constants\<close>

record binterp = 
  BConsts\<^sub>\<Omega> :: "ident \<Rightarrow> chan set"
  BConsts\<^sub>R\<^sub>V0 :: "ident \<Rightarrow> rvar set"

abbreviation mkbinterp :: "(ident \<Rightarrow> chan set) \<Rightarrow> (ident \<Rightarrow> rvar set) \<Rightarrow> binterp"
  where "mkbinterp J\<^sub>\<Omega> J\<^sub>R\<^sub>V \<equiv> \<lparr> BConsts\<^sub>\<Omega> = J\<^sub>\<Omega>, BConsts\<^sub>R\<^sub>V0 = J\<^sub>R\<^sub>V \<rparr>"

abbreviation BConsts\<^sub>R\<^sub>V :: "binterp \<Rightarrow> ident \<Rightarrow> rvar set"
  where "BConsts\<^sub>R\<^sub>V J X \<equiv> BConsts\<^sub>R\<^sub>V0 J X"

lemma BConsts\<^sub>R\<^sub>V_correct [simp, intro]: "BConsts\<^sub>R\<^sub>V J X \<subseteq> \<V>\<^sub>R" by auto



paragraph \<open>Interpretation of Program Constants\<close>

type_synonym raw_chpinterp = "ident \<Rightarrow> (variable set \<Rightarrow> chan set \<Rightarrow> chp_domain set)"

abbreviation is_chp_denotation :: "raw_chpinterp \<Rightarrow> ident \<Rightarrow> variable set \<Rightarrow> chan set \<Rightarrow> bool"
  where "is_chp_denotation D a Z Y \<equiv> (is_denotation (D a Z Y) \<and> bound_effect (D a Z Y) (\<iota>\<^sub>V Z \<union> (\<iota>\<^sub>C (\<pi>\<^sub>T Z \<times> Y))) \<and> FVD (D a Z Y) \<subseteq> Z)"

definition is_chpinterp :: "raw_chpinterp \<Rightarrow> bool"
  where "is_chpinterp D = (\<forall>a Z Y. is_chp_denotation D a Z Y)"

lemma leastComp_is_chpinterp [simp, intro]: "is_chpinterp (\<lambda>_ _ _. \<bottom>\<^sub>\<D>)"
  unfolding is_chpinterp_def FVD_def by blast

typedef chpinterp = "{D:: raw_chpinterp. is_chpinterp D}"
  morphisms raw_interp well_interp
  by auto

setup_lifting type_definition_chpinterp

lift_definition Chps_raw :: "chpinterp \<Rightarrow> (ident \<Rightarrow> (variable set \<Rightarrow> chan set \<Rightarrow> chp_domain set))" is "\<lambda>D. D" .

lift_definition mkchpinterp:: "raw_chpinterp \<Rightarrow> chpinterp" 
  is "\<lambda>D. if is_chpinterp D then D else (\<lambda>_ _ _. \<bottom>\<^sub>\<D>)"
  apply auto
    apply (simp add: is_chpinterp_def)
  using is_chpinterp_def leastComp_is_chpinterp by auto

lemma mkchpinterp_Chps_raw [simp, intro]: "mkchpinterp (Chps_raw I) = I"
  apply transfer by auto

lemma access_mkchpinterp [simp]:
    "Chps_raw (mkchpinterp D) = (if is_chpinterp D then D else (\<lambda>_ _ _. \<bottom>\<^sub>\<D>))"
  by (transfer, auto)

lemma Chps_raw_correct [simp, intro]: "is_chpinterp (Chps_raw I)"
  by (transfer, auto)

lifting_update chpinterp.lifting
lifting_forget chpinterp.lifting

definition dflt_chpinterp where "dflt_chpinterp = mkchpinterp (\<lambda>_ _ _. \<bottom>\<^sub>\<D>)"

lemma chpinterp_eqI: "Chps_raw I\<^sub>1 = Chps_raw I\<^sub>2 \<Longrightarrow> I\<^sub>1 = I\<^sub>2"
  by (metis mkchpinterp_Chps_raw)



paragraph \<open>Interpretations and Liftings\<close>

text \<open>Interpretations of dLCHP as record of interpretations for every type of symbol\<close>
                                
record interp =                         
  AllRConsts :: "bool \<Rightarrow> ident \<Rightarrow> nat \<Rightarrow> real"
  AllRFuncs :: "bool \<Rightarrow> ident \<Rightarrow> real pinterp"
  TConsts :: "ident \<Rightarrow> nat \<Rightarrow> trace"
  TFuncs :: "ident \<Rightarrow> trace pinterp"
  AllPsymbs :: "bool \<Rightarrow> ident \<Rightarrow> bool pinterp"
  Chps0 :: "chpinterp"
  Bindrs :: "binterp"

abbreviation dflt_interp :: interp
  where "dflt_interp \<equiv> \<lparr>
    AllRConsts = \<lambda>_ _ _. 0, 
    AllRFuncs = \<lambda>_ _. dflt_pinterp, 
    TConsts = \<lambda>_ _. [], 
    TFuncs = \<lambda>_. dflt_pinterp, 
    AllPsymbs = \<lambda>_ _. dflt_pinterp,
    Chps0 = dflt_chpinterp,
    Bindrs = \<lparr> BConsts\<^sub>\<Omega> = \<lambda>_. {}, BConsts\<^sub>R\<^sub>V0 = \<lambda>_. {} \<rparr> \<rparr>"

lemma interp_eqI: "AllRConsts I = AllRConsts J \<Longrightarrow> AllRFuncs I = AllRFuncs J \<Longrightarrow> TConsts I = TConsts J \<Longrightarrow> TFuncs I = TFuncs J \<Longrightarrow> AllPsymbs I = AllPsymbs J \<Longrightarrow> Chps0 I = Chps0 J \<Longrightarrow> Bindrs I = Bindrs J \<Longrightarrow> (I::interp) = J"
  by simp

definition Chps :: "interp \<Rightarrow> ident \<Rightarrow> (variable set \<Rightarrow> chan set \<Rightarrow> chp_domain set)"
  where "Chps I = Chps_raw (Chps0 I)"

definition Consts\<^sub>\<Omega>:: "interp \<Rightarrow> ident \<Rightarrow> chan set" 
  where "Consts\<^sub>\<Omega> I = BConsts\<^sub>\<Omega> (Bindrs I)"

definition Consts\<^sub>R\<^sub>V:: "interp \<Rightarrow> ident \<Rightarrow> rvar set"
  where "Consts\<^sub>R\<^sub>V I = BConsts\<^sub>R\<^sub>V (Bindrs I)"

notation Bindrs ("\<pi>\<^sub>I")

definition RConsts :: "interp \<Rightarrow> ident \<Rightarrow> nat \<Rightarrow> real" where "RConsts I \<equiv> AllRConsts I False"
definition RFuncs :: "interp \<Rightarrow> ident \<Rightarrow> real pinterp" where "RFuncs I \<equiv> AllRFuncs I False"
definition QRConsts :: "interp \<Rightarrow> ident \<Rightarrow> nat \<Rightarrow> real" where "QRConsts I \<equiv> AllRConsts I True"
definition QRFuncs :: "interp \<Rightarrow> ident \<Rightarrow> (real list \<Rightarrow> real)" 
  where "QRFuncs I f = QRPred (AllRFuncs I True f)"
definition Psymbs :: "interp \<Rightarrow> ident \<Rightarrow> bool pinterp" where "Psymbs I \<equiv> AllPsymbs I False"
definition QRPsymbs :: "interp \<Rightarrow> ident \<Rightarrow> (real list \<Rightarrow> bool)" 
  where "QRPsymbs I p = QRPred (AllPsymbs I True p)"



(* Ensures that Chps_mkinterp_self gets applied *)


lemma Consts\<^sub>R\<^sub>V_correct [simp, intro]: "(Consts\<^sub>R\<^sub>V I) i \<subseteq> \<V>\<^sub>R"
  apply transfer
  using BConsts\<^sub>R\<^sub>V_correct Consts\<^sub>R\<^sub>V_def by auto

lemma Chps_correct0 [simp, intro]: "is_chpinterp (Chps I)"                       
  by (auto simp add: Chps_def)

lemma Chps_access_success [simp, intro]: "is_chpinterp D \<Longrightarrow> Chps_raw (mkchpinterp D) = D"
  by simp

lemma Chps_correct [simp, intro]: 
  shows "is_denotation ((Chps I) a Z Y)"
    and "bound_effect ((Chps I) a Z Y) (\<iota>\<^sub>V Z \<union> (\<iota>\<^sub>C (\<pi>\<^sub>T Z \<times> Y)))"
    and "FVD ((Chps I) a Z Y) \<subseteq> Z"
  using is_chpinterp_def by blast+

lemma mkchpinterp_Chps [simp, intro]: "mkchpinterp (Chps I) = Chps0 I"
  unfolding Chps_def by auto

lemma binterp_has_interp: "\<exists>I. J = \<pi>\<^sub>I I" by (metis interp.select_convs(7))





    


subsection \<open>Semantics\<close>

paragraph \<open>Semantics of Channel and Variable Spaces\<close>

fun cspace_sem :: "binterp \<Rightarrow> cspace \<Rightarrow> chan set"
  where
  "cspace_sem J \<top>\<^sub>\<Omega> = \<Omega>"
| "cspace_sem J (CChan ch) = {ch}"
| "cspace_sem J (CConst Y) = (BConsts\<^sub>\<Omega> J) Y"
| "cspace_sem J (-\<^sub>\<Omega> e) = (-(cspace_sem J e))"
| "cspace_sem J (Y\<^sub>1 \<inter>\<^sub>\<Omega> Y\<^sub>2) = cspace_sem J Y\<^sub>1 \<inter> cspace_sem J Y\<^sub>2"

fun vspace_sem :: "binterp \<Rightarrow> vspace \<Rightarrow> variable set" 
  where
  "vspace_sem J \<top>\<^sub>R = \<iota>\<^sub>R \<V>\<^sub>R"
| "vspace_sem J (VRVar x) = { Rv x }"
| "vspace_sem J (VTVar h) = { Tv h }"
| "vspace_sem J (VRConst X) = \<iota>\<^sub>R ((BConsts\<^sub>R\<^sub>V J) X)"
| "vspace_sem J (-\<^sub>V X) = -vspace_sem J X"
| "vspace_sem J (X \<inter>\<^sub>V Z) = vspace_sem J X \<inter> vspace_sem J Z"

abbreviation rvspace_sem :: "binterp \<Rightarrow> vspace \<Rightarrow> rvar set"
  where "rvspace_sem J Z \<equiv> \<pi>\<^sub>R (vspace_sem J Z)"



paragraph \<open>Semantics of Terms\<close>

type_synonym arg_sem_type = "interp \<Rightarrow> arg \<Rightarrow> (state \<Rightarrow> vals)"

definition args_sem_pre :: "interp \<Rightarrow> arg list \<Rightarrow> arg_sem_type \<Rightarrow> (state \<Rightarrow> vals list)"
  where "args_sem_pre I \<Theta> arg_sem \<equiv> (\<lambda>\<omega>. map (\<lambda>\<theta>. arg_sem I \<theta> \<omega>) \<Theta>)"

(* Used by Isabelle for proving termination *)
lemma args_sem_pre_cong [fundef_cong]: "\<lbrakk> I = J; \<Theta>\<^sub>1 = \<Theta>\<^sub>2; \<And>\<theta>. \<theta> \<in> set \<Theta>\<^sub>1 \<Longrightarrow> sem\<^sub>1 I \<theta> = sem\<^sub>2 J \<theta> \<rbrakk> 
  \<Longrightarrow> args_sem_pre I \<Theta>\<^sub>1 sem\<^sub>1 = args_sem_pre J \<Theta>\<^sub>2 sem\<^sub>2"
  unfolding args_sem_pre_def by auto

abbreviation chan_to_reals :: "char \<Rightarrow> real" 
  where "chan_to_reals \<equiv> of_char"

fun rtrm_sem :: "interp \<Rightarrow> rtrm \<Rightarrow> (state \<Rightarrow> real)" and
    ttrm_sem :: "interp \<Rightarrow> ttrm \<Rightarrow> (state \<Rightarrow> trace)" and
    arg_sem :: "interp \<Rightarrow> arg \<Rightarrow> (state \<Rightarrow> vals)"
  where
  "rtrm_sem I (RVar x) = (\<lambda>\<omega>. (stR \<omega>)(x))"
| "rtrm_sem I (RConst b f n) = (\<lambda>\<omega>. AllRConsts I b f n)"
| "rtrm_sem I (RFunc b f Z \<Theta>) = (\<lambda>\<omega>. (PInterp (AllRFuncs I b f) (vspace_sem (\<pi>\<^sub>I I) Z) \<omega> (args_sem_pre I \<Theta> arg_sem \<omega>)))"
| "rtrm_sem I (Number r) = (\<lambda>\<omega>. r)"
| "rtrm_sem I (Plus \<theta> \<eta>) = (\<lambda>\<omega>. rtrm_sem I \<theta> \<omega> + rtrm_sem I \<eta> \<omega>)"
| "rtrm_sem I (Times \<theta> \<eta>) = (\<lambda>\<omega>. rtrm_sem I \<theta> \<omega> * rtrm_sem I \<eta> \<omega>)"
| "rtrm_sem I (ChanOf te) = (\<lambda>\<omega>. chan_to_reals(chname (along (last (ttrm_sem I te \<omega>)))))"
| "rtrm_sem I (ValOf te) = (\<lambda>\<omega>. val (last (ttrm_sem I te \<omega>)))"
| "rtrm_sem I (TimeOf te) = (\<lambda>\<omega>. stamp (last (ttrm_sem I te \<omega>)))"
| "rtrm_sem I (LenT te) = (\<lambda>\<omega>. length(ttrm_sem I te \<omega>))"

| "ttrm_sem I (TVar h) = (\<lambda>\<omega>. ((stT \<omega>)(h)))"
| "ttrm_sem I (TConst f n) = (\<lambda>\<omega>. (TConsts I f n))"
| "ttrm_sem I (TFunc f Z \<Theta>) = (\<lambda>\<omega>. (PInterp (TFuncs I f) (vspace_sem (\<pi>\<^sub>I I) Z) \<omega> (args_sem_pre I \<Theta> arg_sem \<omega>)))"
| "ttrm_sem I Empty = (\<lambda>\<omega>. [])"
| "ttrm_sem I (ComItm ch \<theta> \<eta>) = (\<lambda>\<omega>. [mkevent ch (rtrm_sem I \<theta> \<omega>) (rtrm_sem I \<eta> \<omega>)])"
| "ttrm_sem I (Concat te\<^sub>1 te\<^sub>2) = (\<lambda>\<omega>. ttrm_sem I te\<^sub>1 \<omega> @ ttrm_sem I te\<^sub>2 \<omega>)" 
| "ttrm_sem I (Proj te Y) = (\<lambda>\<omega>. (ttrm_sem I te \<omega>) \<down> (cspace_sem (\<pi>\<^sub>I I) Y))"
| "ttrm_sem I (Access te \<theta>) = (\<lambda>\<omega>. if nat \<lfloor> rtrm_sem I \<theta> \<omega> \<rfloor> < length (ttrm_sem I te \<omega>) 
     then [nth (ttrm_sem I te \<omega>) (nat \<lfloor> rtrm_sem I \<theta> \<omega> \<rfloor>)] else [])"

| "arg_sem I (RArg \<eta>) = (\<lambda>\<omega>. Rp (rtrm_sem I \<eta> \<omega>))"           
| "arg_sem I (TArg te) = (\<lambda>\<omega>. Tp (ttrm_sem I te \<omega>))"

definition args_sem :: "interp \<Rightarrow> arg list \<Rightarrow> (state \<Rightarrow> vals list)" 
  where "args_sem I \<Theta> \<equiv> (\<lambda>\<omega>. map (\<lambda>\<theta>. arg_sem I \<theta> \<omega>) \<Theta>)"

lemma args_sem_pre_args_sem [simp]: "args_sem_pre I \<Theta> arg_sem \<omega> = args_sem I \<Theta> \<omega>"
  unfolding args_sem_pre_def args_sem_def by simp

abbreviation rargs_sem :: "interp \<Rightarrow> rtrm list \<Rightarrow> (state \<Rightarrow> real list)"
  where "rargs_sem I \<Theta> \<equiv> \<lambda>\<omega>. map (\<lambda>\<theta>. rtrm_sem I \<theta> \<omega>) \<Theta>"

lemma rargs_semI: "(\<And>\<theta>. \<theta> \<in> set \<Theta> \<Longrightarrow> rtrm_sem I \<theta> \<nu> = rtrm_sem I \<theta> \<omega>) \<Longrightarrow> rargs_sem I \<Theta> \<nu> = rargs_sem I \<Theta> \<omega>"
  by simp

(* lemma purify_ttrm_sem_idem: "ptrace (ttrm_sem I te \<nu>) = ttrm_sem I te \<nu>"
  apply (induction te rule: ttrm_induct)
         apply (simp_all add: ptrace_nth_idem)
    apply (simp_all add: ptrace_def)
  using ptrace_def ptrace_nth_idem by presburger *)
  


  
paragraph \<open>Semantic operators for programs\<close>


lemma lmerge_vagree: "(\<omega> = lmerge \<omega>\<^sub>1 \<omega>\<^sub>2 X) = (Vagree \<omega> \<omega>\<^sub>1 X \<and> Vagree \<omega> \<omega>\<^sub>2 (-X))"
  unfolding Vagree_def using lmerge_access state_eqI by auto  

lemma lmerge_bound_vars: "Vagree \<nu> \<omega>\<^sub>1 V \<and> Vagree \<nu> \<omega>\<^sub>2 W \<and> \<omega> = lmerge \<omega>\<^sub>1 \<omega>\<^sub>2 X \<Longrightarrow> Vagree \<nu> \<omega> (V\<inter>W)"
  using Vagree_def by auto







paragraph \<open>State-trace prefix sets\<close>

definition g_assm_set :: "(recevent list \<Rightarrow> recevent list \<Rightarrow> bool) \<Rightarrow> state \<Rightarrow> rectrace \<Rightarrow> state set"
  where "g_assm_set rel \<nu> \<tau> = { \<nu> @@ \<tau>' | \<tau>'. rel \<tau>' \<tau> }"

abbreviation strict_assm_set where "strict_assm_set \<nu> \<tau> \<equiv> g_assm_set strict_prefix \<nu> \<tau>"
abbreviation assm_set where "assm_set \<nu> \<tau> \<equiv> g_assm_set prefix \<nu> \<tau>"

lemma strict_assm_nocom_empty [simp]: "strict_assm_set \<nu> [] = {}" 
  by (simp add: g_assm_set_def)

lemma assm_set_contains_boundary [simp]: "\<nu> @@ \<tau> \<in> assm_set \<nu> \<tau>"
  using g_assm_set_def by auto

lemma weaken_assm_set: "strict_assm_set \<nu> \<tau> \<subseteq> assm_set \<nu> \<tau>"
  unfolding g_assm_set_def using prefix_order.less_imp_le by blast

lemma assm_set_kernel_plus_boundary: "{\<nu> @@ \<tau>} \<union> strict_assm_set \<nu> \<tau> = assm_set \<nu> \<tau>"
  apply rule                                    
  using assm_set_contains_boundary weaken_assm_set apply auto[1]
  using pref_split g_assm_set_def by auto

lemma assm_set_pc: "prefix \<tau>' \<tau> \<Longrightarrow> assm_set \<nu> \<tau>' \<subseteq> assm_set \<nu> \<tau>"
  unfolding g_assm_set_def using prefix_order.dual_order.trans by blast

lemma strict_assm_set_pc: "prefix \<tau>' \<tau> \<Longrightarrow> strict_assm_set \<nu> \<tau>' \<subseteq> strict_assm_set \<nu> \<tau>"
  unfolding g_assm_set_def using prefix_order.dual_order.strict_trans1 by blast

lemma assm_subseteq_sassm_non_empty_extension: "\<tau>\<^sub>2 \<noteq> [] \<Longrightarrow> assm_set \<nu> \<tau>\<^sub>1 \<subseteq> strict_assm_set \<nu> (\<tau>\<^sub>1 @ \<tau>\<^sub>2)"
  using pref_spref_non_empty_extension g_assm_set_def by auto

lemma strict_assm_set_singleton: "strict_assm_set \<nu> [\<rho>] = { \<nu> }"
  apply (auto simp add: g_assm_set_def)
   apply (metis strict_perfix_singleton sttconc_empty)
  by (metis strict_prefix_simps(2) sttconc_empty)

text \<open>Subsets for concatenations in assm_set\<close>

lemma assm_set_prefix: "assm_set \<nu> \<tau>\<^sub>1 \<subseteq> assm_set \<nu> (\<tau>\<^sub>1 @ \<tau>\<^sub>2)" 
  using assm_set_pc by auto

lemma assm_set_strict_prefix: "strict_assm_set \<nu> \<tau>\<^sub>1 \<subseteq> strict_assm_set \<nu> (\<tau>\<^sub>1 @ \<tau>\<^sub>2)"
  using strict_assm_set_pc by auto

lemma prefix_sttconc_weaken: "\<tau>' \<preceq> \<tau>\<^sub>2 \<and> \<nu>' = (\<nu> @@ \<tau>\<^sub>1) @@ \<tau>' \<Longrightarrow> \<exists>\<tau>'. \<tau>' \<preceq> (\<tau>\<^sub>1 @ \<tau>\<^sub>2) \<and> \<nu>' = \<nu> @@ \<tau>'"
  by (metis same_prefix_prefix sttconc_dist_app)
  
lemma assm_set_sttconc_weaken: "assm_set (\<nu> @@ \<tau>\<^sub>1) \<tau>\<^sub>2 \<subseteq> assm_set \<nu> (\<tau>\<^sub>1 @ \<tau>\<^sub>2)"
  unfolding g_assm_set_def using prefix_sttconc_weaken by fastforce

lemma sprefix_sttconc_weaken: "\<tau>' \<prec> \<tau>\<^sub>2 \<and> \<nu>' = (\<nu> @@ \<tau>\<^sub>1) @@ \<tau>' \<Longrightarrow> \<exists>\<tau>'. \<tau>' \<prec> (\<tau>\<^sub>1 @ \<tau>\<^sub>2) \<and> \<nu>' = \<nu> @@ \<tau>'"
  by (metis append.assoc strict_prefixE' strict_prefixI' sttconc_dist_app)

lemma strict_assm_set_sttconc_weaken: "strict_assm_set (\<nu> @@ \<tau>\<^sub>1) \<tau>\<^sub>2 \<subseteq> strict_assm_set \<nu> (\<tau>\<^sub>1 @ \<tau>\<^sub>2)"
  unfolding g_assm_set_def using sprefix_sttconc_weaken by fastforce

text \<open>Supersets for concatenations in assm_set\<close>

lemma g_assm_set_dist_app:
  assumes "prefrel rel"
  shows "g_assm_set rel \<nu> (\<tau>\<^sub>1 @ \<tau>\<^sub>2) \<subseteq> g_assm_set rel \<nu> \<tau>\<^sub>1 \<union> g_assm_set rel (\<nu> @@ \<tau>\<^sub>1) \<tau>\<^sub>2"
proof
  fix \<nu>'
  assume "\<nu>' \<in> g_assm_set rel \<nu> (\<tau>\<^sub>1 @ \<tau>\<^sub>2)"
  then obtain \<tau>' where 0: "rel \<tau>' (\<tau>\<^sub>1 @ \<tau>\<^sub>2) \<and> \<nu>' = \<nu> @@ \<tau>'" unfolding g_assm_set_def by blast
  hence "\<nu>' \<in> g_assm_set rel \<nu> \<tau>\<^sub>1 \<or> \<nu>' \<in> g_assm_set rel (\<nu> @@ \<tau>\<^sub>1) \<tau>\<^sub>2"
  proof (cases "rel \<tau>' \<tau>\<^sub>1")
    case True
    thus ?thesis using 0 g_assm_set_def by auto
  next
    case False
    then obtain \<tau>\<^sub>2' where "\<tau>' = \<tau>\<^sub>1 @ \<tau>\<^sub>2' \<and> rel \<tau>\<^sub>2' \<tau>\<^sub>2" using 0 assms not_prefix_of_append_left by blast
    thus ?thesis using 0 g_assm_set_def sttconc_def by auto
  qed
  thus "\<nu>' \<in> g_assm_set rel \<nu> \<tau>\<^sub>1 \<union> g_assm_set rel (\<nu> @@ \<tau>\<^sub>1) \<tau>\<^sub>2" by auto
qed

lemma assm_union: "assm_set \<nu> (\<tau>\<^sub>1 @ \<tau>\<^sub>2) \<subseteq> assm_set \<nu> \<tau>\<^sub>1 \<union> assm_set (\<nu> @@ \<tau>\<^sub>1) \<tau>\<^sub>2"
  using g_assm_set_dist_app by blast

lemma assm_union_strict_assm: "strict_assm_set \<nu> (\<tau>\<^sub>1 @ \<tau>\<^sub>2) \<subseteq> assm_set \<nu> \<tau>\<^sub>1 \<union> strict_assm_set (\<nu> @@ \<tau>\<^sub>1) \<tau>\<^sub>2"
   using assm_set_kernel_plus_boundary g_assm_set_dist_app by blast



paragraph \<open>Semantics of Formulas and Communicating Hybrid Programs\<close>

text \<open>Channel names occurring in a program (syntactically)\<close>
fun CN :: "binterp \<Rightarrow> chp \<Rightarrow> chan set" where
  "CN J (Chp a Z Y) = cspace_sem J Y"
| "CN J (x := \<theta>) = {}"
| "CN J (Nondet x) = {}"
| "CN J (Test \<phi>) = {}"
| "CN J (Evolution x \<theta> \<phi>) = {}"
| "CN J (Choice \<alpha> \<beta>) = CN J \<alpha> \<union> CN J \<beta>"
| "CN J (Compose \<alpha> \<beta>) = CN J \<alpha> \<union> CN J \<beta>"
| "CN J (Loop \<alpha>) = CN J \<alpha>"
| "CN J (Send ch h \<theta>) = { ch }"
| "CN J (Receive ch h x) = { ch }"
| "CN J (\<alpha> par \<beta>) = CN J \<alpha> \<union> CN J \<beta>"



abbreviation bvrident :: "ident \<Rightarrow> variable set"
  where "bvrident x \<equiv> {Rv (RVarName x), Rv (DVarName x)}"

definition solves_ODE :: "interp \<Rightarrow> solution \<Rightarrow> ident \<Rightarrow> rtrm \<Rightarrow> bool"
where "solves_ODE I F x \<theta> \<equiv> (\<forall>\<zeta>::real.
     Vagree (F(0)) (F(\<zeta>)) (-(bvrident x))
   \<and> stR (F(\<zeta>)) (DVarName x) = deriv(\<lambda>t. stR (F(t)) (RVarName x))(\<zeta>)
   \<and> stR (F(\<zeta>)) (DVarName x) = rtrm_sem I \<theta> (F(\<zeta>)))"

definition solution_merge :: "state \<Rightarrow> solution \<Rightarrow> ident \<Rightarrow> solution"
  where "solution_merge \<nu> F x = (\<lambda>\<zeta>. rrepv (rrepv \<nu> (RVarName x) (stR (F(\<zeta>)) (RVarName x))) (DVarName x) (stR (F(\<zeta>)) (DVarName x)))"

text \<open>Mutual recursive definition of the semantics of formulas fml_sem and the semantics of programs
chp_sem. The program semantics relies on the (semantically) bound variables of its constituent 
programs BVP_pre\<close>
fun fml_sem :: "interp \<Rightarrow> fml \<Rightarrow> (state set)" and
    chp_sem :: "interp \<Rightarrow> chp \<Rightarrow> chp_domain set" and
    BVP_pre :: "binterp \<Rightarrow> chp \<Rightarrow> variable set"
where
  "fml_sem I (GPsymb b p Z \<Theta>) = {\<omega>. (PInterp (AllPsymbs I b p) (vspace_sem (\<pi>\<^sub>I I) Z) \<omega> (args_sem I \<Theta> \<omega>))}"
| "fml_sem I (Geq \<theta> \<eta>) = {\<omega>. rtrm_sem I \<theta> \<omega> \<ge> rtrm_sem I \<eta> \<omega>}"
| "fml_sem I (Pref \<theta> \<eta>) = {\<omega>. ttrm_sem I \<theta> \<omega> \<preceq> ttrm_sem I \<eta> \<omega>}"
| "fml_sem I (Not \<phi>) = {\<omega>. \<omega> \<notin> fml_sem I \<phi>}"
| "fml_sem I (And \<phi> \<psi>) = fml_sem I \<phi> \<inter> fml_sem I \<psi>"
| "fml_sem I (Exists z \<phi>) = {\<omega>. \<exists>d. sorteq z d \<and> upds \<omega> z d \<in> fml_sem I \<phi>}"
| "fml_sem I (Box \<alpha> \<psi>) = {\<nu>. \<forall>\<tau> \<omega>. (\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha> \<longrightarrow> \<omega> @@ \<tau> \<in> fml_sem I \<psi>}"
| "fml_sem I (AcBox \<alpha> A C \<psi>) = { \<nu>. \<forall>\<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha>
        \<longrightarrow> (strict_assm_set \<nu> \<tau> \<subseteq> fml_sem I A \<longrightarrow> \<nu> @@ \<tau> \<in> fml_sem I C)
            \<and> (\<omega> \<noteq> NonFin \<and> assm_set \<nu> \<tau> \<subseteq> fml_sem I A \<longrightarrow> (gets \<omega>) @@ \<tau> \<in> fml_sem I \<psi>)}"
| "fml_sem I (ChanIn ch Y) = {\<omega>. rtrm_sem I ch \<omega> \<in> { chan_to_reals (chname dh) | dh. dh \<in> cspace_sem (\<pi>\<^sub>I I) Y }}"

| "chp_sem I (Chp a Z Y) = (Chps I) a (vspace_sem (\<pi>\<^sub>I I) Z) (cspace_sem (\<pi>\<^sub>I I) Y)"
| "chp_sem I (x := \<theta>) = \<bottom>\<^sub>\<D> \<union> {(\<nu>, [], Fin \<omega>) | \<nu> \<omega>. \<omega> = rrepv \<nu> x (rtrm_sem I \<theta> \<nu>) }"
| "chp_sem I (Nondet x) = \<bottom>\<^sub>\<D> \<union> {(\<nu>, [], Fin \<omega>) | \<nu> \<omega>. \<exists>r. \<omega> = rrepv \<nu> x r }"
| "chp_sem I (Test \<phi>) = \<bottom>\<^sub>\<D> \<union> {(\<nu>, [], Fin \<nu>) | \<nu>. \<nu> \<in> fml_sem I \<phi> }"
| "chp_sem I (Evolution x \<theta> \<phi>) = \<bottom>\<^sub>\<D> \<union> {(\<nu>, [], Fin \<omega>) | \<nu> \<omega>. 
      (\<exists>F T. Vagree \<nu> (F(0)) (-{Rv (DVarName x)}) \<and> F(T) = \<omega> \<and> solves_ODE I F x \<theta> \<and> (\<forall>\<zeta>. F(\<zeta>) \<in> fml_sem I \<phi>)) }"
| "chp_sem I (Choice \<alpha> \<beta>) = chp_sem I \<alpha> \<union> chp_sem I \<beta>"
| "chp_sem I (Compose \<alpha> \<beta>) = botop (chp_sem I \<alpha>) \<union> (chp_sem I \<alpha>) \<triangleright> (chp_sem I \<beta>)"
| "chp_sem I (Loop \<alpha>) = rtcl_linhis (chp_sem I \<alpha>)" 
| "chp_sem I (Send ch h \<theta>) = {(\<nu>, \<tau>', \<omega>') | \<nu> \<tau>' \<omega>'. (\<tau>', \<omega>') \<sqsubseteq> ([mkrecevent h ch (rtrm_sem I \<theta> \<nu>) ((stR \<nu>)(\<mu>))], Fin \<nu>) }"
| "chp_sem I (Receive ch h x) = {(\<nu>, \<tau>', \<omega>') | \<nu> \<tau>' \<omega>'. \<exists>r. (\<tau>', \<omega>') \<sqsubseteq> ([mkrecevent h ch r ((stR \<nu>)(\<mu>))], Fin (rrepv \<nu> x r)) }"
| "chp_sem I (Par \<alpha> \<beta>) = {(\<nu>, \<tau>, \<omega>) | \<nu> \<tau> \<omega>. \<exists>\<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta>. 
    (\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha>), \<omega>\<^sub>\<alpha>) \<in> chp_sem I \<alpha> \<and> (\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<beta>), \<omega>\<^sub>\<beta>) \<in> chp_sem I \<beta> \<and>
    (Vagreebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> \<V>\<^sub>\<mu>) \<and> (\<omega> = lmergebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> (BVP_pre (\<pi>\<^sub>I I) \<alpha>)) \<and> \<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha> \<union> CN (\<pi>\<^sub>I I) \<beta>) = \<tau> }"

| "BVP_pre J \<alpha> = {z. \<exists>I. J = \<pi>\<^sub>I I \<and> (\<exists>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<and> ((\<omega> \<squnion> \<nu>) @@ \<tau>) $$ z \<noteq> \<nu> $$ z)}"

text \<open>For better proof automation the bound variables of a program (BVP_pre) find an identical 
definition (BVP) in theory Static_Semantics\<close>
declare BVP_pre.simps[simp del] (* BVP_pre shall act like a definition *)

lemma send_no_state_change: "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I (Send ch h \<theta>) \<Longrightarrow> \<nu> = \<omega>"
proof -
  assume "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I (Send ch h \<theta>)"
  hence "(\<tau>, Fin \<omega>) \<sqsubseteq> ([mkrecevent h ch (rtrm_sem I \<theta> \<nu>) (rval (\<nu> $$ (Rv \<mu>)))], Fin \<nu>)" by auto
  thus ?thesis by (simp add: obspref_alt)
qed

lemma receive_var_change: "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I (Receive ch h x) \<Longrightarrow> \<exists>r. \<omega> = rrepv \<nu> x r"
proof -
  assume "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I (Receive ch h x)"
  then obtain r where "(\<tau>, Fin \<omega>) \<sqsubseteq> ([mkrecevent h ch r (rval (\<nu> $$ (Rv \<mu>)))], Fin (rrepv \<nu> x r))" by auto
  thus ?thesis by (meson obspref_alt reachedstate.discI reachedstate.inject)
qed

fun expr_sem :: "interp \<Rightarrow> expr \<Rightarrow> (state \<Rightarrow> evals)" where
  "expr_sem I (Ertrm \<theta>) = (\<lambda>\<omega>. Rs (rtrm_sem I \<theta> \<omega>))"
| "expr_sem I (Ettrm te) = (\<lambda>\<omega>. Ts (ttrm_sem I te \<omega>))"
| "expr_sem I (Earg e) = (\<lambda>\<omega>. to_evals (arg_sem I e \<omega>))"
| "expr_sem I (Efml \<phi>) = (\<lambda>\<omega>. Bs (\<omega> \<in> fml_sem I \<phi>))"



text \<open>Validity\<close>

definition valid_in :: "interp \<Rightarrow> fml \<Rightarrow> bool"
where "valid_in I \<phi> \<equiv> (\<forall>\<omega>. \<omega> \<in> fml_sem I \<phi>)"

definition valid :: "fml \<Rightarrow> bool"
  where "valid \<phi> \<equiv> (\<forall>I.\<forall>\<omega>. \<omega> \<in> fml_sem I \<phi>)"

lemma valid_is_valid_in_all: "valid \<phi> = (\<forall>I. valid_in I \<phi>)"
  unfolding valid_def valid_in_def by auto

definition locally_sound :: "inference \<Rightarrow> bool"
  where "locally_sound R \<equiv>
  (\<forall>I. (\<forall>k. 0\<le>k \<longrightarrow> k<length (fst R) \<longrightarrow> valid_in I (nth (fst R) k)) \<longrightarrow> valid_in I (snd R))"

definition sound :: "inference \<Rightarrow> bool"
  where "sound R \<equiv>
  (\<forall>k. 0\<le>k \<longrightarrow> k<length (fst R) \<longrightarrow> valid (nth (fst R) k)) \<longrightarrow> valid (snd R)"

lemma locally_sound_is_sound: "locally_sound R \<Longrightarrow> sound R"
  unfolding locally_sound_def sound_def using valid_is_valid_in_all by auto



paragraph \<open>Typeclass for expression semantics\<close>

text \<open>Provides syntactic sugar especially for theory Coincidence\<close>
class expr = expr +
  fixes expr_sem :: "interp \<Rightarrow> 'a \<Rightarrow> (state \<Rightarrow> evals)"

instantiation rtrm :: expr
begin
definition "expr_sem I (\<theta>::rtrm) \<nu> = Rs (rtrm_sem I \<theta> \<nu>)"
instance ..
end

instantiation ttrm :: expr
begin
definition "expr_sem I (te::ttrm) \<nu> = Ts (ttrm_sem I te \<nu>)"
instance ..
end

instantiation arg :: expr
begin
definition "expr_sem I (e::arg) \<nu> = to_evals (arg_sem I e \<nu>)"
instance ..
end

instantiation fml :: expr
begin
definition "expr_sem I (\<phi>::fml) \<nu> = Bs (\<nu> \<in> (fml_sem I \<phi>))"
instance ..
end

lemma expr_sem_Arg [simp]: 
  shows "expr_sem I (RArg \<theta>) = expr_sem I \<theta>" 
    and "expr_sem I (TArg te) = expr_sem I te"
  using arg_sem.simps expr_sem_arg_def expr_sem_rtrm_def expr_sem_ttrm_def to_evals.simps by presburger+



subsection \<open>Observations\<close>

paragraph \<open>Semantics of Derived Spaces\<close>

lemma cspace_sem_CBot [simp]: "cspace_sem J \<bottom>\<^sub>\<Omega> = {}" by (simp add: CBot_def)
lemma cspace_sem_CCup [simp]: "cspace_sem J (Y\<^sub>1 \<union>\<^sub>\<Omega> Y\<^sub>2) = cspace_sem J Y\<^sub>1 \<union> cspace_sem J Y\<^sub>2" 
  by (simp add: CCup_def)

lemma vspace_sem_VCup [simp]: "vspace_sem J (X \<union>\<^sub>V Z) = vspace_sem J X \<union> vspace_sem J Z"
  by (simp add: VCup_def)

lemma vspace_sem_VTTop [simp]: "vspace_sem J \<top>\<^sub>T = \<iota>\<^sub>T \<V>\<^sub>T"
  by (simp add: VTTop_def)

lemma vspace_sem_VTop [simp]: "vspace_sem J \<top>\<^sub>V = \<V>"
  by (simp add: VTop_def compose_allvars)

lemma vspace_sem_VBot [simp]: "vspace_sem J \<bottom>\<^sub>V = {}"
  by (simp add: VBot_def)

lemma vspace_sem_RCompl [simp]: "vspace_sem J (-\<^sub>R X) = -vspace_sem J X \<inter> \<iota>\<^sub>R \<V>\<^sub>R"
  by (auto simp add: RCompl_def iota_vars_def iota_rvars_def)

lemma tvars_intersect_rvars_emtpy [simp, intro]: "\<iota>\<^sub>T \<V>\<^sub>T \<inter> \<iota>\<^sub>R \<V>\<^sub>R = {}"
  unfolding iota_tvars_def iota_rvars_def by blast

lemma vspace_sem_RCup [simp]: "vspace_sem J (X \<union>\<^sub>R Z) = (vspace_sem J X \<union> vspace_sem J Z) \<inter> \<iota>\<^sub>R \<V>\<^sub>R"
  apply (simp add: RCup_def) using tvars_intersect_rvars_emtpy by blast
  
lemma vspace_sem_BRvSet [simp]: "vspace_sem J (BRvSet xs) = {Rv x | x. x \<in> set xs}"
  apply (induction xs)
  by (auto simp add: BRvSet_def)

lemma vspace_sem_VRConst_only_rvars: "vspace_sem J (VRConst X) = \<iota>\<^sub>R (BConsts\<^sub>R\<^sub>V J X)"
  by (simp add: iota_vars_def)



lemma pi_vars_diff [simp]: "\<pi>\<^sub>V (Z - X) = \<pi>\<^sub>V Z - \<pi>\<^sub>V X" by (auto simp add: pi_vars_def)

lemma rvspace_sem [simp]:
  shows "rvspace_sem J (-\<^sub>V Z) = -(rvspace_sem J Z)"
    and "rvspace_sem J (X \<inter>\<^sub>V Z) = rvspace_sem J X \<inter> rvspace_sem J Z "
    and "rvspace_sem J (X \<union>\<^sub>R Z) = rvspace_sem J X \<union> rvspace_sem J Z"
  by (auto simp add: pi_vars_def)


lemma rspace_only_rvars [simp, intro!]: "Z \<in> rspace \<Longrightarrow> vspace_sem J Z \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R"
  by (induction rule: rspace.induct) (auto)
  
lemma rspace_no_tvars [simp]: "Z \<in> rspace \<Longrightarrow> \<pi>\<^sub>T (vspace_sem J Z) = {}"
  using rspace_only_rvars by fastforce





paragraph \<open>Semantics of Derived Terms\<close>

lemma rtrm_sem_QRConst [simp]: "rtrm_sem I (QRConst f n) = (\<lambda>\<omega>. (QRConsts I f n))"
  by (simp add: QRConst_def QRConsts_def)

lemma rtrm_sem_Neg [simp]: "rtrm_sem I (Neg \<theta>) \<nu> = - rtrm_sem I \<theta> \<nu>"
  by (simp add: Neg_def)

lemma rtrm_sem_Minus [simp]: "rtrm_sem I (Minus \<theta> \<eta>) \<nu> = rtrm_sem I \<theta> \<nu> - rtrm_sem I \<eta> \<nu>"
  by (simp add: Minus_def)

lemma rtrm_sem_Dec [simp]: "rtrm_sem I (Dec \<theta>) \<nu> = rtrm_sem I \<theta> \<nu> - 1" 
  by (simp add: Dec_def)



paragraph \<open>Semantics of Derived Formulas\<close>

lemma fml_sem_Psymb [simp]: "fml_sem I (Psymb p Z \<Theta>) = {\<omega>. PInterp (Psymbs I p) (vspace_sem (\<pi>\<^sub>I I) Z) \<omega> (args_sem I \<Theta> \<omega>) }"
  using Psymb_def Psymbs_def fml_sem.simps(1) by presburger

lemma fml_sem_Requals [simp]: "fml_sem I (\<theta> =\<^sub>R \<eta>) = {\<omega>. rtrm_sem I \<theta> \<omega> = rtrm_sem I \<eta> \<omega> }"
  unfolding REquals_def by auto

lemma fml_sem_TEquals [simp]: "fml_sem I (\<theta> =\<^sub>T \<eta>) = {\<omega>. ttrm_sem I \<theta> \<omega> = ttrm_sem I \<eta> \<omega> }"
  unfolding TEquals_def by auto

lemma fml_sem_SPref [simp]: "fml_sem I (te' \<prec>\<^sub>T te) = {\<omega>. ttrm_sem I te' \<omega> \<prec> ttrm_sem I te \<omega> }"
  unfolding SPref_def TEquals_def by auto

lemma fml_sem_Greater [simp]: "fml_sem I (\<theta> >\<^sub>R \<eta>) = {\<omega>. rtrm_sem I \<theta> \<omega> > rtrm_sem I \<eta> \<omega> }"
  unfolding Greater_def by auto
 
lemma fml_sem_not [simp]: "fml_sem I (Not \<phi>) = -fml_sem I \<phi>"
  by auto

lemma fml_sem_not_not [simp]: "fml_sem I (Not (Not \<phi>)) = fml_sem I \<phi>"
  by simp

lemma fml_sem_or [simp]: "fml_sem I (Or \<phi> \<psi>) = fml_sem I \<phi> \<union> fml_sem I \<psi>"
  unfolding Or_def by auto

lemma fml_sem_Implies [simp]: "fml_sem I (Implies \<phi> \<psi>) = (-fml_sem I \<phi>) \<union> fml_sem I \<psi>"
  unfolding Implies_def by auto

lemma fml_sem_TT [simp]: "fml_sem I TT = UNIV"
  unfolding TT_def by simp

lemma fml_sem_FF [simp]: "fml_sem I FF = {}" 
  unfolding FF_def by simp

lemma fml_sem_Exists_RVar [simp]: "fml_sem I (Exists (Rv x) \<phi>) = {\<omega>. \<exists>d. rrepv \<omega> x d \<in> fml_sem I \<phi>}"
  using sorteq_def by force

lemma fml_sem_Exists_Tvar [simp]: "fml_sem I (Exists (Tv h) \<phi>) = {\<omega>. \<exists>\<tau>. trepv \<omega> h \<tau> \<in> fml_sem I \<phi>}"
  using sorteq_def by force

lemma fml_sem_Forall [simp]: "fml_sem I (Forall z \<phi>) = {\<omega>. \<forall>d. sorteq z d \<longrightarrow> upds \<omega> z d \<in> fml_sem I \<phi>}"
  unfolding Forall_def by auto

lemma fml_sem_Forall_RVar [simp]: "fml_sem I (Forall (Rv x) \<phi>) = {\<omega>. \<forall>d. rrepv \<omega> x d \<in> fml_sem I \<phi>}"
  using sorteq_def fml_sem_Forall by force

lemma fml_sem_Forall_TVar [simp]: "fml_sem I (Forall (Tv h) \<phi>) = {\<omega>. \<forall>\<tau>. trepv \<omega> h \<tau> \<in> fml_sem I \<phi>}"
  using sorteq_def fml_sem_Forall by force


declare fml_sem.simps(6)[simp del]

lemma fml_sem_Diamond [simp]: "fml_sem I (\<langle>\<alpha>\<rangle>\<phi>) = {\<nu>. \<exists>\<tau> \<omega>. (\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha> \<and> \<omega> @@ \<tau> \<in> fml_sem I \<phi>}"
  unfolding Diamond_def by simp

lemma fml_sem_AcDia [simp]: "fml_sem I (AcDia \<alpha> A C \<psi>) = { \<nu>. \<exists>\<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha>
        \<and> (strict_assm_set \<nu> \<tau> \<subseteq> fml_sem I A \<and> \<nu> @@ \<tau> \<in> fml_sem I C
            \<or> \<omega> \<noteq> NonFin \<and> assm_set \<nu> \<tau> \<subseteq> fml_sem I A \<and> (gets \<omega>) @@ \<tau> \<in> fml_sem I \<psi>)}"
  unfolding AcDia_def by simp


lemma fml_sem_AcDia_commitI: "\<exists>\<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<and> (strict_assm_set \<nu> \<tau> \<subseteq> fml_sem I A \<and> \<nu> @@ \<tau> \<in> fml_sem I C) \<Longrightarrow> \<nu> \<in> fml_sem I (AcDia \<alpha> A C \<psi>)"
  by auto

lemma TT_valid [simp]: "valid TT"
  unfolding valid_def by simp

lemma chp_sem_test_TT: "chp_sem I (? TT) = I\<^sub>\<D>"
  using fml_sem_TT by auto



paragraph \<open>Semantic equivalence of formulas\<close>

definition fml_equiv:: "fml => fml => bool"
  where "fml_equiv \<phi> \<psi> \<equiv> (\<forall>I. fml_sem I \<phi> = fml_sem I \<psi>)"

text \<open>Substitutionality for Equivalent Formulas\<close>

lemma fml_equiv_subst: "fml_equiv \<phi> \<psi> \<Longrightarrow> P (fml_sem I \<phi>) \<Longrightarrow> P (fml_sem I \<psi>)"
proof-
  assume a1: "fml_equiv \<phi> \<psi>"
  assume a2: "P (fml_sem I \<phi>)"
  from a1 have "fml_sem I \<phi> = fml_sem I \<psi>" using fml_equiv_def by blast
  thus ?thesis using forw_subst a2 by simp
qed
  
lemma valid_fml_equiv: "valid (\<phi> \<leftrightarrow> \<psi>) = fml_equiv \<phi> \<psi>"
  unfolding valid_def Equiv_def Or_def fml_equiv_def by auto

lemma valid_in_equiv: "valid_in I (\<phi> \<leftrightarrow> \<psi>) = ((fml_sem I \<phi>) = (fml_sem I \<psi>))"
  using Equiv_def unfolding valid_in_def by auto

lemma valid_in_impl: "valid_in I (\<phi> \<rightarrow> \<psi>) = ((fml_sem I \<phi>) \<subseteq> (fml_sem I \<psi>))"
  unfolding valid_in_def Implies_def Or_def by auto

lemma valid_equiv: "valid (\<phi> \<leftrightarrow> \<psi>) = (\<forall>I. fml_sem I \<phi> = fml_sem I \<psi>)"
  using valid_fml_equiv fml_equiv_def by auto

lemma valid_impl: "valid (\<phi> \<rightarrow> \<psi>) = (\<forall>I. (fml_sem I \<phi>) \<subseteq> (fml_sem I \<psi>))"
  unfolding valid_def Implies_def Or_def by auto

lemma equiv_refl_valid [simp]: "valid (\<phi> \<leftrightarrow> \<phi>)"
  unfolding valid_def Equiv_def Or_def by simp

lemma Tequal_refl_valid [simp]: "valid (\<theta> =\<^sub>T \<theta>)"
  unfolding valid_def TEquals_def Or_def by simp



paragraph \<open>Properties of the program semantics\<close>

lemma chp_sem_total_and_pc [simp]: "total (chp_sem I \<alpha>) \<and> pc (chp_sem I \<alpha>)"
proof (induction \<alpha> rule: chp_induct)
  case (Chp a Z)                   
  thus ?case using Chps_correct by (simp add: bound_effect_def is_denotation_def)
next                      
  case (Assign x \<theta>)
  show ?case by (rule nocom_leastComp_is_total_and_pc, auto)
next
  case (Nondet x)
  show ?case by (rule nocom_leastComp_is_total_and_pc, auto)
next
  case (Test \<phi>)
  thus ?case by (rule nocom_leastComp_is_total_and_pc, auto)
next
  case (Evolution ode \<phi>)
  show ?case by (rule nocom_leastComp_is_total_and_pc, auto)
next
  case (Choice \<alpha> \<beta>)
  have "total (chp_sem I (\<alpha> \<union>\<union> \<beta>))" by (metis Choice.IH(2) Un_iff chp_sem.simps(6) total.simps)
  moreover have "pc (chp_sem I (\<alpha> \<union>\<union> \<beta>))"
    apply (rule pc.intros) by (metis (no_types, lifting) Choice.IH(1) Choice.IH(2) Un_iff chp_sem.simps(6) pc.cases)
  ultimately show ?case by simp
next
  case (Compose \<alpha> \<beta>)
  show ?case using Compose.IH(1) Compose.IH(2) compose_total compose_pc by auto
next
  case (Loop \<alpha>)
  thus ?case by (simp add: rtcl_linhis_total rtcl_linhis_pc)
next
  case (Send ch h \<theta>)
  thus ?case
  proof
    have "\<And>\<nu>. (\<nu>, [], NonFin) \<in> chp_sem I (Send ch h \<theta>)" using obspref_least by auto
    thus "total (chp_sem I (Send ch h \<theta>))" by (meson total.intros)
  next
    show "pc (chp_sem I (Send ch h \<theta>))"  
    proof
      fix \<nu> \<tau> \<omega> \<tau>' \<omega>'
      assume "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I (Send ch h \<theta>)"
      moreover assume "(\<tau>', \<omega>') \<sqsubseteq> (\<tau>, \<omega>)"
      ultimately show "(\<nu>, \<tau>', \<omega>') \<in> chp_sem I (Send ch h \<theta>)" using obspref_trans by auto
    qed
  qed  
next
  case (Receive ch h x)
  thus ?case
  proof
    have "\<And>\<nu>. (\<nu>, [], NonFin) \<in> chp_sem I (Receive ch h x)" using obspref_least by auto
    thus "total (chp_sem I (Receive ch h x))" by simp
  next
    show "pc (chp_sem I (Receive ch h x))"
    proof
      fix \<nu> \<tau> \<omega> \<tau>' \<omega>'
      assume "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I (Receive ch h x)"
      moreover assume "(\<tau>', \<omega>') \<sqsubseteq> (\<tau>, \<omega>)"
      ultimately show "(\<nu>, \<tau>', \<omega>') \<in> chp_sem I (Receive ch h x)" using obspref_trans by fastforce
    qed
  qed
next
  case (Par \<alpha> \<beta>)
  show ?case
  proof   
    have "\<And>\<nu>. (\<nu>, [], NonFin) \<in> chp_sem I \<alpha> \<and> (\<nu>, [], NonFin) \<in> chp_sem I \<beta>" 
       by (meson Par.IH obspref_least pc.cases total.cases)
    hence "\<And>\<nu>. (\<nu>, [], NonFin) \<in> chp_sem I (\<alpha> par \<beta>)" by fastforce
    thus  "total (chp_sem I (\<alpha> par \<beta>))" by (meson total.intros)
  next
    show "pc (chp_sem I (\<alpha> par \<beta>))"
    proof
      fix \<nu> \<tau> \<omega> \<tau>' \<omega>'
      assume base: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I (\<alpha> par \<beta>)"
      assume pref: "(\<tau>', \<omega>') \<sqsubseteq> (\<tau>, \<omega>)"
      show "(\<nu>, \<tau>', \<omega>') \<in> chp_sem I (\<alpha> par \<beta>)"
      proof (cases "\<omega>' = NonFin")
        case True
        from base obtain \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> where 
          alpha: "(\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha>), \<omega>\<^sub>\<alpha>) \<in> chp_sem I \<alpha>" and
          beta: "(\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<beta>), \<omega>\<^sub>\<beta>) \<in> chp_sem I \<beta>" and
          nojunk: "\<tau> \<down> ((CN (\<pi>\<^sub>I I) \<alpha>) \<union> (CN (\<pi>\<^sub>I I) \<beta>)) = \<tau>" by fastforce

          have "(\<tau>' \<down> (CN (\<pi>\<^sub>I I) \<alpha>), NonFin) \<sqsubseteq> (\<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha>), \<omega>\<^sub>\<alpha>)"
            by (metis obspref_alt obspref_proj_cong pref prefix_order.le_less)
          hence alpha: "(\<nu>, \<tau>' \<down> (CN (\<pi>\<^sub>I I) \<alpha>), NonFin) \<in> chp_sem I \<alpha>" by (meson Par.IH(1) alpha pc.cases)
          have "(\<tau>' \<down> (CN (\<pi>\<^sub>I I) \<beta>), NonFin) \<sqsubseteq> (\<tau> \<down> (CN (\<pi>\<^sub>I I) \<beta>), \<omega>\<^sub>\<beta>)"
            by (metis obspref_alt obspref_proj_cong pref prefix_order.le_less)
          hence beta: "(\<nu>, \<tau>' \<down> (CN (\<pi>\<^sub>I I) \<beta>), NonFin) \<in> chp_sem I \<beta>"
            by (meson Par.IH(2) beta pc.cases)

          have "\<tau>' \<down> ((CN (\<pi>\<^sub>I I) \<alpha>) \<union> (CN (\<pi>\<^sub>I I) \<beta>)) = \<tau>'" 
            using nojunk junkfree_prefix_junkfree by (metis obspref_alt pref)
          moreover have "\<omega>' = NonFin" using True by simp
          ultimately show "(\<nu>, \<tau>', \<omega>') \<in> chp_sem I (\<alpha> par \<beta>)" using alpha beta by fastforce
      next
        case False
        thus ?thesis using pref obspref_alt base by metis
      qed
    qed
  qed
qed

corollary chp_sem_least_computations [simp]: "(\<nu>, [], NonFin) \<in> chp_sem I \<alpha>"
  by (meson chp_sem_total_and_pc obspref_least pc.cases total.cases)

lemma lower_run: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> (\<nu>, \<tau>, NonFin) \<in> chp_sem I \<alpha>"
  using pc.simps by fastforce

lemma chp_sem_Repeat: "chp_sem I (Repeat \<alpha> n) = iterate_linhis n (chp_sem I \<alpha>)"
  apply (induction n)
  by auto


lemma chp_sem_Loop_by_iterate: "chp_sem I \<alpha>** = (\<Union>n. iterate_linhis n (chp_sem I \<alpha>))"
  by (simp add: linhis_rtcl_eq_iteration)

lemma chp_sem_Loop_by_Repeat: "chp_sem I \<alpha>** = (\<Union>n. chp_sem I (Repeat \<alpha> n))"
  using chp_sem_Loop_by_iterate chp_sem_Repeat by presburger

lemma chps_do_not_bind_tvars: "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> Vagree \<nu> \<omega> (\<iota>\<^sub>T \<V>\<^sub>T)"
proof (induction arbitrary: \<nu> \<tau> \<omega> rule: chp_induct)
 case (Chp a Z Y)
  hence 0: "DiffD (chp_sem I (Chp a Z Y)) \<subseteq> -(\<iota>\<^sub>T \<V>\<^sub>T)" using Chps_correct(1) is_denotation_def by simp
  show ?case
  unfolding Vagree_def proof (rule, rule)
    fix z
    assume "z \<in> \<iota>\<^sub>T \<V>\<^sub>T"
    hence "z \<notin> DiffD (chp_sem I (Chp a Z Y))" using 0 by blast
    thus "\<nu> $$ z = \<omega> $$ z" using Chp unfolding DiffD_def by auto
  qed
next
  case (Assign x \<theta>)
  thus ?case by (simp add: Vagree_def)
next
  case (Nondet x)
  thus ?case by (auto simp add: Vagree_def)
next
  case (Evolution x \<theta> \<phi>)  
  then obtain F T where sol: "Vagree \<nu> (F(0)) (-{Rv (DVarName x)}) \<and> F(T) = \<omega> \<and> solves_ODE I F x \<theta>" by auto
  hence "Vagree (F(0)) (F(T)) (-(bvrident x))" unfolding solves_ODE_def by auto
  hence "Vagree (F(0)) (F(T)) (\<iota>\<^sub>T \<V>\<^sub>T)" apply (rule Vagree_antimon) by auto
  moreover have "Vagree \<nu> (F(0)) (\<iota>\<^sub>T \<V>\<^sub>T)" using sol by auto
  moreover have "Vagree (F(T)) \<omega> (\<iota>\<^sub>T \<V>\<^sub>T)" using sol by blast
  ultimately show ?case using Vagree_only_trans by blast
next
  case (Test \<phi>)
  thus ?case by simp
next
  case (Choice \<alpha> \<beta>)
  thus ?case by auto
next
  case (Compose \<alpha> \<beta>)
  then obtain \<tau>\<^sub>1 \<kappa> \<tau>\<^sub>2 where "(\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> chp_sem I \<alpha> \<and> (\<kappa>, \<tau>\<^sub>2, Fin \<omega>) \<in> chp_sem I \<beta>" by auto
  thus ?case using Compose Vagree_def by fastforce
next
  case (Loop \<alpha>)
  then obtain n where "(\<nu>, \<tau>, Fin \<omega>) \<in> iterate_linhis n (chp_sem I \<alpha>)" unfolding chp_sem.simps linhis_rtcl_eq_iteration by blast
  thus ?case
  proof (induction n arbitrary: \<nu> \<tau> \<omega>)
    case 0
    thus ?case unfolding iterate_linhis.simps by fastforce
  next
    case (Suc n)
    then obtain \<tau>\<^sub>1 \<kappa> \<tau>\<^sub>2 where "(\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> chp_sem I \<alpha> \<and> (\<kappa>, \<tau>\<^sub>2, Fin \<omega>) \<in> iterate_linhis n (chp_sem I \<alpha>)" unfolding iterate_linhis.simps botop.simps continue.simps by blast
    hence "Vagree \<nu> \<kappa> (\<iota>\<^sub>T \<V>\<^sub>T) \<and> Vagree \<kappa> \<omega> (\<iota>\<^sub>T \<V>\<^sub>T)" using Loop.IH Suc.IH by blast
    thus ?case using Vagree_trans inf_idem by metis
  qed
next
  case (Send ch h \<theta>)
  hence "Fin \<omega> = Fin \<nu>" by (simp add: obspref_alt)
  thus ?case using Vagree_refl by blast
next
  case (Receive ch h x)
  hence "\<exists>r. (\<tau>, Fin \<omega>) \<sqsubseteq> ([mkrecevent h ch r (rval (\<nu> $$ (Rv \<mu>)))], Fin (rrepv \<nu> x r))" by auto
  hence "\<exists>r. Fin \<omega> = Fin (rrepv \<nu> x r)" using obspref_alt by (metis reachedstate.distinct(1))
  thus ?case using Vagree_def by force
next
  case (Par \<alpha> \<beta>)
  then obtain \<tau>\<^sub>1 \<omega>\<^sub>\<alpha> \<tau>\<^sub>2 \<omega>\<^sub>\<beta> where 0: "(\<nu>, \<tau>\<^sub>1, \<omega>\<^sub>\<alpha>) \<in> chp_sem I \<alpha> \<and> (\<nu>, \<tau>\<^sub>2, \<omega>\<^sub>\<beta>) \<in> chp_sem I \<beta> 
    \<and> (Fin \<omega> = lmergebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> (BVP_pre (\<pi>\<^sub>I I) \<alpha>))"  by auto
  then obtain \<omega>\<^sub>1 \<omega>\<^sub>2 where fin: "\<omega>\<^sub>\<alpha> = Fin \<omega>\<^sub>1" "\<omega>\<^sub>\<beta> = Fin \<omega>\<^sub>2" using lmergebot_Exists_Fin by blast
  hence "\<omega> = lmerge \<omega>\<^sub>1 \<omega>\<^sub>2 (BVP_pre (\<pi>\<^sub>I I) \<alpha>)" using 0 by simp
  moreover have "Vagree \<nu> \<omega>\<^sub>1 (\<iota>\<^sub>T \<V>\<^sub>T) \<and> Vagree \<nu> \<omega>\<^sub>2 (\<iota>\<^sub>T \<V>\<^sub>T)" using 0 Par.IH lmergebot_fin fin by blast
  ultimately have "Vagree \<nu> \<omega> (\<iota>\<^sub>T \<V>\<^sub>T)" using lmerge_bound_vars by fastforce 
  thus ?case by force
qed


paragraph \<open>Some Simple Obvious Observations about formulas\<close>

lemma ac_box_commit: "\<nu> \<in> fml_sem I (AcBox \<alpha> A C \<psi>) 
  \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> strict_assm_set \<nu> \<tau> \<subseteq> fml_sem I A \<Longrightarrow> \<nu> @@ \<tau> \<in> fml_sem I C"
  using reachedstate.sel by fastforce

lemma ac_box_post: "\<nu> \<in> fml_sem I (AcBox \<alpha> A C \<psi>) 
  \<Longrightarrow> (\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> assm_set \<nu> \<tau> \<subseteq> fml_sem I A \<Longrightarrow> \<omega> @@ \<tau> \<in> fml_sem I \<psi>"
  using reachedstate.sel by fastforce


lemma ac_box_commits_initial: "fml_sem I (AcBox \<alpha> A C \<psi>) \<subseteq> fml_sem I C"
proof -
  have "\<And>\<nu>. \<nu> \<in> fml_sem I (AcBox \<alpha> A C \<psi>) \<Longrightarrow> ((\<nu>, [], NonFin) \<in> chp_sem I \<alpha> \<Longrightarrow> \<nu> @@ [] \<in> fml_sem I C)"
    using fml_sem.simps(8) strict_assm_nocom_empty by blast
  thus ?thesis by auto
qed

lemma nocom_box: 
  assumes "\<nu> \<in> fml_sem I (Box \<alpha> \<phi>)"
  shows "(\<And>\<omega>. (\<nu>, [], Fin \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> \<omega> \<in> fml_sem I \<phi>)"
proof -
  fix \<omega>
  assume "(\<nu>, [], Fin \<omega>) \<in> chp_sem I \<alpha>"
  hence "\<omega> @@ [] \<in> fml_sem I \<phi>" using assms using fml_sem.simps(7) by blast
  thus "\<omega> \<in> fml_sem I \<phi>" by force
qed

lemma ac_box_impl_weaken: "fml_sem I (AcBox \<alpha> A C \<psi>) \<subseteq> fml_sem I (AcBox \<alpha> A C (\<phi> \<rightarrow> \<psi>))"
  by auto



paragraph \<open>Rules for proving axioms\<close>

lemma fml_sem_implI: "(\<nu> \<in> fml_sem I \<phi> \<Longrightarrow> \<nu> \<in> fml_sem I \<psi>) \<Longrightarrow> \<nu> \<in> fml_sem I (\<phi> \<rightarrow> \<psi>)"
  unfolding Implies_def by auto 

lemma fml_sem_andI: "\<nu> \<in> fml_sem I \<phi> \<Longrightarrow> \<nu> \<in> fml_sem I \<psi> \<Longrightarrow> \<nu> \<in> fml_sem I (\<phi> && \<psi>)" 
  by auto

lemma valid_equivI:
  assumes "\<And>I \<nu>. \<nu> \<in> fml_sem I \<phi> \<Longrightarrow> \<nu> \<in> fml_sem I \<psi>"
      and "\<And>I \<nu>. \<nu> \<in> fml_sem I \<psi> \<Longrightarrow> \<nu> \<in> fml_sem I \<phi>"
    shows "valid (\<phi> \<leftrightarrow> \<psi>)"
using valid_equiv by (simp add: assms subsetI subset_antisym valid_def)

lemma box_by_runsI:
  assumes "\<And>\<tau> \<omega>. (\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> \<omega> @@ \<tau> \<in> fml_sem I \<psi>"
  shows "\<nu> \<in> fml_sem I (Box \<alpha> \<psi>)"
  using assms by simp


lemma ac_box_by_runsI:
  assumes "\<And>\<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> (strict_assm_set \<nu> \<tau> \<subseteq> fml_sem I A \<longrightarrow> \<nu> @@ \<tau> \<in> fml_sem I C)
            \<and> (\<omega> \<noteq> NonFin \<and> assm_set \<nu> \<tau> \<subseteq> fml_sem I A \<longrightarrow> (gets \<omega>) @@ \<tau> \<in> fml_sem I \<psi>)"
  shows "\<nu> \<in> fml_sem I (AcBox \<alpha> A C \<psi>)"
  using assms by auto

lemma ac_box_by_ac_casesI:
  assumes "\<And>\<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> (strict_assm_set \<nu> \<tau> \<subseteq> fml_sem I A \<Longrightarrow> \<nu> @@ \<tau> \<in> fml_sem I C)"
      and "\<And>\<tau> \<omega>. (\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> (assm_set \<nu> \<tau> \<subseteq> fml_sem I A \<Longrightarrow> \<omega> @@ \<tau> \<in> fml_sem I \<psi>)"
    shows "\<nu> \<in> fml_sem I (AcBox \<alpha> A C \<psi>)"
  by (simp add: assms(1) assms(2))

lemma ac_box_refinement: "chp_sem I \<beta> \<subseteq> chp_sem I \<alpha> \<Longrightarrow> fml_sem I (AcBox \<alpha> A C \<psi>) \<subseteq> fml_sem I (AcBox \<beta> A C \<psi>)"
  by auto



subsection \<open>Properties of Closing Sets of Binders\<close>

definition bclose0 :: "bindr \<Rightarrow> bindr set" 
  where "bclose0 = bclose"

definition bclosure :: "bindr set \<Rightarrow> bindr set"
  where "bclosure Z = (\<Union> { bclose b | b. b \<in> Z })"

definition bclosed :: "bindr set \<Rightarrow> bool"
  where "bclosed Z = ((\<forall>h ch. Bc h ch \<in> Z \<longrightarrow> Bv (Tv h) \<in> Z)
    \<and> (\<forall>h. Bv (Tv h) \<in> Z \<longrightarrow> (\<exists>ch. Bc h ch \<in> Z)))"

lemma bclosed_bclose_Bv: "bclosed (bclose (Bv z))"
  unfolding bclosed_def apply (cases z) by simp_all

lemma bclosed_bclose: "bclosed (bclose b)"
  apply (cases b)
  using bclosed_bclose_Bv bclosed_def by simp_all

lemma bclosed_unionI: "\<forall>X \<in> Z. bclosed X \<Longrightarrow> bclosed (\<Union> Z)"
  unfolding bclosed_def apply simp by metis
  

lemma bclosed_bclosure: "bclosed (bclosure Z)"
  apply (simp add: bclosure_def)
  apply (rule bclosed_unionI)
  using bclosed_bclose by auto



lemma pi_vars_diff_dist: "\<pi>\<^sub>V (Z - U) = \<pi>\<^sub>V Z - \<pi>\<^sub>V U" by (auto simp add: pi_vars_def)
lemma pi_comtar_diff_dist: "\<pi>\<^sub>C (Z - U) = \<pi>\<^sub>C Z - \<pi>\<^sub>C U" by (auto simp add: pi_comtar_def)


lemma bclosed_not_rec_no_comtar: "bclosed U \<Longrightarrow> Tv h \<notin> \<pi>\<^sub>V U \<Longrightarrow> \<pi>\<^sub>C U `` {h} = {}"
  by (auto simp add: bclosed_def pi_vars_def pi_comtar_def)

lemma bclosed_comtar_non_empty_rec: "bclosed U \<Longrightarrow> \<pi>\<^sub>C U `` {h} \<noteq> {} \<Longrightarrow> Tv h \<in> \<pi>\<^sub>V U"
  using bclosed_not_rec_no_comtar by auto


lemma VCagree_bclosed_tvars: "bclosed U \<Longrightarrow>
    Vagree (sfilter \<nu> (\<pi>\<^sub>C U)) (sfilter \<omega> (\<pi>\<^sub>C U)) (\<pi>\<^sub>V U) \<Longrightarrow>
    Vagree (sfilter \<nu> (\<pi>\<^sub>C U)) (sfilter \<omega> (\<pi>\<^sub>C U)) (\<iota>\<^sub>T \<V>\<^sub>T - \<pi>\<^sub>V U)"
  using bclosed_not_rec_no_comtar by (auto simp add: Vagree_def sfilter_def tsfilter_def iota_tvars_def)


lemma VCagree_bclosed: "bclosed U \<Longrightarrow> VCagree \<nu> \<omega> U = VCagree \<nu> \<omega> (U \<union> \<iota>\<^sub>V (\<iota>\<^sub>T \<V>\<^sub>T))"
  unfolding VCagree_def apply rule
  apply simp_all
  using VCagree_bclosed_tvars by (metis Un_Diff_cancel Vagree_union)

lemma bclosure_dist_union [simp]: "bclosure (Z \<union> U) = bclosure Z \<union> bclosure U"
  by (auto simp add: bclosure_def)

lemma bclosure_rvars [simp]: "bclosure (\<iota>\<^sub>V (\<iota>\<^sub>R X)) = \<iota>\<^sub>V (\<iota>\<^sub>R X)" 
  by (fastforce simp add: bclosure_def iota_vars_def iota_rvars_def)


lemma pi_rvars_bclosure_comtars_empty: "\<pi>\<^sub>R (\<pi>\<^sub>V (bclosure (\<iota>\<^sub>C Y))) = {}"
  by (auto simp add: bclosure_def pi_rvars_def iota_comtar_def)

lemma pi_comtar_bclosure_non_empty_conv: "Y `` {z} \<noteq> {} \<Longrightarrow> \<pi>\<^sub>C (bclosure (\<iota>\<^sub>C Y)) `` {z} \<noteq> {}"
  by (fastforce simp add: bclosure_def pi_comtar_def iota_comtar_def)

lemma bclosure_inflates_comtars: "Y \<subseteq> \<pi>\<^sub>C (bclosure (\<iota>\<^sub>C Y))"
  by (fastforce simp add: bclosure_def pi_comtar_def iota_comtar_def)

lemma bclosure_fp_for_pure_binders: "U = \<iota>\<^sub>V (\<iota>\<^sub>R X) \<union> \<iota>\<^sub>C Y \<Longrightarrow> \<pi>\<^sub>C (bclosure (\<iota>\<^sub>C Y)) = Y"
  by (fastforce simp add: iota_comtar_def pi_comtar_def bclosure_def)

lemma "U = \<iota>\<^sub>V (\<iota>\<^sub>R X) \<union> \<iota>\<^sub>C Y \<Longrightarrow> VCagree \<nu> \<omega> (U \<union> \<iota>\<^sub>V (\<iota>\<^sub>T \<V>\<^sub>T)) = VCagree \<nu> \<omega> (bclosure U)"
  apply rule
  apply (auto simp add: VCagree_def Vagree_eqon pi_rvars_bclosure_comtars_empty eqon_def)
  using bclosure_fp_for_pure_binders apply simp
  by (metis bclosed_bclosure bclosed_comtar_non_empty_rec bclosure_fp_for_pure_binders tfilter_nochans tsfilter_access)



subsection \<open>Lemmas\<close>


lemma DiffD_reach_stT [simp]: "DiffD D \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> D \<Longrightarrow> stT (\<omega> \<squnion> \<nu>) = stT \<nu>"
  apply (cases \<omega>)
   apply (simp_all add: DiffD_def iota_rvars_def) by force

lemma rrepv_sfilter: "rrepv (sfilter \<nu> Y) x d = sfilter (rrepv \<nu> x d) Y"
  by (simp add: rrepv_def sfilter_def)

lemma stR_lmerge_access [simp, intro]:
  "Rv x \<in> X \<Longrightarrow> stR (lmerge \<nu> \<omega> X) x = stR \<nu> x" 
  by (simp add: lmerge_def) 
 
lemma stT_lmerge_access [simp, intro]:
  "Tv x \<in> X \<Longrightarrow> stT (lmerge \<nu> \<omega> X) x = stT \<nu> x" 
  by (simp add: lmerge_def) 

lemma Vagree_upds2: "Vagree \<nu> \<nu>' (X - {z}) \<Longrightarrow> sorteq z d \<Longrightarrow> Vagree (upds \<nu> z d) (upds \<nu>' z d) X"
  by (simp add: Vagree_def)

lemma Vagree_sfilter_cong0: "sorteq z d \<Longrightarrow> Vagree (upds (sfilter \<nu> Y) z d) (upds (sfilter \<nu>' Y) z d) X \<Longrightarrow> Vagree (sfilter (upds \<nu> z d) Y) (sfilter (upds \<nu>' z d) Y) X"
  apply (rule Vagree_by_sortI; cases z)
     apply (auto simp add: Vagree_def sorteq_def eqon_def tsfilter_def)
  by (auto simp add: Vagree_def sorteq_def eqon_def tsfilter_def)

lemma sfilter_state_to_upds:
  "Vagree (sfilter \<nu> Y) (sfilter \<nu>' Y) (X - {z}) \<Longrightarrow> sorteq z d \<Longrightarrow> Vagree (sfilter (upds \<nu> z d) Y) (sfilter (upds \<nu>' z d) Y) X"
  using Vagree_upds2 Vagree_sfilter_cong0 by blast

 

end