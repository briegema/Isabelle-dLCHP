theory "Axioms" 
imports
  "Syntax"
  "Denotational_Semantics"
  "Least_Static_Semantics"
  "Ids"
begin

section \<open>Axioms and Axiomatic Proof Rules of dLCHP\<close>

subsection \<open>Axioms\<close>

text \<open>The axioms of dLCHP's uniform substitution calculus are concrete formulas of dLCHP build from
function, predicate, and program symbols instead of being axiom schemata representing infinitely 
many axioms. Instances of the axioms can be obtained using uniform substitution to replace the 
symbols with concrete objects.\<close>

paragraph \<open>Definition of Symbols\<close>

text \<open>This paragraph defines symbols as abbreviations that are used for several axioms\<close>

abbreviation Y\<^sub>1 where "Y\<^sub>1 \<equiv> CConst chset1"
abbreviation Y\<^sub>2 where "Y\<^sub>2 \<equiv> CConst chset2"
abbreviation Y\<^sub>3 where "Y\<^sub>3 \<equiv> CConst chset3"

abbreviation X\<^sub>1 where "X\<^sub>1 \<equiv> VRConst xvar1"
abbreviation X\<^sub>2 where "X\<^sub>2 \<equiv> VRConst xvar2"
abbreviation X\<^sub>3 where "X\<^sub>3 \<equiv> VRConst zvar3" 

(* Space {(rec, Y)} \<union> X of real variables X and communication interface (rec, Y) *)
abbreviation recX\<^sub>1 where "recX\<^sub>1 \<equiv> (VTVar rec) \<union>\<^sub>V X\<^sub>1"
abbreviation recX\<^sub>2 where "recX\<^sub>2 \<equiv> (VTVar rec) \<union>\<^sub>V X\<^sub>2"

(* Program constant a\<lparr>{(rec, Y)} \<union> X\<rparr> with communication interface (rec, Y) and state variables X *)
abbreviation chp1 where "chp1 \<equiv> Chp chpid1 recX\<^sub>1 Y\<^sub>1" (* a\<lparr>Y\<^sub>1, {rec} \<union> X\<^sub>1\<rparr> *)
abbreviation chp2 where "chp2 \<equiv> Chp chpid2 recX\<^sub>2 Y\<^sub>2" (* b\<lparr>Y\<^sub>2, {rec} \<union> X\<^sub>2\<rparr> *)


(* Program constant a\<lparr> X \<rparr> without communication interface but with state variables X *)
definition chp_nocom where "chp_nocom \<equiv> Chp chpid1 X\<^sub>1 \<bottom>\<^sub>\<Omega>"

lemma wf_chp1: "wf_chp \<L> chp1" by simp
lemma wf_chp2: "wf_chp \<L> chp2" by simp
lemma wf_chp_nocom: "wf_chp \<L> chp_nocom" by (simp add: chp_nocom_def)

(* Predicate symbol p(X)(rec) depending on real variables X and the trace variable rec *)
abbreviation p1 where "p1 \<equiv> Psymb pid1 X\<^sub>3 [TArg (TVar rec)]"
abbreviation p2 where "p2 \<equiv> Psymb pid2 X\<^sub>3 [TArg (TVar rec)]"


(* Predicate symbol p(rec) depending on the trace variable rec *)
abbreviation Aof where "Aof te \<equiv> Psymb pid_A \<bottom>\<^sub>V [TArg te]"
abbreviation Cof where "Cof te \<equiv> Psymb pid_C \<bottom>\<^sub>V [TArg te]"
abbreviation A where "A \<equiv> Aof (TVar rec)"
abbreviation C where "C \<equiv> Cof (TVar rec)"
abbreviation B where "B \<equiv> Psymb pid_B \<bottom>\<^sub>V [TArg (TVar rec)]"
abbreviation C2 where "C2 \<equiv> Psymb pid_C2 \<bottom>\<^sub>V [TArg (TVar rec)]"

(* Predicate symbol p(x) depending on the real variable x *)
abbreviation Pof where "Pof x \<equiv> Psymb pid1 \<bottom>\<^sub>V [RArg x]"

abbreviation Pofh where "Pofh h \<equiv> Psymb pid1 \<bottom>\<^sub>V [TArg (TVar h)]"

abbreviation Pofhx where "Pofhx h x \<equiv> Psymb pid1 \<bottom>\<^sub>V [TArg (TVar h), RArg (RVar x)]"


abbreviation Poff where "Poff te \<equiv> Psymb pid1 X\<^sub>3 [TArg te]"

(* Predicate symbol p() of no arguments at all *)
abbreviation p where "p \<equiv> Psymb pid1 \<bottom>\<^sub>V []"
abbreviation q where "q \<equiv> Psymb pid2 \<bottom>\<^sub>V []"
                                     
abbreviation const where "const \<equiv> QRFunc fid1 []"



abbreviation xhconv where "xhconv \<equiv> (X\<^sub>1 \<inter>\<^sub>V (-\<^sub>V (VRVar vvar))) \<union>\<^sub>V (VTVar rec)"
abbreviation chpconv where "chpconv \<equiv> Chp chpid1 xhconv Y\<^sub>1"
abbreviation PhxOf where "PhxOf x \<equiv> Psymb pid1 (X\<^sub>3 \<inter>\<^sub>V (-\<^sub>V (VRVar vvar))) [RArg x, TArg (TVar rec)]"


lemma wf_chpconv: "wf_chp \<L> chpconv" by simp

(* Abbreviation for the convergence axioms *)
abbreviation aconv_exists :: "fml"
  where "aconv_exists \<equiv> Exists (Rv vvar) ((Geq (Number 0) (RVar vvar)) && (PhxOf (RVar vvar)))"

lemma xid1_neq_gtime [intro]: "xid1 \<noteq> \<mu>" by (simp add: gtime_def)


paragraph \<open>Modal Logic Principles\<close>

text \<open>Fundamental laws of modal logic such as the duality between boxes and diamonds and modal modus
ponens generalized to ac-modalities in dLCHP.\<close>

named_theorems axiom_defs "Axiom definitions"

definition diamond_axiom :: "fml"
  where [axiom_defs]:
"diamond_axiom \<equiv> (Diamond chp1 p1) \<leftrightarrow> Not(Box chp1 (Not p1))" 

definition ac_diamond_axiom :: "fml"
  where [axiom_defs]:
"ac_diamond_axiom \<equiv> (AcDia chp1 A C p1) \<leftrightarrow> Not(AcBox chp1 A (Not C) (Not p1))" 

definition boxes_dual_axiom
  where [axiom_defs]:
"boxes_dual_axiom \<equiv> (Box chp1 p1) \<leftrightarrow> (AcBox chp1 TT TT p1)"

definition ac_modal_mp_axiom :: "fml"
  where [axiom_defs]:
"ac_modal_mp_axiom \<equiv> AcBox chp1 A (C \<rightarrow> C2) (p1 \<rightarrow> p2) \<rightarrow> (AcBox chp1 A C p1 \<rightarrow> AcBox chp1 A C2 p2)"

definition assumption_weakening_axiom :: "fml"
  where [axiom_defs]:
"assumption_weakening_axiom \<equiv> (AcBox chp1 TT ((C && B) \<rightarrow> A) TT && AcBox chp1 A C p1) \<rightarrow> AcBox chp1 B C p1"



paragraph \<open>Axioms for Atomic Programs\<close>

(* this axiom is not required for completeness *)
definition stutterd_axiom :: "fml"
  where [axiom_defs]:
"stutterd_axiom \<equiv> (Box (xid1 := (RVar xid1)) (Pof (RVar xid1))) \<leftrightarrow> Pof (RVar xid1)"

definition assign_axiom :: "fml"
  where [axiom_defs]:
"assign_axiom \<equiv> (Box (xid1 := const) (Pof (RVar xid1))) \<leftrightarrow> (Pof const)"

definition assigneq_axiom :: "fml"
  where [axiom_defs]:
"assigneq_axiom \<equiv> Box (xid1 := const) (Psymb pid1 \<top>\<^sub>V []) \<leftrightarrow> Forall (Rv xid1) (REquals (RVar xid1) const \<rightarrow> (Psymb pid1 \<top>\<^sub>V []))"

definition test_axiom :: "fml"
  where [axiom_defs]:
"test_axiom \<equiv> Box (? q) p \<leftrightarrow> (q \<rightarrow> p)"

definition send_axiom :: "fml"
  where [axiom_defs]:
"send_axiom \<equiv> Box (Send ch1 rec const) (Pofh rec) \<leftrightarrow> Forall (Tv hid0) ((TEquals (TVar hid0) ((TVar rec) \<circ>\<^sub>T (ComItm ch1 const (RVar \<mu>)))) \<rightarrow> Pofh hid0)"

definition receive_axiom :: "fml"
  where [axiom_defs]:
"receive_axiom \<equiv> Box (Receive ch1 rec xid1) (Pofhx rec xid1) \<leftrightarrow> Box (xid1 := *) (Box (Send ch1 rec (RVar xid1)) (Pofhx rec xid1))"

definition ac_receive_axiom :: "fml"
  where [axiom_defs]:
"ac_receive_axiom \<equiv> AcBox (Receive ch1 rec xid1) A C (Pofhx rec xid1) \<leftrightarrow> Box (Nondet xid1) (AcBox (Send ch1 rec (RVar xid1)) A C (Pofhx rec xid1))"

definition ac_unfolding_axiom :: "fml"
  where [axiom_defs]:
"ac_unfolding_axiom \<equiv> AcBox (Send ch1 rec const) A C (Pofh rec) \<leftrightarrow> AcBox (? TT) A C (Box (Send ch1 rec const) (AcBox (? TT) A C (Pofh rec)))"



paragraph \<open>Axioms for Compound Programs\<close>

(* this axiom is not required for completeness *)
definition ac_weakening_axiom :: "fml"
  where [axiom_defs]:
"ac_weakening_axiom \<equiv> AcBox chp1 A C p1 \<leftrightarrow> (C && AcBox chp1 A C (C && (A \<rightarrow> p1)))"

definition nocom_axiom :: "fml"
  where [axiom_defs]:
"nocom_axiom \<equiv> AcBox chp_nocom A C p1 \<leftrightarrow> (C && (A \<rightarrow> Box chp_nocom p1))"

definition ac_choice_axiom :: "fml"
  where [axiom_defs]:
"ac_choice_axiom \<equiv> AcBox (chp1 \<union>\<union> chp2) A C p1 \<leftrightarrow> (AcBox chp1 A C p1 && AcBox chp2 A C p1)"

definition ac_composition_axiom :: "fml"
  where [axiom_defs]:
"ac_composition_axiom \<equiv> AcBox (chp1 ;; chp2) A C p1 \<leftrightarrow> (AcBox chp1 A C (AcBox chp2 A C p1))"

definition ac_iteration_axiom :: "fml"
  where [axiom_defs]:
"ac_iteration_axiom \<equiv> AcBox (chp1**) A C p1 \<leftrightarrow> (AcBox (? TT) A C p1 && AcBox chp1 A C (AcBox (chp1**) A C p1))"

definition ac_induction_axiom :: "fml"
  where [axiom_defs]:
"ac_induction_axiom \<equiv> AcBox (chp1**) A C p1 \<leftrightarrow> (AcBox (? TT) A C p1 && AcBox (chp1**) A TT (p1 \<rightarrow> AcBox chp1 A C p1))"

(* this axiom is not required for completeness *)
definition convergence_axiom :: fml
  where [axiom_defs]:
"convergence_axiom \<equiv> Box (chpconv**) (Forall (Rv vvar) (((RVar vvar) >\<^sub>R (Number 0) && PhxOf (RVar vvar)) \<rightarrow> \<langle> chpconv \<rangle> (PhxOf (Dec (RVar vvar))))) \<rightarrow> Forall (Rv vvar) (PhxOf (RVar vvar) \<rightarrow> \<langle> chpconv** \<rangle> aconv_exists)"

definition action_convergence_axiom :: "fml"
  where [axiom_defs]:
"action_convergence_axiom \<equiv> (A && AcBox (chpconv**) A TT (Forall (Rv vvar) (((RVar vvar) >\<^sub>R (Number 0) && PhxOf (RVar vvar)) \<rightarrow> AcDia chpconv A FF (PhxOf (Dec (RVar vvar)))))) \<rightarrow> Forall (Rv vvar) (PhxOf (RVar vvar) \<rightarrow> AcDia (chpconv**) A FF aconv_exists)"



paragraph \<open>Axiomatic Properties of the Computational Domain\<close>

definition history_extension_axiom :: "fml"
  where [axiom_defs]:
"history_extension_axiom \<equiv> (TVar hid0) =\<^sub>T (TVar rec) \<rightarrow> AcBox chp1 TT ((TVar hid0) \<preceq>\<^sub>T (TVar rec)) ((TVar hid0) \<preceq>\<^sub>T (TVar rec))"


definition Acl :: "(ttrm \<Rightarrow> ttrm \<Rightarrow> fml) \<Rightarrow> fml"
  (* where "Acl rel Y \<equiv> Forall (Tv hid') (((TVar hid0) \<preceq>\<^sub>T (TVar hid') && rel (TVar hid') (Proj (TVar rec) Y)) \<rightarrow> Aof hid')" *)
  where "Acl rel \<equiv> Forall (Tv hid') (((TVar hid0) \<preceq>\<^sub>T (TVar hid') && rel (TVar hid') (TVar rec)) \<rightarrow> Aof (TVar hid'))"

definition assumption_closure_axiom :: "fml"
  where [axiom_defs]:
(* "assumption_closure_axiom \<equiv> (TVar hid0) =\<^sub>T (Proj (TVar rec) (Y\<^sub>1 \<union>\<^sub>V Y\<^sub>2)) \<rightarrow> AcBox chp1 (Aof rec) (Acl SPref (Y\<^sub>1 \<union>\<^sub>\<Omega> Y\<^sub>2)) (Acl Pref (Y\<^sub>1 \<union> Y\<^sub>2))" *)
"assumption_closure_axiom \<equiv> (TVar hid0) =\<^sub>T (TVar rec) \<rightarrow> AcBox chp1 A (Acl SPref) (Acl Pref)"



paragraph \<open>Parallel Injection Axiom\<close>

abbreviation paralpha where "paralpha \<equiv> Chp chpid1 ((VTVar rec) \<union>\<^sub>V X\<^sub>1) Y\<^sub>1"
abbreviation injectableChans where "injectableChans \<equiv> Y\<^sub>2 \<inter>\<^sub>\<Omega> ((-\<^sub>\<Omega> Y\<^sub>3) \<union>\<^sub>\<Omega> Y\<^sub>1)"
definition gtVars where "gtVars \<equiv> BRvSet [\<mu>, \<mu>p]" (* this is a definition because gtset is a definition as well *)
abbreviation injectableVars where "injectableVars \<equiv> (VTVar rec) \<union>\<^sub>V (-\<^sub>R X\<^sub>3 \<inter>\<^sub>V -\<^sub>R X\<^sub>1) \<union>\<^sub>V gtVars"
abbreviation parbeta where "parbeta \<equiv> Chp chpid2 injectableVars injectableChans"

abbreviation hY where "hY \<equiv> TArg (Proj (TVar rec) (Y\<^sub>3))"

abbreviation parA where "parA \<equiv> Psymb pid_A \<bottom>\<^sub>V [ TArg (Proj (TVar rec) Y\<^sub>3) ]"
abbreviation parC where "parC \<equiv> Psymb pid_C \<bottom>\<^sub>V [ TArg (Proj (TVar rec) Y\<^sub>3) ]"
abbreviation parP where "parP \<equiv> Psymb pid1 X\<^sub>3 [ TArg (Proj (TVar rec) Y\<^sub>3) ]"

definition ac_par_axiom :: "fml" 
  where [axiom_defs]:
"ac_par_axiom \<equiv> AcBox paralpha parA parC parP \<rightarrow> AcBox (paralpha par parbeta) parA parC parP"



paragraph \<open>Liveness of Parallel Programs\<close>

(* \<forall>h=te \<psi> is short for \<forall>h (h = te \<rightarrow> \<psi>) *)
definition Forall_EqT :: "tvar \<Rightarrow> ttrm \<Rightarrow> fml \<Rightarrow> fml"
  where "Forall_EqT h te \<psi> = Forall (Tv h) ( TVar h =\<^sub>T te \<rightarrow> \<psi>)"

(* \<exists>h=te \<psi> is short for \<exists>h (h = te \<and> \<psi>) *)
definition Exists_EqT :: "tvar \<Rightarrow> ttrm \<Rightarrow> fml \<Rightarrow> fml"
  where "Exists_EqT h te \<psi> = Not (Forall_EqT h te (Not \<psi>))"

definition rChp :: "ident \<Rightarrow> cspace \<Rightarrow> vspace \<Rightarrow> chp"
  where "rChp a Y Z = Chp a (((VTVar rec \<union>\<^sub>V gtVars)) \<union>\<^sub>V Z) Y"

(* Assumes existence of an overall communication history his for \<alpha> || \<beta> and stores the initial value of rec in hid0 *)
definition SyncQ :: "fml \<Rightarrow> fml"
  where "SyncQ \<psi> \<equiv> Exists_EqT his (Proj (TVar his) (Y\<^sub>1 \<union>\<^sub>\<Omega> Y\<^sub>2)) (Forall_EqT hid0 (TVar rec) \<psi>)"

(* The sync modalities check whether the communication of \<alpha> matches the overall history his on the channels Y *)
definition SyncDiaC :: "chp \<Rightarrow> cspace \<Rightarrow> fml \<Rightarrow> fml"
  where "SyncDiaC \<alpha> Y \<psi> \<equiv> Forall_EqT rec Empty (AcDia \<alpha> TT (TVar rec =\<^sub>T Proj (TVar his) Y && \<psi>) FF)"

definition SyncDiaP :: "chp \<Rightarrow> cspace \<Rightarrow> fml \<Rightarrow> fml"
  where "SyncDiaP \<alpha> Y \<psi> \<equiv> Forall_EqT rec Empty (Diamond \<alpha> (TVar rec =\<^sub>T Proj (TVar his) Y && \<psi>))"

definition ac_live_parC :: "fml"
  where [axiom_defs]:
"ac_live_parC \<equiv> SyncQ (
     SyncDiaC (rChp chpid1 Y\<^sub>1 X\<^sub>1) Y\<^sub>1 TT 
  && SyncDiaC (rChp chpid2 Y\<^sub>2 (-\<^sub>R X\<^sub>1)) Y\<^sub>2 TT
  && Cof ((TVar hid0) \<circ>\<^sub>T (TVar his)))
  \<rightarrow> (AcDia ((rChp chpid1 Y\<^sub>1 X\<^sub>1) par (rChp chpid2 Y\<^sub>2 (-\<^sub>R X\<^sub>1))) TT (Cof (TVar rec)) FF)"

definition gtime0 :: "rvar" ("\<mu>\<^sub>0") where "gtime0 \<equiv> RVarName (hd ''0'')"
definition gtime0_pace :: "rvar" ("\<mu>\<^sub>0p") where "gtime0_pace \<equiv> DVarName (hd ''0'')"
definition gtime1 :: "rvar" ("\<mu>\<^sub>1") where "gtime1 \<equiv> RVarName (hd ''1'')"
definition gtime1_pace :: "rvar" ("\<mu>\<^sub>1p") where "gtime1_pace \<equiv> DVarName (hd ''1'')"

definition fresh_gtime :: "vspace" ("\<mu>f")
  where "fresh_gtime \<equiv> BRvSet [\<mu>\<^sub>0, \<mu>\<^sub>0p, \<mu>\<^sub>1, \<mu>\<^sub>1p]"

abbreviation live_par_alpha :: "chp"
  where "live_par_alpha \<equiv> rChp chpid1 Y\<^sub>1 (X\<^sub>1 \<inter>\<^sub>V (-\<^sub>V \<mu>f))"

abbreviation live_par_beta :: "chp"
  where "live_par_beta \<equiv> rChp chpid2 Y\<^sub>2 (-\<^sub>R X\<^sub>1 \<inter>\<^sub>V (-\<^sub>V \<mu>f))"

abbreviation LiveParP
  where "LiveParP te \<equiv> Psymb pid1 (X\<^sub>3 \<inter>\<^sub>V (-\<^sub>V \<mu>f)) [TArg te]"

definition ac_live_parP :: "fml"
  where [axiom_defs]:
"ac_live_parP \<equiv> SyncQ 
     (Diamond (\<mu>\<^sub>0 := RVar \<mu> ;; \<mu>\<^sub>0p := RVar \<mu>p)
     (SyncDiaP live_par_alpha Y\<^sub>1 
     (Diamond (\<mu>\<^sub>1 := RVar \<mu> ;; \<mu>\<^sub>1p := RVar \<mu>p ;; \<mu> := RVar \<mu>\<^sub>0 ;; \<mu>p := RVar \<mu>\<^sub>0p)
     (SyncDiaP live_par_beta Y\<^sub>2
     (Diamond (? ((RVar \<mu>) =\<^sub>R (RVar \<mu>\<^sub>1) && (RVar \<mu>p) =\<^sub>R (RVar \<mu>\<^sub>1p)))
   (LiveParP ((TVar hid0) \<circ>\<^sub>T (TVar his))))))))
  \<rightarrow> (Diamond (live_par_alpha par live_par_beta) (LiveParP (TVar rec)))"



paragraph \<open>Properties of the Syntactical Elements\<close>



lemma FVV_VBot [simp]: "FVV J \<bottom>\<^sub>V = {}" by (simp add: FVV_def)

lemma wf_A: "communicatively_wf J A \<alpha>" 
  unfolding communicatively_wf_def using FVE_Psymb by fastforce

lemma wf_C: "communicatively_wf J C \<alpha>"
  unfolding communicatively_wf_def using FVE_Psymb by fastforce



subsection \<open>Proof machinery\<close>

lemma CNP_chp_nocom: "CNP J chp_nocom \<subseteq> {}"
  using CNP_Chp by (fastforce simp add: chp_nocom_def) 

lemma nocom_empty_trace: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I chp_nocom \<Longrightarrow> \<tau> = []"
  using CNP_chp_nocom CNP_empty_no_com by blast


lemma coincidence_assm_set:
  assumes "Vagree \<nu> \<kappa> (FVE (\<pi>\<^sub>I I) A)"
  assumes "g_assm_set rel \<nu> \<tau> \<subseteq> fml_sem I A"
  shows "g_assm_set rel \<kappa> \<tau> \<subseteq> fml_sem I A"
proof
  fix \<kappa>'
  assume "\<kappa>' \<in> g_assm_set rel \<kappa> \<tau>"
  then obtain \<tau>' where 0: "rel \<tau>' \<tau> \<and> \<kappa>' = \<kappa> @@ \<tau>'" using g_assm_set_def by auto
  hence "Vagree (\<nu> @@ \<tau>') (\<kappa> @@ \<tau>') (FVE (\<pi>\<^sub>I I) A)" using assms Vagree_sttconc_cong by blast
  moreover have "\<nu> @@ \<tau>' \<in> fml_sem I A" using assms g_assm_set_def 0 by blast
  ultimately show "\<kappa>' \<in> fml_sem I A" using 0 coincidence_fml_FVE by blast
qed

lemma assm_set_forward_transfer:
  assumes "(\<nu>, \<tau>, Fin \<kappa>) \<in> chp_sem I \<alpha>"
  shows "(g_assm_set rel \<nu> \<tau>' \<subseteq> fml_sem I A) \<Longrightarrow> (g_assm_set rel \<kappa> \<tau>' \<subseteq> fml_sem I A)"
  by (meson Vagree_sym assms communicative_coincidence(1) coincidence_assm_set wf_A)

lemma assm_set_backward_transfer:
  assumes "(\<nu>, \<tau>, Fin \<kappa>) \<in> chp_sem I \<alpha>"
  shows "(g_assm_set rel \<kappa> \<tau>' \<subseteq> fml_sem I A) \<Longrightarrow> (g_assm_set rel \<nu> \<tau>' \<subseteq> fml_sem I A)"
  by (meson Vagree_sym assms communicative_coincidence(1) coincidence_assm_set wf_A)


lemma C_xid1: "\<nu> @@ \<tau> \<in> fml_sem I C \<longleftrightarrow> rrepv \<nu> xid1 r @@ \<tau> \<in> fml_sem I C"
  by (simp add: args_sem_def sttconc_def)

lemma g_assm_set_xid1: "g_assm_set rel \<nu> \<tau> \<subseteq> fml_sem I A \<longleftrightarrow> g_assm_set rel (rrepv \<nu> xid1 r) \<tau> \<subseteq> fml_sem I A"
  apply (simp add: g_assm_set_def args_sem_def sttconc_def)
  by fastforce


definition comfree :: "chp \<Rightarrow> bool"
  where "comfree \<alpha> = (\<forall>I \<nu> \<tau> \<omega> h. (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<longrightarrow> byrec \<tau> h = [])"


lemma assm_set_empty_traceI: "\<nu> \<in> fml_sem I A \<Longrightarrow> assm_set \<nu> [] \<subseteq> fml_sem I A"
  using g_assm_set_def by auto






lemma stT_ini_eq_fin: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> \<omega> \<noteq> NonFin \<Longrightarrow> (stT \<nu>) = (stT (gets \<omega>))"
  by (metis reachedstate.collapse Vagree_alltvars bound_effect_on_state(2))
                                                                            
lemma trecs_subseteq_RecP_trecs: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> trecs \<tau> \<subseteq> RecP (\<pi>\<^sub>I I) \<alpha>"
  by (fastforce simp add: RecP_def trecs_equiv_byrec)

lemma trecs_bounded: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I chp1 \<Longrightarrow> byrec \<tau> rec = tflat \<tau>"
proof -
  have "RecP (\<pi>\<^sub>I I) chp1 \<subseteq> {rec}" using RecP_Chp_overapprox by fastforce
  moreover assume "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I chp1"
  ultimately show "byrec \<tau> rec = tflat \<tau>"  by (meson basic_trans_rules(23) trecs_byrec trecs_subseteq_RecP_trecs)
qed

lemma byrec_non_rec_empty: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I chp1 \<Longrightarrow> byrec \<tau> hid0 = []"
  using urec_byrec_other trecs_bounded by blast





lemma PInterp_coincidence: "Vagree \<nu> \<omega> X \<Longrightarrow> d\<^sub>1 = d\<^sub>2 \<Longrightarrow> PInterp I X \<nu> d\<^sub>1 = PInterp I X \<omega> d\<^sub>2"
  by (metis PInterp_correct is_pinterp_alt)

lemma PInterp_coincidence_conv: "PInterp I X \<nu> d\<^sub>1 \<noteq> PInterp I X \<omega> d\<^sub>2 \<Longrightarrow> \<not>Vagree \<nu> \<omega> X \<or> d\<^sub>1 \<noteq> d\<^sub>2"
  using PInterp_coincidence by blast




subsection \<open>Soundness of Modal Logic Principles\<close>

text \<open>Because an axiom in a uniform substitution calculus is an individual formula, 
  proving the validity of that formula suffices to prove soundness\<close>

lemma diamond_axiom_valid: "valid diamond_axiom"
  unfolding diamond_axiom_def Diamond_def by simp

lemma ac_diamond_axiom_valid: "valid ac_diamond_axiom"
  unfolding AcDia_def ac_diamond_axiom_def by simp

lemma boxes_dual_valid_schematic: "valid ((Box \<alpha> \<psi>) \<leftrightarrow> (AcBox \<alpha> TT TT \<psi>))"
  by (rule valid_equivI) fastforce+

lemma boxes_dual_valid: "valid boxes_dual_axiom"
  unfolding boxes_dual_axiom_def using boxes_dual_valid_schematic by simp

lemma ac_modal_mp_valid: "valid ac_modal_mp_axiom"
  unfolding ac_modal_mp_axiom_def valid_impl by auto

lemma assumption_weakening_lemma:
  assumes "\<nu> \<in> fml_sem I (AcBox chp1 TT ((C && B) \<rightarrow> A) TT)"
  assumes "\<nu> \<in> fml_sem I (AcBox chp1 A C p1)"
  shows "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I chp1 \<Longrightarrow> strict_assm_set \<nu> \<tau> \<subseteq> fml_sem I B \<Longrightarrow> strict_assm_set \<nu> \<tau> \<subseteq> fml_sem I A"
proof (induction \<tau> arbitrary: \<omega> rule: rev_induct, simp)
  case (snoc \<rho> \<tau>)
  hence run: "(\<nu>, \<tau>, NonFin) \<in> chp_sem I chp1"
    by (metis chp_sem_total_and_pc obspref_alt pc.simps prefix_def)
  hence subset: "strict_assm_set \<nu> \<tau> \<subseteq> fml_sem I A" using snoc assm_set_strict_prefix by blast

  show ?case
  proof (rule; goal_cases strict_assm)
    case (strict_assm \<kappa>)
    then obtain \<tau>' where kappa: "\<kappa> = \<nu> @@ \<tau>'" and prec: "\<tau>' \<prec> (\<tau> @ [\<rho>])"
      unfolding g_assm_set_def by auto
    hence "\<tau>' \<preceq> \<tau>" unfolding strict_prefix_def by (metis prefix_snoc)
    hence "\<tau>' \<prec> \<tau> \<or> \<tau>' = \<tau>" by auto
    then show ?case
    proof
      assume "\<tau>' \<prec> \<tau>"
      hence "\<kappa> \<in> strict_assm_set \<nu> \<tau>" unfolding g_assm_set_def using kappa by auto
      thus ?case using subset by auto
    next
      assume "\<tau>' = \<tau>"
      hence eq: "\<kappa> = \<nu> @@ \<tau>" using kappa by simp
      hence "\<kappa> \<in> fml_sem I ((C && B) \<rightarrow> A)" using ac_box_commit assms(1) run by auto
      moreover have "\<kappa> \<in> fml_sem I C" using ac_box_commit assms(2) subset run eq by auto
      moreover have "\<kappa> \<in> fml_sem I B" using snoc(3) eq strict_assm by auto
      ultimately show ?case by simp
    qed
  qed
qed

lemma assumption_weakening_valid: "valid assumption_weakening_axiom"
  unfolding assumption_weakening_axiom_def valid_impl
proof (clarify, rule ac_box_by_ac_casesI, goal_cases commit post)
  case (commit I \<nu> \<tau> \<omega>)
  then show ?case using assumption_weakening_lemma by simp
next
  case (post I \<nu> \<tau> \<omega>)
  hence "strict_assm_set \<nu> \<tau> \<subseteq> fml_sem I B" using weaken_assm_set by auto
  hence strictA: "strict_assm_set \<nu> \<tau> \<subseteq> fml_sem I A" using assumption_weakening_lemma post by simp

  hence C: "\<nu> @@ \<tau> \<in> fml_sem I C" using ac_box_commit post by simp
  moreover have "\<nu> @@ \<tau> \<in> fml_sem I ((C && B) \<rightarrow> A)" using post by auto
  moreover have "\<nu> @@ \<tau> \<in> fml_sem I B" using assm_set_contains_boundary post(3) by fastforce
  ultimately have "\<nu> @@ \<tau> \<in> fml_sem I A" by simp
  hence "assm_set \<nu> \<tau> \<subseteq> fml_sem I A" using strictA assm_set_kernel_plus_boundary by force
  then show ?case using ac_box_post fml_sem.simps(5) post by blast
qed



subsection \<open>Soundness of Axioms for Atomic Programs\<close>

lemma stutterd_valid: "valid stutterd_axiom" 
  unfolding stutterd_axiom_def using valid_equivI fml_sem.simps(8) by force

lemma assign_valid: "valid assign_axiom"
  unfolding assign_axiom_def
  by (auto simp add: valid_equiv args_sem_def)

lemma assigneq_valid: "valid assigneq_axiom"
  unfolding assigneq_axiom_def
  by (auto simp add: valid_equiv args_sem_def sorteq_def)

lemma test_valid: "valid test_axiom" 
  unfolding test_axiom_def using valid_equiv by fastforce

lemma send_valid: "valid send_axiom"
proof (unfold send_axiom_def, rule valid_equivI, goal_cases forward backward)
  case (forward I \<nu>)
  then show ?case
    apply (auto simp add: args_sem_def stT_sttconc_dist)
    using obspref_refl by fastforce
next
  case (backward I \<nu>)
  let ?\<tau> = "Tp ((stT \<nu> rec) @ [mkevent ch1 (QRFuncs I fid1 []) (stR \<nu> \<mu>)])"
  have "sorteq (Tv hid0) ?\<tau> \<longrightarrow> upds \<nu> (Tv hid0) ?\<tau> \<in> fml_sem I 
      (TVar hid0 =\<^sub>T (TVar rec) \<circ>\<^sub>T (ComItm ch1 const (RVar \<mu>)) \<rightarrow> Pofh hid0)"
    using backward by auto
  hence "upds \<nu> (Tv hid0) ?\<tau> \<in> fml_sem I (Pofh hid0)"
    unfolding sorteq_def by simp
  thus ?case by (auto simp add: args_sem_def stT_sttconc_dist obspref_alt)
qed

lemma receive_valid: "valid receive_axiom"
  unfolding receive_axiom_def
  apply (rule valid_equivI)
  using xid1_neq_gtime by fastforce+

lemma ac_receive_valid: "valid ac_receive_axiom" 
proof (unfold ac_receive_axiom_def, rule valid_equivI, goal_cases forward backward)
  case (forward I \<nu>)
  show "\<nu> \<in> fml_sem I ([[ xid1 := * ]] AcBox (Send ch1 rec (RVar xid1)) A C (Pofhx rec xid1))"
  proof (rule box_by_runsI)
    fix \<tau>\<^sub>0 \<kappa>
    assume "(\<nu>, \<tau>\<^sub>0, Fin \<kappa>) \<in> chp_sem I (xid1 := *)"
    then obtain r where 0: "\<tau>\<^sub>0 = []" and 1: "\<kappa> = rrepv \<nu> xid1 r" by auto
    moreover have "rrepv \<nu> xid1 r \<in> fml_sem I (AcBox (Send ch1 rec (RVar xid1)) A C (Pofhx rec xid1))"
    proof (rule ac_box_by_ac_casesI, goal_cases commit post)
      case (commit \<tau> \<omega>)
      hence "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I (Receive ch1 rec xid1)" using xid1_neq_gtime by fastforce
      moreover have  "strict_assm_set \<nu> \<tau> \<subseteq> fml_sem I A" using g_assm_set_xid1 commit by simp
      ultimately show ?case using C_xid1 ac_box_commit forward by simp
    next
      case (post \<tau> \<omega>)
      hence "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I (Receive ch1 rec xid1)" using xid1_neq_gtime by fastforce
      moreover have "assm_set \<nu> \<tau> \<subseteq> fml_sem I A" using g_assm_set_xid1 post by blast
      ultimately show ?case using ac_box_post forward by blast
    qed
    ultimately show "\<kappa> @@ \<tau>\<^sub>0 \<in> fml_sem I (AcBox (Send ch1 rec (RVar xid1)) A C (Pofhx rec xid1))" by simp
  qed
next
  case (backward I \<nu>)
  show ?case
  proof (rule ac_box_by_ac_casesI, goal_cases commit post)
    case (commit \<tau> \<omega>)
    then obtain r where "(\<tau>, \<omega>) \<sqsubseteq> ([mkrecevent rec ch1 r (stR \<nu> \<mu>)], Fin (rrepv \<nu> xid1 r))" by auto
    hence "(rrepv \<nu> xid1 r, \<tau>, \<omega>) \<in> chp_sem I (Send ch1 rec (RVar xid1))"
      by (simp add: rrepv_def gtime_def)
    moreover have "rrepv \<nu> xid1 r \<in> fml_sem I (AcBox (Send ch1 rec (RVar xid1)) A C (Pofhx rec xid1))"
      using backward by fastforce
    moreover from commit have "strict_assm_set (rrepv \<nu> xid1 r) \<tau> \<subseteq> fml_sem I A" 
      using g_assm_set_xid1 by simp
    ultimately show ?case using C_xid1 ac_box_commit by simp
  next
    case (post \<tau> \<omega>)
    then obtain r where "(\<tau>, Fin \<omega>) \<sqsubseteq> ([mkrecevent rec ch1 r (stR \<nu> \<mu>)], Fin (rrepv \<nu> xid1 r))" by auto
    hence "(rrepv \<nu> xid1 r, \<tau>, Fin \<omega>) \<in> chp_sem I (Send ch1 rec (RVar xid1))"
      by (simp add: rrepv_def gtime_def)
    moreover have "rrepv \<nu> xid1 r \<in> fml_sem I (AcBox (Send ch1 rec (RVar xid1)) A C (Pofhx rec xid1))"
      using backward by fastforce
    moreover from post have "assm_set (rrepv \<nu> xid1 r) \<tau> \<subseteq> fml_sem I A" 
      using g_assm_set_xid1 by simp
    ultimately show ?case using ac_box_post by blast
  qed
qed                                                 

lemma ac_unfolding_valid: "valid ac_unfolding_axiom" 
proof (unfold ac_unfolding_axiom_def, rule valid_equivI, goal_cases forward backward)
  case (forward I \<nu>)
  show ?case
  proof (rule ac_box_by_ac_casesI, goal_cases commit post)
    case (commit \<tau>\<^sub>0 \<omega>\<^sub>0)
    hence "\<nu> \<in> fml_sem I C" using forward ac_box_commits_initial by blast
    then show ?case using commit by auto
  next
    case (post \<tau>\<^sub>0 \<omega>\<^sub>0)
    hence A: "\<nu> \<in> fml_sem I A" using assm_set_contains_boundary by fastforce

    have "\<nu> \<in> fml_sem I ([[ Send ch1 rec const ]] AcBox (? TT) A C (Pofh rec))"
    proof (rule box_by_runsI)
      fix \<tau> \<omega>
      assume 0: "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I (Send ch1 rec const)"
      hence com: "\<tau> = [mkrecevent rec ch1 (rtrm_sem I const \<nu>) ((stR \<nu>)(\<mu>))]" 
        by (simp add: obspref_alt)
      hence sassm: "strict_assm_set \<nu> \<tau> \<subseteq> fml_sem I A" using strict_assm_set_singleton com A by simp

      have "\<nu> @@ \<tau> \<in> fml_sem I (AcBox (? TT) A C (Pofh rec))"
      proof (rule ac_box_by_ac_casesI, goal_cases commit post)
        case (commit \<tau>\<^sub>1 \<omega>\<^sub>1)
        then show ?case using 0 forward sassm by auto            
      next
        case (post \<tau>\<^sub>1 \<omega>\<^sub>1)
        hence "\<nu> @@ \<tau> \<in> fml_sem I A"  using assm_set_contains_boundary by fastforce
        hence "assm_set \<nu> \<tau> \<subseteq> fml_sem I A" using sassm assm_set_kernel_plus_boundary by force
        hence "\<nu> @@ \<tau> \<in> fml_sem I (Pofh rec)" 
          using 0 forward send_no_state_change ac_box_post by blast
        then show ?case using post send_no_state_change by simp
      qed
      thus "\<omega> @@ \<tau> \<in> fml_sem I (AcBox (? TT) A C (Pofh rec))" 
        using 0 send_no_state_change by blast
    qed
    then show ?case using post by auto
  qed
next
  case (backward I \<nu>)
  show ?case
  proof (rule ac_box_by_ac_casesI, goal_cases commit post)
    case (commit \<tau> \<omega>)   
    then show ?case
    proof (cases "\<tau>")
      case Nil
      then show ?thesis using backward by simp
    next
      case (Cons _ _)
      hence "\<tau> \<noteq> []" by simp
      moreover have "(\<tau>, \<omega>) \<sqsubseteq> ([mkrecevent rec ch1 (rtrm_sem I const \<nu>) ((stR \<nu>)(\<mu>))], Fin \<nu>)" 
        using commit by simp
      ultimately have com: "\<tau> = [mkrecevent rec ch1 (rtrm_sem I const \<nu>) ((stR \<nu>)(\<mu>))]" 
        by (metis obspref_alt prefix_Cons prefix_bot.extremum_uniqueI)
      
      hence "\<nu> \<in> fml_sem I A" using commit by (simp add: strict_assm_set_singleton)
      hence "assm_set \<nu> [] \<subseteq> fml_sem I A" using g_assm_set_def by auto
      then show ?thesis using backward by (simp add: com obspref_refl)
    qed
  next
    case (post \<tau> \<omega>)
    hence com: "\<tau> = [mkrecevent rec ch1 (rtrm_sem I const \<nu>) ((stR \<nu>)(\<mu>))]" 
      using obspref_alt by fastforce
    
    hence "\<nu> \<in> fml_sem I A" using post 
      by (metis assm_set_contains_boundary assm_set_pc prefix_code(1) sttconc_empty subset_eq)
    hence "assm_set \<nu> [] \<subseteq> fml_sem I A" using g_assm_set_def by auto
    hence pof: "\<nu> @@ \<tau> \<in> fml_sem I (AcBox (? TT) A C (Pofh rec))" 
      using backward by (simp add: com obspref_refl)

    have "\<nu> @@ \<tau> \<in> fml_sem I A" using com post by force
    hence "assm_set (\<nu> @@ \<tau>) [] \<subseteq> fml_sem I A" using g_assm_set_def by auto
    hence "\<nu> @@ \<tau> \<in> fml_sem I (Pofh rec)" using pof by simp

    then show ?case using post(1) send_no_state_change by blast
  qed
qed


             
subsection \<open>Soundness of Axioms for Compound Programs\<close>

lemma ac_weakening_valid: "valid ac_weakening_axiom"
proof (unfold ac_weakening_axiom_def, rule valid_equivI, goal_cases forward backward)
  case (forward I \<nu>)
  show "\<nu> \<in> fml_sem I (C && AcBox chp1 A C (C && (A \<rightarrow> p1)))"
  proof (rule fml_sem_andI)
    have "(\<nu>, [], NonFin) \<in> chp_sem I chp1" using chp_sem_least_computations by blast
    thus "\<nu> \<in> fml_sem I C" using forward by fastforce
  next
    show "\<nu> \<in> fml_sem I (AcBox chp1 A C (C && (A \<rightarrow> p1)))"
    proof (rule ac_box_by_ac_casesI, goal_cases commit post)
      case (commit \<tau> \<omega>)
      thus ?case using forward by simp 
    next
      case (post \<tau> \<omega>)
      have "\<nu> @@ \<tau> \<in> fml_sem I C" using forward post weaken_assm_set by fastforce
      hence "\<omega> @@ \<tau> \<in> fml_sem I C" using communicative_coincidence wf_C post by blast
      moreover have "\<omega> @@ \<tau> \<in> fml_sem I p1" using forward post by fastforce
      ultimately show ?case by simp
    qed
  qed
next
  case (backward I \<nu>)
  show "\<nu> \<in> fml_sem I (AcBox chp1 A C p1)"
  proof (rule ac_box_by_ac_casesI, goal_cases commit post)
    case (commit \<tau> \<omega>)
    thus ?case using backward by simp
  next
    case (post \<tau> \<omega>)
    hence "\<omega> @@ \<tau> \<in> fml_sem I (C && (A \<rightarrow> p1))" by (metis IntD2 ac_box_post backward fml_sem.simps(5))
    hence "\<omega> @@ \<tau> \<in> fml_sem I (A \<rightarrow> p1)" by simp
    moreover have "\<omega> @@ \<tau> \<in> fml_sem I A" using assm_set_contains_boundary assm_set_forward_transfer post by blast
    ultimately show ?case by simp
  qed
qed

lemma nocom_valid: "valid nocom_axiom"
proof (unfold nocom_axiom_def, rule valid_equivI, goal_cases forward backward)
  case (forward I \<nu>)
  hence "\<nu> \<in> fml_sem I (A \<rightarrow> Box chp_nocom p1)"
    by (metis ac_box_post assm_set_empty_traceI box_by_runsI fml_sem_implI nocom_empty_trace)
  thus ?case using ac_box_commits_initial fml_sem_andI forward by blast
next 
  case (backward I \<nu>)
  thus ?case using ac_box_by_ac_casesI assm_set_kernel_plus_boundary nocom_empty_trace by fastforce
qed

lemma ac_choice_valid: "valid ac_choice_axiom"
  unfolding ac_choice_axiom_def Or_def by (auto simp add: valid_equiv)

(* Ac-composition is shown schematically in order to make it useable for the soundness proofs
of other axioms without the need of instantiating it via uniform substitution. A direct proof 
for the non-schematic ac-composition axiom would be along a quite similar structure *)
lemma ac_composition_schematic:
  assumes wf_a: "wf_chp \<L> \<alpha>" and wf_b: "wf_chp \<L> \<beta>"
  shows "fml_sem I ((AcBox (\<alpha> ;; \<beta>) A C \<psi>)) = fml_sem I (AcBox \<alpha> A C (AcBox \<beta> A C \<psi>))"
proof ((rule; rule), goal_cases forward backward)
  case (forward \<nu>)
  assume satSeq: "\<nu> \<in> fml_sem I (AcBox (\<alpha> ;; \<beta>) A C \<psi>)"
  show "\<nu> \<in> fml_sem I (AcBox \<alpha> A C (AcBox \<beta> A C \<psi>))"
  proof (rule ac_box_by_ac_casesI, goal_cases outer_commit outer_post)
    case (outer_commit \<tau>\<^sub>1 \<kappa>)
    hence "(\<nu>, \<tau>\<^sub>1, NonFin) \<in> chp_sem I (\<alpha> ;; \<beta>)" by auto
    thus ?case using fml_sem.simps(8) satSeq outer_commit(2) by blast
  next
    case (outer_post \<tau>\<^sub>1 \<kappa>)
    hence assm: "assm_set \<kappa> \<tau>\<^sub>1 \<subseteq> fml_sem I A" using assm_set_forward_transfer by simp
    show "\<kappa> @@ \<tau>\<^sub>1 \<in> fml_sem I (AcBox \<beta> A C \<psi>)"                    
    proof (rule ac_box_by_ac_casesI, goal_cases inner_commit inner_post)
      case (inner_commit \<tau>\<^sub>2 \<omega>)
      hence "(\<kappa>, \<tau>\<^sub>2, botify (stt_rmsuffix \<tau>\<^sub>1) \<omega>) \<in> chp_sem I \<beta>" using remove_initial_communication wf_b by blast
      hence "(\<nu>, \<tau>\<^sub>1 @ \<tau>\<^sub>2, botify (stt_rmsuffix \<tau>\<^sub>1) \<omega>) \<in> chp_sem I (\<alpha> ;; \<beta>)" using outer_post by auto   
      moreover have "strict_assm_set \<nu> (\<tau>\<^sub>1 @ \<tau>\<^sub>2) \<subseteq> fml_sem I A" using assm inner_commit
        assm_union_strict_assm assm_set_backward_transfer by (meson Un_subset_iff dual_order.trans outer_post(1))
      ultimately have  "\<nu> @@ (\<tau>\<^sub>1 @ \<tau>\<^sub>2) \<in> fml_sem I C" using ac_box_commit satSeq by blast
      hence "(\<nu> @@ \<tau>\<^sub>1) @@ \<tau>\<^sub>2 \<in> fml_sem I C" using sttconc_dist_app by auto
      moreover have "Vagree ((\<nu> @@ \<tau>\<^sub>1) @@ \<tau>\<^sub>2) ((\<kappa> @@ \<tau>\<^sub>1) @@ \<tau>\<^sub>2) (FVE (\<pi>\<^sub>I I) C)" using Vagree_and Vagree_sttconc_cong communicative_coincidence(1) wf_C outer_post(1) by meson
      ultimately show "(\<kappa> @@ \<tau>\<^sub>1) @@ \<tau>\<^sub>2 \<in> fml_sem I C" using coincidence_fml_FVE by blast
    next
      case (inner_post \<tau>\<^sub>2 \<omega>)
      hence "(\<kappa>, \<tau>\<^sub>2, Fin (stt_rmsuffix \<tau>\<^sub>1 \<omega>)) \<in> chp_sem I \<beta>" using remove_initial_communication wf_b botify.simps(2) by metis
      hence "(\<nu>, \<tau>\<^sub>1 @ \<tau>\<^sub>2, Fin (stt_rmsuffix \<tau>\<^sub>1 \<omega>)) \<in> chp_sem I (\<alpha> ;; \<beta>)" using outer_post by auto 
      moreover have "assm_set \<nu> (\<tau>\<^sub>1 @ \<tau>\<^sub>2) \<subseteq> fml_sem I A" using assm inner_post assm_union assm_set_backward_transfer
        by (meson Un_subset_iff dual_order.trans outer_post(1))
      moreover have "Fin (stt_rmsuffix \<tau>\<^sub>1 \<omega>) \<noteq> NonFin" by blast
      ultimately have "(gets (Fin (stt_rmsuffix \<tau>\<^sub>1 \<omega>))) @@ (\<tau>\<^sub>1 @ \<tau>\<^sub>2) \<in> fml_sem I \<psi>" by (metis ac_box_post reachedstate.sel satSeq)
      hence "(stt_rmsuffix \<tau>\<^sub>1 \<omega>) @@ (\<tau>\<^sub>1 @ \<tau>\<^sub>2) \<in> fml_sem I \<psi>" by simp
      hence "((stt_rmsuffix \<tau>\<^sub>1 \<omega>) @@ \<tau>\<^sub>1) @@ \<tau>\<^sub>2 \<in> fml_sem I \<psi>" by (metis sttconc_dist_app)
      moreover have "is_stt_suffix \<omega> \<tau>\<^sub>1" using suffix_of_initial_is_suffix_of_final inner_post(1) by blast
      ultimately show "\<omega> @@ \<tau>\<^sub>2 \<in> fml_sem I \<psi>" by (metis stt_rmsuffix_correct_rev)
    qed
  qed
next
  case (backward \<nu>)
  assume satDecomposed: "\<nu> \<in> fml_sem I (AcBox \<alpha> A C (AcBox \<beta> A C \<psi>))"
  show "\<nu> \<in> fml_sem I (AcBox (\<alpha> ;; \<beta>) A C \<psi>)"
  proof (rule ac_box_by_ac_casesI, goal_cases commit post)
    case (commit \<tau> \<omega>)
    then obtain \<tau>\<^sub>1 \<kappa> \<tau>\<^sub>2 where seqSem: "(\<nu>, \<tau>, NonFin) \<in> botop (chp_sem I \<alpha>) \<or> (\<tau> = \<tau>\<^sub>1 @ \<tau>\<^sub>2 \<and> (\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> chp_sem I \<alpha> \<and> (\<kappa>, \<tau>\<^sub>2, \<omega>) \<in> chp_sem I \<beta>)" by auto
    thus ?case
    proof (cases "(\<nu>, \<tau>, NonFin) \<in> botop (chp_sem I \<alpha>)")
      case True
      hence "(\<nu>, \<tau>, NonFin) \<in> chp_sem I \<alpha>" using denotations_contain_bot chp_sem_total_and_pc by blast
      thus ?thesis using commit(2) satDecomposed by fastforce
    next
      case False
      hence continueSem: "\<tau> = \<tau>\<^sub>1 @ \<tau>\<^sub>2 \<and> (\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> chp_sem I \<alpha> \<and> (\<kappa>, \<tau>\<^sub>2, \<omega>) \<in> chp_sem I \<beta>" using seqSem by blast
      thus ?thesis
      proof (cases "\<tau>\<^sub>2")
        case Nil (* this case can be proven since \<tau>\<^sub>2 = [] empty is false *)
        thus ?thesis using False seqSem by fastforce
      next
        case (Cons _ _)
        have 0: "strict_assm_set \<kappa> (\<tau>\<^sub>1 @ \<tau>\<^sub>2) \<subseteq> fml_sem I A" using commit(2) continueSem assm_set_forward_transfer by blast

        have "assm_set \<nu> \<tau>\<^sub>1 \<subseteq> fml_sem I A" using Cons commit(2) continueSem assm_subseteq_sassm_non_empty_extension by blast
        hence "\<kappa> @@ \<tau>\<^sub>1 \<in> fml_sem I (AcBox \<beta> A C \<psi>)" using continueSem satDecomposed fml_sem.simps(8) by fastforce
        moreover have "(\<kappa> @@ \<tau>\<^sub>1, \<tau>\<^sub>2, NonFin) \<in> chp_sem I \<beta>" using continueSem add_initial_com_nonfin wf_b by blast
        moreover have "strict_assm_set (\<kappa> @@ \<tau>\<^sub>1) \<tau>\<^sub>2 \<subseteq> fml_sem I A" using 0 strict_assm_set_sttconc_weaken order.trans by blast
        ultimately have "(\<kappa> @@ \<tau>\<^sub>1) @@ \<tau>\<^sub>2 \<in> fml_sem I C" using fml_sem.simps(8) by fastforce
        thus ?thesis by (metis continueSem communicative_coincidence(2) wf_C sttconc_dist_app)
      qed
    qed  
  next
    case (post \<tau> \<omega>)                                                                         
    then obtain \<tau>\<^sub>1 \<kappa> \<tau>\<^sub>2 where continueSem: "\<tau> = \<tau>\<^sub>1 @ \<tau>\<^sub>2 \<and> (\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> chp_sem I \<alpha> \<and> (\<kappa>, \<tau>\<^sub>2, Fin \<omega>) \<in> chp_sem I \<beta>" by fastforce
    hence "assm_set \<nu> \<tau>\<^sub>1 \<subseteq> fml_sem I A" using assm_set_prefix post(2) by blast
    hence secondBox: "\<kappa> @@ \<tau>\<^sub>1 \<in> fml_sem I (AcBox \<beta> A C \<psi>)" using continueSem satDecomposed by fastforce
    
    have "assm_set \<kappa> \<tau> \<subseteq> fml_sem I A" using post continueSem assm_set_forward_transfer by blast
    hence "assm_set (\<kappa> @@ \<tau>\<^sub>1) \<tau>\<^sub>2 \<subseteq> fml_sem I A" using assm_set_sttconc_weaken continueSem by blast
    moreover have "(\<kappa> @@ \<tau>\<^sub>1, \<tau>\<^sub>2, Fin (\<omega> @@ \<tau>\<^sub>1)) \<in> chp_sem I \<beta>" using add_initial_communication_fin continueSem wf_b by blast
    ultimately have "(\<omega> @@ \<tau>\<^sub>1) @@ \<tau>\<^sub>2 \<in> fml_sem I \<psi>" using secondBox by fastforce
    thus ?case using continueSem sttconc_dist_app by presburger
  qed
qed

lemma ac_composition_valid: "valid ac_composition_axiom"
  unfolding ac_composition_axiom_def
  using ac_composition_schematic wf_chp1 wf_chp2
  by (simp only: valid_equiv) blast

(* Shown schematically first for the same reasons as for ac-composition *)
lemma ac_iteration_schematic:                    
  assumes wf: "wf_chp \<L> \<alpha>"
  shows "fml_sem I ((AcBox \<alpha>** A C \<psi>)) = fml_sem I (AcBox (? TT) A C \<psi>) \<inter> fml_sem I (AcBox \<alpha> A C (AcBox \<alpha>** A C \<psi>))"
proof ((rule; rule), goal_cases forward backward)
  case (forward \<nu>)
  show "\<nu> \<in> (fml_sem I (AcBox (? TT) A C \<psi>)) \<inter> (fml_sem I (AcBox \<alpha> A C (AcBox \<alpha>** A C \<psi>)))"
  proof
    have "chp_sem I (? TT) \<subseteq> chp_sem I \<alpha>**" using chp_sem_test_TT zero_iterations by force
    thus "\<nu> \<in> fml_sem I (AcBox (? TT) A C \<psi>)" using ac_box_refinement forward by blast
  next
    have "chp_sem I (\<alpha> ;; (\<alpha>**)) \<subseteq> chp_sem I \<alpha>**" using unroll_rtcl_linhis by fastforce
    hence "\<nu> \<in> fml_sem I (AcBox (\<alpha> ;; (\<alpha>**)) A C \<psi>)" using ac_box_refinement forward by blast
    thus "\<nu> \<in> fml_sem I (AcBox \<alpha> A C (AcBox \<alpha>** A C \<psi>))"
      using wf by (simp only: ac_composition_schematic wf_chp.simps)
  qed
next
  case (backward \<nu>)
  hence "\<nu> \<in> fml_sem I (AcBox (? TT) A C \<psi>) \<inter> fml_sem I (AcBox (\<alpha> ;; (\<alpha>**)) A C \<psi>)"
    using wf by (simp only: ac_composition_schematic wf_chp.simps)
  hence "\<nu> \<in> fml_sem I (AcBox (? TT \<union>\<union> (\<alpha> ;; (\<alpha>**))) A C \<psi>)" by simp
  moreover have "chp_sem I (\<alpha>**) \<subseteq> chp_sem I (? TT \<union>\<union> (\<alpha> ;; (\<alpha>**)))" using unroll_rtcl_linhis by auto
  ultimately show "\<nu> \<in> fml_sem I (AcBox (\<alpha>**) A C \<psi>)" using ac_box_refinement by blast
qed

lemma ac_iteration_valid: "valid ac_iteration_axiom"
  unfolding ac_iteration_axiom_def 
  using ac_iteration_schematic wf_chp1 fml_sem.simps(5)
  by (simp only: valid_equiv) (blast)

lemma ac_induction_valid: "valid ac_induction_axiom"
proof (unfold ac_induction_axiom_def, rule valid_equivI, goal_cases forward backward)
  case (forward I \<nu>)
  show "\<nu> \<in> fml_sem I (AcBox (? TT) A C p1 && AcBox (chp1**) A TT (p1 \<rightarrow> AcBox chp1 A C p1))"
  proof (rule fml_sem_andI)
    show "\<nu> \<in> fml_sem I (AcBox (? TT) A C p1)" using forward ac_iteration_schematic wf_chp1 by blast
  next 
    have "\<nu> \<in> fml_sem I (AcBox chp1 A C (AcBox (chp1**) A C p1))" using forward ac_iteration_schematic wf_chp1 by blast                                        
    hence "\<nu> \<in> fml_sem I (AcBox (chp1 ;; (chp1**)) A C p1)" using ac_composition_schematic wf_chp1 wf_chp.simps(8) by blast
    hence "\<nu> \<in> fml_sem I (AcBox ((chp1**) ;; chp1) A C p1)" 
      unfolding fml_sem.simps(8) chp_sem.simps(7,8) using rtcl_assoc chp_sem_total_and_pc compose.simps by blast
    hence "\<nu> \<in> fml_sem I (AcBox (chp1**) A C (p1 \<rightarrow> AcBox chp1 A C p1))" 
      using ac_composition_schematic valid_equiv ac_box_impl_weaken wf_chp1 wf_chp.simps(8) by blast
    thus "\<nu> \<in> fml_sem I (AcBox (chp1**) A TT (p1 \<rightarrow> AcBox chp1 A C p1))" unfolding fml_sem.simps(8) using TT_valid valid_def by blast
  qed
next
  case (backward I \<nu>)
  have base: "\<nu> \<in> fml_sem I (AcBox (? TT) A C p1)" 
   and step: "\<nu> \<in> fml_sem I (AcBox (chp1**) A TT (p1 \<rightarrow> AcBox chp1 A C p1))" using backward by simp+
  show "\<nu> \<in> fml_sem I (AcBox (chp1**) A C p1)"
  proof (unfold fml_sem.simps(8), clarify)
    fix \<tau> \<omega>
    assume "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I (chp1**)"
    then obtain n where "(\<nu>, \<tau>, \<omega>) \<in> iterate_linhis n (chp_sem I chp1)" unfolding chp_sem.simps(8) linhis_rtcl_eq_iteration by blast
    thus "(strict_assm_set \<nu> \<tau> \<subseteq> fml_sem I A \<longrightarrow> \<nu> @@ \<tau> \<in> fml_sem I C) \<and>
         (\<omega> \<noteq> NonFin \<and> assm_set \<nu> \<tau> \<subseteq> fml_sem I A \<longrightarrow> gets \<omega> @@ \<tau> \<in> fml_sem I p1)"
    proof (induction n arbitrary: \<tau> \<omega>)
      case 0
      hence "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I (? TT)" using TT_valid valid_def by auto
      thus ?case by (metis ac_box_commit ac_box_post base reachedstate.collapse)
    next
      case (Suc m) (* m = n-1 *)
      hence 2: "(\<nu>, \<tau>, \<omega>) \<in> (botop (iterate_linhis m (chp_sem I chp1)) \<union> ((iterate_linhis m (chp_sem I chp1)) \<triangleright> (chp_sem I chp1)))" 
        using iterate_linhis_assoc chp_sem_total_and_pc unfolding iterate_linhis.simps(2) compose.simps by blast
      show ?case
      proof (cases "(\<nu>, \<tau>, \<omega>) \<in> botop (iterate_linhis m (chp_sem I chp1))")
        case True
        thus ?thesis using Suc.IH denotations_contain_bot chp_sem_total_and_pc iterate_linhis_pc by blast
      next
        case False
        hence "(\<nu>, \<tau>, \<omega>) \<in> (iterate_linhis m (chp_sem I chp1)) \<triangleright> (chp_sem I chp1)" using 2 by blast
        then obtain \<tau>\<^sub>1 \<kappa> \<tau>\<^sub>2 where com: "\<tau> = \<tau>\<^sub>1 @ \<tau>\<^sub>2"
          and arun_m: "(\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> iterate_linhis m (chp_sem I chp1)"
          and brun: "(\<kappa>, \<tau>\<^sub>2, \<omega>) \<in> chp_sem I chp1" by fastforce
        hence arun: "(\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> rtcl_linhis (chp_sem I chp1)" using linhis_rtcl_eq_iteration by blast

        have postIH:"(assm_set \<nu> \<tau>\<^sub>1 \<subseteq> fml_sem I A) \<Longrightarrow> \<kappa> @@ \<tau>\<^sub>1 \<in> fml_sem I (AcBox chp1 A C p1)"
        proof -
          assume 0: "assm_set \<nu> \<tau>\<^sub>1 \<subseteq> fml_sem I A"
          hence "\<kappa> @@ \<tau>\<^sub>1 \<in> fml_sem I p1" by (metis Suc.IH arun_m reachedstate.distinct(1) reachedstate.sel)
          moreover have "(\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> rtcl_linhis (chp_sem I chp1)" using arun linhis_rtcl_eq_iteration by blast
          ultimately show "\<kappa> @@ \<tau>\<^sub>1 \<in> fml_sem I (AcBox chp1 A C p1)" by (metis step Compl_iff UnE 0 ac_box_post chp_sem.simps(8) fml_sem_Implies)
        qed
        
        show ?thesis
        proof ((rule; rule), goal_cases commit post)
          case commit
          hence assm: "strict_assm_set \<kappa> \<tau> \<subseteq> fml_sem I A" using arun chp_sem.simps(8) assm_set_forward_transfer by blast
          show ?case
          proof (cases "\<tau>\<^sub>2 = []")
            case True
            thus ?thesis by (metis Suc.IH arun_m com commit self_append_conv)
          next
            case False
            hence "assm_set \<nu> \<tau>\<^sub>1 \<subseteq> fml_sem I A" using commit com assm_subseteq_sassm_non_empty_extension by blast
            hence "\<kappa> @@ \<tau>\<^sub>1 \<in> fml_sem I (AcBox chp1 A C p1)" using postIH com by fastforce
            moreover have "strict_assm_set (\<kappa> @@ \<tau>\<^sub>1) \<tau>\<^sub>2 \<subseteq> fml_sem I A" using assm com strict_assm_set_sttconc_weaken by blast
            moreover have "\<exists>\<omega>'. (\<kappa> @@ \<tau>\<^sub>1, \<tau>\<^sub>2, \<omega>') \<in> chp_sem I chp1" using brun add_initial_communication wf_chp.simps(1) by metis
            ultimately have "\<kappa> @@ \<tau> \<in> fml_sem I C" using postIH com sttconc_def by fastforce
            thus "\<nu> @@ \<tau> \<in> fml_sem I C" using communicative_coincidence(2) wf_C arun chp_sem.simps(8) by blast
          qed
        next
          case post
          hence assm: "assm_set \<kappa> \<tau> \<subseteq> fml_sem I A" using arun chp_sem.simps(8) assm_set_forward_transfer by blast
          have "assm_set \<nu> \<tau>\<^sub>1 \<subseteq> fml_sem I A" using post com assm_set_prefix by blast
          hence "\<kappa> @@ \<tau>\<^sub>1 \<in> fml_sem I (AcBox chp1 A C p1)" using postIH com by fastforce
          moreover have "(\<kappa> @@ \<tau>\<^sub>1, \<tau>\<^sub>2, Fin ((gets \<omega>) @@ \<tau>\<^sub>1)) \<in> chp_sem I chp1" using brun add_initial_communication_fin wf_chp.simps(1) by (metis post reachedstate.collapse)
          moreover have "assm_set (\<kappa> @@ \<tau>\<^sub>1) \<tau>\<^sub>2 \<subseteq> fml_sem I A" using assm com assm_set_sttconc_weaken by blast
          ultimately show "(gets \<omega>) @@ \<tau> \<in> fml_sem I p1" using ac_box_post com sttconc_dist_app by metis
        qed
      qed
    qed
  qed
qed

lemma VCagree_PhxOf_Dec: "Vagree \<nu> (rrepv \<nu> vvar (stR \<nu> vvar - 1)) (vspace_sem J (X\<^sub>3 \<inter>\<^sub>V (-\<^sub>V (VRVar vvar))))"
  using Vagree_rrepv apply (rule Vagree_antimon) by simp

lemma PhxOf_Dec: "\<nu> \<in> fml_sem I (PhxOf (Dec (RVar vvar))) \<Longrightarrow> rrepv \<nu> vvar (stR \<nu> vvar - 1) \<in> fml_sem I (PhxOf (RVar vvar))"
  apply (simp add: args_sem_def)
  using PInterp_correct VCagree_PhxOf_Dec PInterp_coincidence by fastforce

lemma vvar_notin_FVP_chpconv: "Rv vvar \<in> -FVP (\<pi>\<^sub>I I) chpconv"
  using FRvP_Chp by fastforce

lemma vvar_notin_BVP_chpconv [simp, intro]: "Rv vvar \<in> -BVP J chpconv"
  using BRvP_Chp by fastforce

lemma run_suffix_of_final:
  assumes "wf_chp \<L> \<alpha>"
  assumes "(\<nu> @@ \<tau>\<^sub>1, \<tau>\<^sub>2, Fin \<omega>) \<in> chp_sem I \<alpha>"
  shows "\<exists>\<omega>'. \<omega> = \<omega>' @@ \<tau>\<^sub>1 \<and> (\<nu>, \<tau>\<^sub>2, Fin \<omega>') \<in> chp_sem I \<alpha>"
  by (metis assms remove_initial_com_fin stt_rmsuffix_correct_rev suffix_of_initial_is_suffix_of_final)




lemma chpconv_run_vvar_cong:
  assumes "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I chpconv"
  shows "(rrepv \<nu> vvar d, \<tau>, Fin (rrepv \<omega> vvar d)) \<in> chp_sem I chpconv"
proof -
  have "Vagree \<nu> (rrepv \<nu> vvar d) (-{Rv vvar})" using Vagree_rrepv by blast
  moreover have "-{Rv vvar} \<supseteq> FVP (\<pi>\<^sub>I I) chpconv" using vvar_notin_FVP_chpconv by simp
  ultimately obtain \<omega>' where run: "(rrepv \<nu> vvar d, \<tau>, Fin \<omega>') \<in> chp_sem I chpconv \<and> Vagree \<omega> \<omega>' (-{Rv vvar})"
    using assms coincidence_chp_fin by blast
  moreover have "\<omega>' = rrepv \<omega> vvar d"
  proof -
    have "Vagree (rrepv \<nu> vvar d) \<omega>' (-BVP (\<pi>\<^sub>I I) chpconv)" 
      using bound_effect_property_short run by blast
    moreover have "(Rv vvar) \<in> (-BVP (\<pi>\<^sub>I I) chpconv)" using vvar_notin_BVP_chpconv by blast
    ultimately have "\<omega>' $$ (Rv vvar) = Rp d" using Vagree_def by auto
    thus ?thesis by (metis Vagree_single_upds run upds.simps(1))
  qed
  ultimately show ?thesis by simp
qed

lemma chpconv_rep_vvar_cong: "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I (Repeat chpconv n) \<Longrightarrow> (rrepv \<nu> vvar d, \<tau>, Fin (rrepv \<omega> vvar d)) \<in> chp_sem I (Repeat chpconv n)"
proof (induction n arbitrary: \<nu> \<tau>)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain \<tau>\<^sub>1 \<tau>\<^sub>2 \<kappa>
    where com: "\<tau> = \<tau>\<^sub>1 @ \<tau>\<^sub>2" and "(\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> chp_sem I chpconv" and runn: "(\<kappa>, \<tau>\<^sub>2, Fin \<omega>) \<in> chp_sem I (Repeat chpconv n)"
    by auto
  hence "(rrepv \<nu> vvar d, \<tau>\<^sub>1, Fin (rrepv \<kappa> vvar d)) \<in> chp_sem I chpconv"
    using chpconv_run_vvar_cong by simp
  moreover have "(rrepv \<kappa> vvar d, \<tau>\<^sub>2, Fin (rrepv \<omega> vvar d)) \<in> chp_sem I (Repeat chpconv n)"
    using Suc(1) runn by simp
  ultimately show ?case using com by auto
qed

lemma chpconv_loop_vvar_cong:
  assumes "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I (chpconv**)"
  shows "(rrepv \<nu> vvar d, \<tau>, Fin (rrepv \<omega> vvar d)) \<in> chp_sem I (chpconv**)"
  using assms chpconv_rep_vvar_cong by (fastforce simp add: linhis_rtcl_eq_iteration chp_sem_Repeat)




lemma rrepv_sttconc_rev: "rrepv \<nu> x d @@ \<tau> = rrepv (\<nu> @@ \<tau>) x d"
  unfolding rrepv_def sttconc_def by simp




lemma convergence_lemma:
  assumes "\<And>\<tau> \<omega> x. (\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I (chpconv**) \<Longrightarrow> x > 0 \<Longrightarrow>
      rrepv (\<omega> @@ \<tau>) vvar x \<in> fml_sem I (PhxOf (RVar vvar) \<rightarrow> \<langle> chpconv \<rangle> (PhxOf (Dec (RVar vvar))))"
  shows "rrepv \<nu> vvar x \<in> fml_sem I (PhxOf (RVar vvar)) \<Longrightarrow>
      \<exists>\<tau> \<omega>. (rrepv \<nu> vvar x, \<tau>, Fin \<omega>) \<in> chp_sem I (Repeat chpconv (nat (ceiling x))) \<and>
        rrepv (\<omega> @@ \<tau>) vvar (x - nat (ceiling x)) \<in> fml_sem I (PhxOf (RVar vvar))"
using assms proof (induction "nat (ceiling x)" arbitrary: x \<nu>)
  case 0
  hence "(rrepv \<nu> vvar x, [], Fin (rrepv \<nu> vvar x)) \<in> chp_sem I (Repeat chpconv (nat (ceiling x)))" 
    and "rrepv (rrepv \<nu> vvar x @@ []) vvar (x - nat (ceiling x)) \<in> fml_sem I (PhxOf (RVar vvar))"
    by (simp_all add: rrepv_def)
  then show ?case by fastforce
next
  case (Suc n)

  (* obtain alpha run *)

  hence "x > 0" by linarith
  moreover have "(\<nu>, [], Fin \<nu>) \<in> chp_sem I (chpconv**)" 
    by (simp add: rtcl_linhis.rtcl_linhis_base_id)
  ultimately have "rrepv (\<nu> @@ []) vvar x \<in> fml_sem I (PhxOf (RVar vvar) \<rightarrow> \<langle> chpconv \<rangle> (PhxOf (Dec (RVar vvar))))"
    using Suc.prems(2) by blast
  hence "rrepv \<nu> vvar x \<in> fml_sem I (\<langle> chpconv \<rangle> (PhxOf (Dec (RVar vvar))))"
    using Suc.prems(1) by simp
  then obtain \<tau>\<^sub>1 \<kappa>
    where run: "(rrepv \<nu> vvar x, \<tau>\<^sub>1, Fin \<kappa>) \<in> chp_sem I chpconv"
      and phi_dec: "\<kappa> @@ \<tau>\<^sub>1 \<in> fml_sem I (PhxOf (Dec (RVar vvar)))"
    by auto

  (* obtain alpha* run *)

  hence kappa_vvar: "(rrepv \<nu> vvar x) $$ Rv vvar = \<kappa> $$ Rv vvar"
    by (meson Vagree_def bound_effect_property_short vvar_notin_BVP_chpconv)

  have "rrepv (\<kappa> @@ \<tau>\<^sub>1) vvar (x - 1) \<in> fml_sem I (PhxOf (RVar vvar))" 
    using kappa_vvar PhxOf_Dec phi_dec by force

  moreover have "n = nat (ceiling (x - 1))" using Suc(2) by simp
  moreover have "\<And>\<tau> \<omega> x. (\<kappa> @@ \<tau>\<^sub>1, \<tau>, Fin \<omega>) \<in> chp_sem I chpconv** \<Longrightarrow> x > 0 \<Longrightarrow>
        rrepv (\<omega> @@ \<tau>) vvar x \<in> fml_sem I (PhxOf (RVar vvar) \<rightarrow> \<langle>chpconv\<rangle>PhxOf (Dec (RVar vvar)))"
  proof -
    let ?x = "stR \<nu> vvar"
    fix \<tau>\<^sub>2 :: rectrace
    fix \<omega> :: state
    fix x' :: real
    assume "(\<kappa> @@ \<tau>\<^sub>1, \<tau>\<^sub>2, Fin \<omega>) \<in> chp_sem I chpconv**"
    moreover have "\<And>\<L>. wf_chp \<L> (chpconv**)" by simp
    ultimately obtain \<omega>' where omega: "\<omega> = \<omega>' @@ \<tau>\<^sub>1" and "(\<kappa>, \<tau>\<^sub>2, Fin \<omega>') \<in> chp_sem I (chpconv**)"
      using run_suffix_of_final by blast

    hence "(rrepv \<nu> vvar x, \<tau>\<^sub>1 @ \<tau>\<^sub>2, Fin \<omega>') \<in> chp_sem I (chpconv**)"
      using run rtcl_linhis.rtcl_linhis_continue by fastforce
    hence "(rrepv (rrepv \<nu> vvar x) vvar ?x, \<tau>\<^sub>1 @ \<tau>\<^sub>2, Fin (rrepv \<omega>' vvar ?x)) \<in> chp_sem I (chpconv**)"
      by (rule chpconv_loop_vvar_cong)
    hence "(\<nu>, \<tau>\<^sub>1 @ \<tau>\<^sub>2, Fin (rrepv \<omega>' vvar ?x)) \<in> chp_sem I (chpconv**)" by simp

    moreover assume "0 < x'"
    ultimately have "rrepv (rrepv \<omega>' vvar ?x @@ (\<tau>\<^sub>1 @ \<tau>\<^sub>2)) vvar x' \<in> fml_sem I (PhxOf (RVar vvar) \<rightarrow> \<langle>chpconv\<rangle>PhxOf (Dec (RVar vvar)))"
      using Suc.prems(2) by blast
    thus "?thesis \<tau>\<^sub>2 \<omega> x'" using rrepv_sttconc_rev rrepv_idem sttconc_dist_app omega by simp
  qed

  ultimately have "\<exists>\<tau> \<omega>. (rrepv (\<kappa> @@ \<tau>\<^sub>1) vvar (x - 1), \<tau>, Fin \<omega>) \<in> chp_sem I (Repeat chpconv n) \<and>
          rrepv (\<omega> @@ \<tau>) vvar (x - 1 - n) \<in> fml_sem I (PhxOf (RVar vvar))"
    using Suc(1) by blast

  then obtain \<tau>\<^sub>2 \<omega>
    where "(rrepv \<kappa> vvar (x - 1) @@ \<tau>\<^sub>1, \<tau>\<^sub>2, Fin \<omega>) \<in> chp_sem I (Repeat chpconv n)"
      and phi: "rrepv \<omega> vvar (x - 1 - n) @@ \<tau>\<^sub>2 \<in> fml_sem I (PhxOf (RVar vvar))"
    using rrepv_sttconc_rev by auto

  (* combine alpha and alpha* run *)

  moreover have "\<And>\<L>. wf_chp \<L> (Repeat chpconv n)" using wf_Repeat by force
  ultimately obtain \<omega>'
    where omega: "\<omega> = \<omega>' @@ \<tau>\<^sub>1"
      and run2: "(rrepv \<kappa> vvar (x - 1), \<tau>\<^sub>2, Fin \<omega>') \<in> chp_sem I (Repeat chpconv n)"
    using run_suffix_of_final wf_Repeat by blast

  hence "(rrepv (rrepv \<kappa> vvar (x - 1)) vvar x, \<tau>\<^sub>2, Fin (rrepv \<omega>' vvar x)) \<in>  chp_sem I (Repeat chpconv n)"
    using chpconv_rep_vvar_cong by blast
  hence "(\<kappa>, \<tau>\<^sub>2, Fin (rrepv \<omega>' vvar x)) \<in>  chp_sem I (Repeat chpconv n)" using kappa_vvar by simp

  hence "(rrepv \<nu> vvar x, \<tau>\<^sub>1 @ \<tau>\<^sub>2, Fin (rrepv \<omega>' vvar x)) \<in> chp_sem I (Repeat chpconv (Suc n))"
    using run by auto

  moreover from omega have "rrepv (rrepv \<omega>' vvar x @@ (\<tau>\<^sub>1 @ \<tau>\<^sub>2)) vvar (x - 1 - n) \<in> fml_sem I (PhxOf (RVar vvar))"
    using phi rrepv_sttconc_rev sttconc_dist_app rrepv_idem by simp
  moreover have "x - 1 - n = x - Suc n" by simp
  ultimately show ?case using Suc(2) by auto
qed

lemma convergence_valid: "valid convergence_axiom"
  unfolding convergence_axiom_def valid_impl
proof (clarify)
  fix I \<nu>
  assume "\<nu> \<in> fml_sem I ([[ chpconv** ]] Forall (Rv vvar)
    (((RVar vvar) >\<^sub>R (Number 0) && PhxOf (RVar vvar)) \<rightarrow> \<langle>chpconv\<rangle>PhxOf (Dec (RVar vvar))))"

  hence assm: "\<And>\<tau> \<omega> x. (\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I (chpconv**) \<Longrightarrow> x > 0 \<Longrightarrow> 
    rrepv (\<omega> @@ \<tau>) vvar x \<in> fml_sem I (PhxOf (RVar vvar) \<rightarrow> \<langle> chpconv \<rangle> (PhxOf (Dec (RVar vvar))))"
      by (fastforce simp add: sorteq_def)

  have "\<And>x. rrepv \<nu> vvar x \<in> fml_sem I (PhxOf (RVar vvar)) \<Longrightarrow> 
      \<exists>\<tau> \<omega>. (rrepv \<nu> vvar x, \<tau>, Fin \<omega>) \<in> chp_sem I (Repeat chpconv (nat (ceiling x))) 
        \<and> (\<exists>y \<le> 0. rrepv (\<omega> @@ \<tau>) vvar y \<in> fml_sem I (PhxOf (RVar vvar)))"
  proof -
    fix x
    assume "rrepv \<nu> vvar x \<in> fml_sem I (PhxOf (RVar vvar))"
    then obtain \<tau> \<omega>
      where "(rrepv \<nu> vvar x, \<tau>, Fin \<omega>) \<in> chp_sem I (Repeat chpconv (nat (ceiling x)))"
        and "rrepv (\<omega> @@ \<tau>) vvar (x - nat (ceiling x)) \<in> fml_sem I (PhxOf (RVar vvar))"
      using assm convergence_lemma by blast
    moreover have "x - nat (ceiling x) \<le> 0" by linarith
    ultimately show "?thesis x" by blast
  qed

  thus "\<nu> \<in> fml_sem I (Forall (Rv vvar) (PhxOf (RVar vvar) \<rightarrow> \<langle>chpconv**\<rangle>aconv_exists))"
    by (fastforce simp add: sorteq_def linhis_rtcl_eq_iteration chp_sem_Repeat)
qed

lemma rrepv_A: "rrepv \<nu> vvar d \<in> fml_sem I A \<Longrightarrow> \<nu> \<in> fml_sem I A" by (simp add: rrepv_def args_sem_def)

lemma action_convergence_lemma:
  "\<nu> \<in> fml_sem I A \<Longrightarrow>
  (\<And>\<tau> \<omega> d. (\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I (chpconv**) \<Longrightarrow>
      assm_set \<nu> \<tau> \<subseteq> fml_sem I A \<Longrightarrow>
      d > 0 \<Longrightarrow>
      rrepv (\<omega> @@ \<tau>) vvar d \<in> fml_sem I (PhxOf (RVar vvar) \<rightarrow> AcDia chpconv A FF (PhxOf (Dec (RVar vvar))))) \<Longrightarrow>
  rrepv \<nu> vvar d \<in> fml_sem I (PhxOf (RVar vvar)) \<Longrightarrow>
  \<exists>\<tau> \<omega>. (rrepv \<nu> vvar d, \<tau>, Fin \<omega>) \<in> chp_sem I (Repeat chpconv (nat (ceiling d))) \<and>
        rrepv (\<omega> @@ \<tau>) vvar (d - nat (ceiling d)) \<in> fml_sem I (PhxOf (RVar vvar)) \<and>
        assm_set (rrepv \<nu> vvar d) \<tau> \<subseteq> fml_sem I A"
proof (induction "nat (ceiling d)" arbitrary: d \<nu>)
  case 0
  hence "(rrepv \<nu> vvar d, [], Fin (rrepv \<nu> vvar d)) \<in> chp_sem I (Repeat chpconv (nat (ceiling d))) \<and>
        rrepv (rrepv \<nu> vvar d @@ []) vvar (d - nat (ceiling d)) \<in> fml_sem I (PhxOf (RVar vvar)) \<and>
        assm_set (rrepv \<nu> vvar d) [] \<subseteq> fml_sem I A"
    by (simp add: rrepv_def args_sem_def g_assm_set_def)
  thus ?case by fastforce
next
  case (Suc n)

  (* obtain alpha run *)

  hence "d > 0" by linarith
  moreover have "(\<nu>, [], Fin \<nu>) \<in> chp_sem I (chpconv**)"
    by (simp add: rtcl_linhis.rtcl_linhis_base_id)
  moreover have "assm_set \<nu> [] \<subseteq> fml_sem I A"
    using Suc(3) by (simp add: g_assm_set_def)
  ultimately have "rrepv (\<nu> @@ []) vvar d \<in> fml_sem I (PhxOf (RVar vvar) \<rightarrow> AcDia chpconv A FF (PhxOf (Dec (RVar vvar))))"
    using Suc(4) by blast
  hence "rrepv \<nu> vvar d \<in> fml_sem I (AcDia chpconv A FF (PhxOf (Dec (RVar vvar))))"
    using Suc(5) by simp
  then obtain \<tau>\<^sub>1 \<kappa>
    where run: "(rrepv \<nu> vvar d, \<tau>\<^sub>1, Fin \<kappa>) \<in> chp_sem I chpconv"
      and assm: "assm_set (rrepv \<nu> vvar d) \<tau>\<^sub>1 \<subseteq> fml_sem I A"
      and phi_dec: "\<kappa> @@ \<tau>\<^sub>1 \<in> fml_sem I (PhxOf (Dec (RVar vvar)))"
    by (force simp add: FF_def)

  (* obtain alpha* run *)

  hence kappa_vvar: "(rrepv \<nu> vvar d) $$ Rv vvar = \<kappa> $$ Rv vvar"
    by (meson Vagree_def bound_effect_property_short vvar_notin_BVP_chpconv)

  have "rrepv (\<kappa> @@ \<tau>\<^sub>1) vvar (d - 1) \<in> fml_sem I (PhxOf (RVar vvar))" 
    using kappa_vvar PhxOf_Dec phi_dec by force

  moreover have "n = nat (ceiling (d - 1))" using Suc(2) by simp
  moreover have "\<And>\<tau> \<omega> d. (\<kappa> @@ \<tau>\<^sub>1, \<tau>, Fin \<omega>) \<in> chp_sem I chpconv** \<Longrightarrow>
        assm_set (\<kappa> @@ \<tau>\<^sub>1) \<tau> \<subseteq> fml_sem I A \<Longrightarrow>
        d > 0 \<Longrightarrow>
        rrepv (\<omega> @@ \<tau>) vvar d \<in> fml_sem I (PhxOf (RVar vvar) \<rightarrow> AcDia chpconv A FF (PhxOf (Dec (RVar vvar))))"
  proof -
    let ?d = "stR \<nu> vvar"
    fix \<tau>\<^sub>2 :: rectrace
    fix \<omega> :: state
    fix d' :: real
    assume "(\<kappa> @@ \<tau>\<^sub>1, \<tau>\<^sub>2, Fin \<omega>) \<in> chp_sem I chpconv**"
    moreover have "\<And>\<L>. wf_chp \<L> (chpconv**)" by simp
    ultimately obtain \<omega>' where omega: "\<omega> = \<omega>' @@ \<tau>\<^sub>1" and "(\<kappa>, \<tau>\<^sub>2, Fin \<omega>') \<in> chp_sem I (chpconv**)"
      using run_suffix_of_final by blast

    hence "(rrepv \<nu> vvar d, \<tau>\<^sub>1 @ \<tau>\<^sub>2, Fin \<omega>') \<in> chp_sem I (chpconv**)"
      using run rtcl_linhis.rtcl_linhis_continue by fastforce
    hence "(rrepv (rrepv \<nu> vvar d) vvar ?d, \<tau>\<^sub>1 @ \<tau>\<^sub>2, Fin (rrepv \<omega>' vvar ?d)) \<in> chp_sem I (chpconv**)"
      by (rule chpconv_loop_vvar_cong)
    hence full_run: "(\<nu>, \<tau>\<^sub>1 @ \<tau>\<^sub>2, Fin (rrepv \<omega>' vvar ?d)) \<in> chp_sem I (chpconv**)" by simp

    assume "assm_set (\<kappa> @@ \<tau>\<^sub>1) \<tau>\<^sub>2 \<subseteq> fml_sem I A"
    moreover have "assm_set \<kappa> \<tau>\<^sub>1 \<subseteq> fml_sem I A" using run assm assm_set_forward_transfer by blast
    ultimately have "assm_set \<kappa> (\<tau>\<^sub>1 @ \<tau>\<^sub>2) \<subseteq> fml_sem I A" using assm_union by fastforce
    hence "assm_set (rrepv \<nu> vvar d) (\<tau>\<^sub>1 @ \<tau>\<^sub>2) \<subseteq> fml_sem I A"
      using run assm_set_backward_transfer by blast

    moreover have "\<And>\<tau>'. rrepv \<nu> vvar d @@ \<tau>' \<in> fml_sem I A \<Longrightarrow> \<nu> @@ \<tau>' \<in> fml_sem I A"
      using rrepv_A rrepv_sttconc_rev by simp
    ultimately have "assm_set \<nu> (\<tau>\<^sub>1 @ \<tau>\<^sub>2) \<subseteq> fml_sem I A" unfolding g_assm_set_def by blast

    moreover assume "d' > 0"
    ultimately have "rrepv (rrepv \<omega>' vvar ?d @@ (\<tau>\<^sub>1 @ \<tau>\<^sub>2)) vvar d' \<in> fml_sem I (PhxOf (RVar vvar) \<rightarrow> AcDia chpconv A FF (PhxOf (Dec (RVar vvar))))"
      using full_run Suc.prems(2) by blast
    thus "?thesis \<tau>\<^sub>2 \<omega> d'" using rrepv_sttconc_rev rrepv_idem sttconc_dist_app omega by simp
  qed

  moreover have "\<kappa> @@ \<tau>\<^sub>1 \<in> fml_sem I A"
    using assm run assm_set_forward_transfer g_assm_set_def by blast

  ultimately have "\<exists>\<tau> \<omega>. (rrepv (\<kappa> @@ \<tau>\<^sub>1) vvar (d - 1), \<tau>, Fin \<omega>) \<in> chp_sem I (Repeat chpconv n) \<and>
          assm_set (rrepv (\<kappa> @@ \<tau>\<^sub>1) vvar (d - 1)) \<tau> \<subseteq> fml_sem I A \<and>
          rrepv (\<omega> @@ \<tau>) vvar (d - 1 - n) \<in> fml_sem I (PhxOf (RVar vvar))"
    using Suc(1) by blast

  then obtain \<tau>\<^sub>2 \<omega>
    where "(rrepv \<kappa> vvar (d - 1) @@ \<tau>\<^sub>1, \<tau>\<^sub>2, Fin \<omega>) \<in> chp_sem I (Repeat chpconv n)"
      and assm2: "assm_set (rrepv \<kappa> vvar (d - 1) @@ \<tau>\<^sub>1) \<tau>\<^sub>2 \<subseteq> fml_sem I A"
      and phi: "rrepv \<omega> vvar (d - 1 - n) @@ \<tau>\<^sub>2 \<in> fml_sem I (PhxOf (RVar vvar))"
    using rrepv_sttconc_rev by auto

  (* combine alpha and alpha* run *)

  moreover have "\<And>\<L>. wf_chp \<L> (Repeat chpconv n)" using wf_Repeat by force
  ultimately obtain \<omega>'
    where omega: "\<omega> = \<omega>' @@ \<tau>\<^sub>1"
      and run2: "(rrepv \<kappa> vvar (d - 1), \<tau>\<^sub>2, Fin \<omega>') \<in> chp_sem I (Repeat chpconv n)"
    using run_suffix_of_final wf_Repeat by blast

  hence "(rrepv (rrepv \<kappa> vvar (d - 1)) vvar d, \<tau>\<^sub>2, Fin (rrepv \<omega>' vvar d)) \<in>  chp_sem I (Repeat chpconv n)"
    using chpconv_rep_vvar_cong by blast
  hence "(\<kappa>, \<tau>\<^sub>2, Fin (rrepv \<omega>' vvar d)) \<in>  chp_sem I (Repeat chpconv n)" using kappa_vvar by simp

  hence run3: "(rrepv \<nu> vvar d, \<tau>\<^sub>1 @ \<tau>\<^sub>2, Fin (rrepv \<omega>' vvar d)) \<in> chp_sem I (Repeat chpconv (Suc n))"
    using run by auto

  have "\<And>\<tau>'. (rrepv \<kappa> vvar (d - 1) @@ \<tau>\<^sub>1) @@ \<tau>' \<in> fml_sem I A \<Longrightarrow> (\<kappa> @@ \<tau>\<^sub>1) @@ \<tau>' \<in> fml_sem I A"
    using rrepv_sttconc_rev rrepv_A by simp
  moreover have "\<And>\<tau>'. (\<kappa> @@ \<tau>\<^sub>1) @@ \<tau>' \<in> fml_sem I A \<Longrightarrow> (rrepv \<nu> vvar d @@ \<tau>\<^sub>1) @@ \<tau>' \<in> fml_sem I A"
    by (metis communicative_coincidence(2) sttconc_dist_app wf_A rrepv_sttconc_rev run)
  ultimately have "assm_set (rrepv \<nu> vvar d @@ \<tau>\<^sub>1) \<tau>\<^sub>2 \<subseteq> fml_sem I A"
    using assm2 unfolding g_assm_set_def by auto
  hence "assm_set (rrepv \<nu> vvar d) (\<tau>\<^sub>1 @ \<tau>\<^sub>2) \<subseteq> fml_sem I A" using assm_union assm by blast
  moreover from omega have "rrepv (rrepv \<omega>' vvar d @@ (\<tau>\<^sub>1 @ \<tau>\<^sub>2)) vvar (d - 1 - n) \<in> fml_sem I (PhxOf (RVar vvar))"
    using phi rrepv_sttconc_rev sttconc_dist_app rrepv_idem by simp
  moreover have "d - 1 - n = d - Suc n" by simp
  ultimately show ?case using run3 Suc(2) by auto
qed

lemma action_convergence_valid: "valid action_convergence_axiom"
  unfolding action_convergence_axiom_def valid_impl
proof (rule; rule)
  fix I \<nu>
  assume "\<nu> \<in> fml_sem I (A &&
                 AcBox chpconv** A TT
                  (Forall (Rv vvar)
                    ((RVar vvar >\<^sub>R Number 0 &&
                     PhxOf (RVar vvar)) \<rightarrow>
                     AcDia chpconv A FF (PhxOf (Dec (RVar vvar))))))"

  hence assm: "\<nu> \<in> fml_sem I A" and step: "\<nu> \<in> fml_sem I (AcBox chpconv** A TT
                  (Forall (Rv vvar)
                    ((RVar vvar >\<^sub>R Number 0 &&
                     PhxOf (RVar vvar)) \<rightarrow>
                     AcDia chpconv A FF (PhxOf (Dec (RVar vvar))))))"
    by simp_all

  have "\<And>d. rrepv \<nu> vvar d \<in> fml_sem I (PhxOf (RVar vvar)) \<Longrightarrow>
  \<exists>\<tau> \<omega>. (rrepv \<nu> vvar d, \<tau>, Fin \<omega>) \<in> chp_sem I (Repeat chpconv (nat (ceiling d))) \<and>
        (\<exists>y \<le> 0. rrepv (\<omega> @@ \<tau>) vvar y \<in> fml_sem I (PhxOf (RVar vvar))) \<and>
        assm_set (rrepv \<nu> vvar d) \<tau> \<subseteq> fml_sem I A"
  proof -
    fix d
    from step have "\<And>\<tau> \<omega> d. (\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I (chpconv**) \<Longrightarrow>
    assm_set \<nu> \<tau> \<subseteq> fml_sem I A \<Longrightarrow>
    d > 0 \<Longrightarrow>
    rrepv (\<omega> @@ \<tau>) vvar d \<in> fml_sem I (PhxOf (RVar vvar) \<rightarrow> AcDia chpconv A FF (PhxOf (Dec (RVar vvar))))"
      by (fastforce simp add: sorteq_def)

    hence "\<And>d. rrepv \<nu> vvar d \<in> fml_sem I (PhxOf (RVar vvar)) \<Longrightarrow>
          \<exists>\<tau> \<omega>. (rrepv \<nu> vvar d, \<tau>, Fin \<omega>) \<in> chp_sem I (Repeat chpconv (nat (ceiling d))) \<and>
                rrepv (\<omega> @@ \<tau>) vvar (d - nat (ceiling d)) \<in> fml_sem I (PhxOf (RVar vvar)) \<and>
                assm_set (rrepv \<nu> vvar d) \<tau> \<subseteq> fml_sem I A"
      using assm action_convergence_lemma by simp

    moreover assume "rrepv \<nu> vvar d \<in> fml_sem I (PhxOf (RVar vvar))"
    ultimately obtain \<tau> \<omega>
      where "(rrepv \<nu> vvar d, \<tau>, Fin \<omega>) \<in> chp_sem I (Repeat chpconv (nat (ceiling d)))"
        and "rrepv (\<omega> @@ \<tau>) vvar (d - nat (ceiling d)) \<in> fml_sem I (PhxOf (RVar vvar))"
        and "assm_set (rrepv \<nu> vvar d) \<tau> \<subseteq> fml_sem I A"
      by blast
    moreover have "d - nat (ceiling d) \<le> 0" by linarith
    ultimately show "?thesis d" by blast
  qed

  thus "\<nu> \<in> fml_sem I
                 (Forall (Rv vvar)
                   (PhxOf (RVar vvar) \<rightarrow> AcDia chpconv** A FF aconv_exists))"
    by (fastforce simp add: sorteq_def linhis_rtcl_eq_iteration chp_sem_Repeat)
qed



subsection \<open>Soundness of the Axiomatic Properties of the Computational Domain\<close>

lemma history_extension_valid: "valid history_extension_axiom"
  unfolding history_extension_axiom_def valid_impl
  by (auto simp add: sttconc_def stT_ini_eq_fin[where \<alpha>=chp1] byrec_non_rec_empty)

lemma sassm_set_eq_Acl:
  assumes "stT \<nu> hid0 = stT \<nu> rec"
  assumes "byrec \<tau> rec = tflat \<tau>"
  assumes "strict_assm_set \<nu> \<tau> \<subseteq> fml_sem I A"
  shows "\<nu> @@ \<tau> \<in> fml_sem I (Acl SPref)"
proof -
  let ?A = "Aof (TVar hid')"

  have "\<And>\<tau>'. stT \<nu> rec \<preceq> \<tau>' \<Longrightarrow> \<tau>' \<prec> (stT \<nu> rec @ tflat \<tau>)  
    \<Longrightarrow> upds (\<nu> @@ \<tau>) (Tv hid') (Tp \<tau>') \<in> fml_sem I ?A"
  proof -
    fix \<tau>'
    assume "\<tau>' \<prec> (stT \<nu> rec @ tflat \<tau>)"
    then obtain \<tau>\<^sub>0 where spref: "\<tau>\<^sub>0 \<prec> (stT \<nu> rec @ tflat \<tau>)" and peq: "\<tau>' = \<tau>\<^sub>0" by simp
    moreover assume "(stT \<nu> rec) \<preceq> \<tau>'"
    ultimately have "stT \<nu> rec \<preceq> \<tau>\<^sub>0" by simp

    then obtain \<tau>\<^sub>1 where tau0: "\<tau>\<^sub>0 = stT \<nu> rec @ \<tau>\<^sub>1" unfolding prefix_def by auto
    hence "\<tau>\<^sub>1 \<prec> tflat \<tau>" using spref by (simp add: prefix_order.less_le)
    then obtain \<tau>\<^sub>2 where tau2: "\<tau>\<^sub>2 \<prec> tflat \<tau>" and tau2_proj: "\<tau>\<^sub>2 = \<tau>\<^sub>1"
      unfolding tfilter_def by simp
    then obtain \<rho>\<^sub>2 where "\<tau>\<^sub>2 @ \<rho>\<^sub>2 = tflat \<tau>" and nonempty: "\<rho>\<^sub>2 \<noteq> []"
      by (auto simp add: strict_prefix_def prefix_def)
    hence "addrec \<tau>\<^sub>2 rec @ addrec \<rho>\<^sub>2 rec = \<tau>" 
      by (metis addrec_dist_app addrec_inv_tflat_urec assms(2))
    hence "addrec \<tau>\<^sub>2 rec \<prec> \<tau>"
      using nonempty addrec_empty_conv pref_spref_non_empty_extension by blast
    hence "upds (\<nu> @@ \<tau>) (Tv hid') (Tp (stT (\<nu> @@ addrec \<tau>\<^sub>2 rec) rec)) \<in> fml_sem I ?A"
      using assms(3) unfolding g_assm_set_def by (auto simp add: trepv_def args_sem_def)
    moreover have "stT (\<nu> @@ addrec \<tau>\<^sub>2 rec) rec = stT \<nu> rec @ \<tau>\<^sub>2" by (simp add: sttconc_def)
    ultimately have "upds (\<nu> @@ \<tau>) (Tv hid') (Tp (stT \<nu> rec @ \<tau>\<^sub>2)) \<in> fml_sem I ?A"
      unfolding strict_prefix_def tau0 sttconc_def byrec_addrec by simp
    thus "upds (\<nu> @@ \<tau>) (Tv hid') (Tp \<tau>') \<in> fml_sem I ?A"
      using tau2_proj by (auto simp add: trepv_def args_sem_def tau0 peq)
  qed
  hence "\<And>\<tau>'. (stT \<nu> rec) \<preceq> \<tau>' \<Longrightarrow> \<tau>' \<prec> (stT \<nu> rec @ tflat \<tau>) 
    \<Longrightarrow> upds (\<nu> @@ \<tau>) (Tv hid') (Tp \<tau>') \<in> fml_sem I ?A"
    by (simp add: trepv_def sttconc_def args_sem_def) 
  thus ?thesis unfolding Acl_def sttconc_def 
    apply (auto simp add:  assms byrec_non_rec_empty sorteq_def)
    by (meson append_prefixD)
qed                                                                              

lemma assm_set_eq_Acl: 
  assumes "stT \<nu> hid0 = stT \<nu> rec"
  assumes "byrec \<tau> rec = tflat \<tau>"
  assumes "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I chp1"
  assumes "assm_set \<nu> \<tau> \<subseteq> fml_sem I A"
  shows "\<omega> @@ \<tau> \<in> fml_sem I (Acl Pref)"
proof -                                                                                                                             
  let ?A = "Aof (TVar hid')"

  have "\<And>\<tau>'. stT \<nu> rec \<preceq> \<tau>' \<Longrightarrow> \<tau>' \<preceq> (stT \<nu> rec @ tflat \<tau>) 
    \<Longrightarrow> upds (\<nu> @@ \<tau>) (Tv hid') (Tp \<tau>') \<in> fml_sem I ?A"
  proof -
    fix \<tau>'
    assume "\<tau>' \<preceq> (stT \<nu> rec @ tflat \<tau>)"
    then obtain \<tau>\<^sub>0 where spref: "\<tau>\<^sub>0 \<preceq> (stT \<nu> rec @ tflat \<tau>)" and peq: "\<tau>' = \<tau>\<^sub>0" by simp
    moreover assume "stT \<nu> rec \<preceq> \<tau>'"
    ultimately have "stT \<nu> rec \<preceq> \<tau>\<^sub>0" by simp

    then obtain \<tau>\<^sub>1 where tau0: "\<tau>\<^sub>0 = stT \<nu> rec @ \<tau>\<^sub>1" unfolding prefix_def by auto
    hence "\<tau>\<^sub>1 \<preceq> tflat \<tau>" using spref by (simp add: prefix_order.less_le)
    then obtain \<tau>\<^sub>2 where tau2: "\<tau>\<^sub>2 \<preceq> tflat \<tau>" and tau2_proj: "\<tau>\<^sub>2 = \<tau>\<^sub>1"
      unfolding tfilter_def by blast
    hence "addrec \<tau>\<^sub>2 rec \<preceq> \<tau>"
      by (metis addrec_def addrec_inv_tflat_urec assms(2) map_mono_prefix)
    hence "upds (\<nu> @@ \<tau>) (Tv hid') (Tp (stT (\<nu> @@ addrec \<tau>\<^sub>2 rec) rec)) \<in> fml_sem I ?A"
      using assms(4) unfolding g_assm_set_def by (auto simp add: trepv_def args_sem_def)
    moreover have "stT (\<nu> @@ addrec \<tau>\<^sub>2 rec) rec = stT \<nu> rec @ \<tau>\<^sub>2" by (simp add: sttconc_def)
    ultimately have "upds (\<nu> @@ \<tau>) (Tv hid') (Tp (stT \<nu> rec @ \<tau>\<^sub>2)) \<in> fml_sem I ?A"
      unfolding strict_prefix_def tau0 sttconc_def by simp
    thus "upds (\<nu> @@ \<tau>) (Tv hid') (Tp \<tau>') \<in> fml_sem I ?A"
      using tau2_proj by (auto simp add: trepv_def args_sem_def tau0 peq)
  qed
  moreover have no_tvars_bound: "\<And>h. stT \<omega> h = stT \<nu> h"
    by (metis bound_effect_on_state(2) Vagree_alltvars assms(3))
  ultimately have "\<And>\<tau>'. (stT \<omega> rec) \<preceq> \<tau>' \<Longrightarrow> \<tau>' \<preceq> (stT \<omega> rec @ tflat \<tau>) 
    \<Longrightarrow> upds (\<omega> @@ \<tau>) (Tv hid') (Tp \<tau>') \<in> fml_sem I ?A"
    by (simp add: trepv_def sttconc_def args_sem_def)
  thus ?thesis unfolding Acl_def sttconc_def 
    using no_tvars_bound assms byrec_non_rec_empty sorteq_def by auto
qed

lemma assumption_closure_valid: "valid assumption_closure_axiom"
  unfolding assumption_closure_axiom_def valid_impl
proof (rule, rule, rule ac_box_by_ac_casesI, goal_cases commit post)
  case (commit I \<nu> \<tau> \<omega>)
  hence "byrec \<tau> rec = tflat \<tau>" using trecs_bounded by simp
  then show ?case using commit sassm_set_eq_Acl by simp
next
  case (post I \<nu> \<tau> \<omega>)
  hence "byrec \<tau> rec = tflat \<tau>" using trecs_bounded by simp
  then show ?case using post assm_set_eq_Acl by simp
qed
  


subsection \<open>Soundness of Parallel Injection\<close>

definition noninterference :: "binterp \<Rightarrow> chp \<Rightarrow> chp \<Rightarrow> fml \<Rightarrow> bool"
  where "noninterference J \<beta> \<alpha> \<psi> \<equiv> FVE J \<psi> \<inter> BVP J \<beta> \<subseteq> \<V>\<^sub>\<mu> \<union> \<iota>\<^sub>T \<V>\<^sub>T \<and>
                                    CNE J \<psi> `` (RecP J (\<alpha> par \<beta>)) \<inter> CN J \<beta> \<subseteq> CN J \<alpha>"

paragraph \<open>Conincidence properties for noninterfering parallel injection\<close>

lemma rec_tfilter_dist_cons: "(\<rho> # \<tau>) \<Down> Y = (if (recvar \<rho>, along \<rho>) \<in> Y then \<rho> # (\<tau> \<Down> Y) else \<tau> \<Down> Y)"
  by (simp add: rec_tfilter_def)

lemma rec_tfilter_hd_in [simp]: "(recvar \<rho>, along \<rho>) \<in> Y \<Longrightarrow> (\<rho> # \<tau>) \<Down> Y = \<rho> # \<tau> \<Down> Y" 
  by (simp add: rec_tfilter_def)

lemma rec_tfilter_hd_not_in [simp]: "(recvar \<rho>, along \<rho>) \<notin> Y \<Longrightarrow> (\<rho> # \<tau>) \<Down> Y = \<tau> \<Down> Y" 
  by (simp add: rec_tfilter_def)

lemma tfilter_rec_tfilter_commute: "(\<tau> \<down> Y) \<Down> YY = (\<tau> \<Down> YY) \<down> Y"
  apply (induction \<tau>)
  by (simp_all add: rec_tfilter_dist_cons tfilter_dist_cons)


lemma bound_effect_recorders: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> h \<in> -RecP (\<pi>\<^sub>I I) \<alpha> \<Longrightarrow> byrec \<tau> h = []"
  unfolding RecP_def by auto

lemma trecs_subseteq_BVP:
  assumes run: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha>"
  shows "trecs \<tau> \<subseteq> RecP (\<pi>\<^sub>I I) \<alpha>"
proof
  fix h
  assume "h \<in> trecs \<tau>"
  hence "byrec \<tau> h \<noteq> []" using trecs_equiv_byrec by simp
  thus "h \<in> RecP (\<pi>\<^sub>I I) \<alpha>" using bound_effect_recorders run by blast
qed

lemma com_coincides_by_noninterference:
  assumes noninter: "noninterference (\<pi>\<^sub>I I) \<beta> \<alpha> \<psi> "
  assumes run: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I (\<alpha> par \<beta>)"
  shows "let Y\<^sub>\<alpha> = CN (\<pi>\<^sub>I I) \<alpha>; Y\<^sub>\<psi> = CNE (\<pi>\<^sub>I I) \<psi> in (\<tau> \<down> Y\<^sub>\<alpha>) \<Down> Y\<^sub>\<psi> = \<tau> \<Down> Y\<^sub>\<psi>"
proof -
  have "tchans \<tau> \<subseteq> (CN (\<pi>\<^sub>I I) \<alpha> \<union> CN (\<pi>\<^sub>I I) \<beta>)" using run tfilter_idem_tchans_overapprox by auto
  moreover have "trecs \<tau> \<subseteq> RecP (\<pi>\<^sub>I I) (\<alpha> par \<beta>)" using trecs_subseteq_BVP run by blast
  ultimately show ?thesis
  proof (induction \<tau>, simp)
    case (Cons \<rho> \<tau>)
    show ?case
    proof (cases "along \<rho> \<in> (CNE (\<pi>\<^sub>I I) \<psi> `` (RecP (\<pi>\<^sub>I I) (\<alpha> par \<beta>)))")
      case True
      have "along \<rho> \<in> CN (\<pi>\<^sub>I I) \<alpha>"
      proof (cases "along \<rho> \<notin> CN (\<pi>\<^sub>I I) \<beta>")
        case True
        hence "along \<rho> \<in> CN (\<pi>\<^sub>I I) \<alpha> \<union> CN (\<pi>\<^sub>I I) \<beta>" using Cons.prems by simp
        thus ?thesis using True by blast
      next
        case False
        thus ?thesis using noninter True unfolding noninterference_def by auto
      qed
      thus ?thesis using Cons by (simp add: rec_tfilter_dist_cons) 
    next
      case False
      moreover have "recvar \<rho> \<in> RecP (\<pi>\<^sub>I I) (\<alpha> par \<beta>)" using Cons by auto
      ultimately have "(recvar \<rho>, along \<rho>) \<notin> CNE (\<pi>\<^sub>I I) \<psi>" by auto
      thus ?thesis using Cons by (simp add: tfilter_rec_tfilter_commute)
    qed
  qed
qed

lemma sttconc_diff_byrec_non_empty: "(\<nu> @@ \<tau>) $$ (Tv h) \<noteq> \<nu> $$ (Tv h) \<Longrightarrow> byrec \<tau> h \<noteq> []"
  using stT_sttconc_neq_iff_byrec by force










lemma trecs_proj: "trecs \<tau> \<subseteq> X \<Longrightarrow> trecs (\<tau> \<down> Y) \<subseteq> X"
  apply (induction \<tau>)
  by (simp_all add: tfilter_dist_cons)

lemma rec_tfilter_sfilter_cong: "\<rho> \<Down> Y = \<tau> \<Down> Y \<Longrightarrow> sfilter (\<nu> @@ \<rho>) Y = sfilter (\<nu> @@ \<tau>) Y"
  apply (rule state_eq_by_sortI)
  by (simp_all add: sfilter_dist_sttconc stT_sttconc_dist)



lemma noninterference_com_formulas:
  assumes noninter: "noninterference (\<pi>\<^sub>I I) \<beta> \<alpha> \<psi>"
  assumes run: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I (\<alpha> par \<beta>)"
  shows "\<nu> @@ (\<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha>)) \<in> fml_sem I \<psi> = (\<nu> @@ \<tau> \<in> fml_sem I \<psi>)"
proof -
  let ?Y\<^sub>\<psi> = "CNE (\<pi>\<^sub>I I) \<psi>"
  let ?Y\<^sub>\<alpha> = "CN (\<pi>\<^sub>I I) \<alpha>"

  have "(\<tau> \<down> ?Y\<^sub>\<alpha>) \<Down> ?Y\<^sub>\<psi> = \<tau> \<Down> ?Y\<^sub>\<psi>" by (meson noninter com_coincides_by_noninterference run)
  hence "sfilter (\<nu> @@ (\<tau> \<down> ?Y\<^sub>\<alpha>)) ?Y\<^sub>\<psi> = sfilter (\<nu> @@ \<tau>) ?Y\<^sub>\<psi>" using rec_tfilter_sfilter_cong by blast
  hence "VCagree (\<nu> @@ (\<tau> \<down> ?Y\<^sub>\<alpha>)) (\<nu> @@ \<tau>) (FNE (\<pi>\<^sub>I I) \<psi>)" by (simp add: VCagree_def FNE_partition)
  thus "((\<nu> @@ (\<tau> \<down> ?Y\<^sub>\<alpha>)) \<in> fml_sem I \<psi>) = ((\<nu> @@ \<tau>) \<in> fml_sem I \<psi>)" using coincidence_fml by auto
qed                                      

lemma run_and_subrun_agree_on_tvars:
  assumes run: "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I (\<alpha> par \<beta>)"
  assumes subrun: "(\<nu>, \<tau> \<down> CN (\<pi>\<^sub>I I) \<alpha>, Fin \<omega>\<^sub>\<alpha>) \<in> chp_sem I \<alpha>"
  shows "Vagree \<omega>\<^sub>\<alpha> \<omega> (\<iota>\<^sub>T \<V>\<^sub>T)"
proof -
  have "Vagree \<omega>\<^sub>\<alpha> \<nu> (\<iota>\<^sub>T \<V>\<^sub>T)" using Vagree_sym subrun bound_effect_on_state by blast
  moreover have "Vagree \<nu> \<omega> (\<iota>\<^sub>T \<V>\<^sub>T)" using run bound_effect_on_state by blast
  ultimately show "Vagree \<omega>\<^sub>\<alpha> \<omega> (\<iota>\<^sub>T \<V>\<^sub>T)" using Vagree_trans by fastforce
qed

lemma noninterference_post:
  assumes noninter: "noninterference (\<pi>\<^sub>I I) \<beta> \<alpha> \<psi>"
  assumes run: "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I (\<alpha> par \<beta>)"
  assumes alpharun: "(\<nu>, \<tau> \<down> CN (\<pi>\<^sub>I I) \<alpha>, Fin \<omega>\<^sub>\<alpha>) \<in> chp_sem I \<alpha>"
  assumes betarun: "(\<nu>, \<tau> \<down> CN (\<pi>\<^sub>I I) \<beta>, Fin \<omega>\<^sub>\<beta>) \<in> chp_sem I \<beta>"
  assumes merge: "\<omega> = lmerge \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> (BVP (\<pi>\<^sub>I I) \<alpha>)"
  assumes tsync: "Vagree \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> \<V>\<^sub>\<mu>"
  shows "\<omega>\<^sub>\<alpha> @@ (\<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha>)) \<in> fml_sem I \<psi> = (\<omega> @@ \<tau> \<in> fml_sem I \<psi>)"
proof -
  let ?X = "RecP (\<pi>\<^sub>I I) (\<alpha> par \<beta>)"
  let ?Y\<^sub>\<psi> = "CNE (\<pi>\<^sub>I I) \<psi>"
  let ?Y\<^sub>\<alpha> = "CN (\<pi>\<^sub>I I) \<alpha>"

  (* \<omega>\<^sub>\<beta> = \<omega> on BV(\<alpha>)\<^sup>C *)
  have beta_on_alpha_compl: "Vagree \<omega>\<^sub>\<beta> \<omega> (-BVP (\<pi>\<^sub>I I) \<alpha>)" using merge Vagree_sym_rel lmerge_vagree by blast

  (* \<omega>\<^sub>\<alpha> = \<omega> on BV(\<alpha>) \<inter> BV(\<beta>)\<^sup>C *)
  have on_alpha: "Vagree \<omega>\<^sub>\<alpha> \<omega> ((BVP (\<pi>\<^sub>I I) \<alpha>) \<inter> (-BVP (\<pi>\<^sub>I I) \<beta>))"
    using Vagree_or Vagree_sym_rel Vagreebot_only_Fin merge lmerge_vagree by metis

  (* \<omega>\<^sub>\<alpha> = \<omega> on BV(\<alpha>)\<^sup>C \<inter> BV(\<beta>)\<^sup>C *)
  moreover have on_alpha_compl: "Vagree \<omega>\<^sub>\<alpha> \<omega> ((-BVP (\<pi>\<^sub>I I) \<alpha>) \<inter> (-BVP (\<pi>\<^sub>I I) \<beta>))"  
  proof -
    have "Vagree \<omega>\<^sub>\<alpha> \<nu> (-BVP (\<pi>\<^sub>I I) \<alpha>)" using Vagree_sym alpharun bound_effect_property_short by presburger
    moreover have "Vagree \<nu> \<omega>\<^sub>\<beta> (-BVP (\<pi>\<^sub>I I) \<beta>)" using betarun bound_effect_property_short Vagree_and by blast     
    ultimately show ?thesis using Vagree_def beta_on_alpha_compl by force
  qed

  (* \<omega>\<^sub>\<alpha> = \<omega> on BV(\<beta>)\<^sup>C *)
  ultimately have alpha_on_beta_compl: "Vagree \<omega>\<^sub>\<alpha> \<omega> (-BVP (\<pi>\<^sub>I I) \<beta>)" using Vagree_def by auto

  (* \<omega>\<^sub>\<alpha> = \<omega> on {\<mu>, \<mu>'} *)
  moreover have on_gtset: "Vagree \<omega>\<^sub>\<alpha> \<omega> \<V>\<^sub>\<mu>" by (metis Vagree_sym_rel Vagree_trans inf.idem merge lmerge_bound_vars tsync)

  (* \<omega>\<^sub>\<alpha> = \<omega> on V\<^sub>T *)
  moreover have on_tvars: "Vagree \<omega>\<^sub>\<alpha> \<omega> (\<iota>\<^sub>T \<V>\<^sub>T)" by (meson alpharun run run_and_subrun_agree_on_tvars)

  ultimately have "Vagree \<omega>\<^sub>\<alpha> \<omega> ((-BVP (\<pi>\<^sub>I I) \<beta>) \<union> \<V>\<^sub>\<mu> \<union> \<iota>\<^sub>T \<V>\<^sub>T)" using Vagree_union by blast
  hence "Vagree \<omega>\<^sub>\<alpha> \<omega> (FVE (\<pi>\<^sub>I I) \<psi>)" by (metis Un_assoc Vagree_antimon noninter noninterference_def shunt1)
  moreover have "sfilter (\<omega>\<^sub>\<alpha> @@ (\<tau> \<down> ?Y\<^sub>\<alpha>)) ?Y\<^sub>\<psi> = sfilter (\<omega>\<^sub>\<alpha> @@ \<tau>) ?Y\<^sub>\<psi>"
  proof -
    have "(\<tau> \<down> ?Y\<^sub>\<alpha>) \<Down> ?Y\<^sub>\<psi> = \<tau> \<Down> ?Y\<^sub>\<psi>" by (meson noninter com_coincides_by_noninterference run)
    thus ?thesis using rec_tfilter_sfilter_cong by blast
  qed
  ultimately have "Vagree (sfilter (\<omega>\<^sub>\<alpha> @@ (\<tau> \<down> ?Y\<^sub>\<alpha>)) ?Y\<^sub>\<psi>) (sfilter (\<omega> @@ \<tau>) ?Y\<^sub>\<psi>) (FVE (\<pi>\<^sub>I I) \<psi>)" 
    using Vagree_sttconc_cong Vagree_sfilter_cong by presburger
  hence "VCagree (\<omega>\<^sub>\<alpha> @@ (\<tau> \<down> ?Y\<^sub>\<alpha>)) (\<omega> @@ \<tau>) (FNE (\<pi>\<^sub>I I) \<psi>)" by (simp add: VCagree_def FNE_partition)
  thus ?thesis using coincidence_fml by blast
qed

paragraph \<open>Noninterference for the tflat parallel injection axiom\<close>

text \<open>This paragraph shows that the tflat formulation of the parallel injection axiom correctly 
encodes noninterferences\<close>

abbreviation hYVal where "hYVal I \<nu> \<equiv> [Tp ((stT \<nu> rec) \<down> (BConsts\<^sub>\<Omega> (\<pi>\<^sub>I I) chset3))]"

lemma FVE_parAC_overapprox: "(FVE J parA \<union> FVE J parC) \<subseteq> \<iota>\<^sub>T \<V>\<^sub>T"
  using FVE_Psymb FVE_Proj by fastforce

abbreviation xVal where "xVal J \<equiv> vspace_sem J X\<^sub>3"
                                     
lemma FVE_parP_overapprox: "FVE J parP \<subseteq> (vspace_sem J X\<^sub>3) \<union> (\<iota>\<^sub>T \<V>\<^sub>T)"
  using FVE_Psymb FVE_Proj by (fastforce simp add: FVV_def) 

lemma vspace_sem_gtVars [simp]: "vspace_sem J gtVars = \<V>\<^sub>\<mu>" by (auto simp add: gtVars_def gtset_def)

lemma BVP_parbeta_overapprox: "BVP J parbeta \<subseteq> -(vspace_sem J X\<^sub>3) \<union> \<V>\<^sub>\<mu> \<union> \<iota>\<^sub>T \<V>\<^sub>T"
  using BVP_Chp by fastforce

abbreviation parTVars :: "binterp \<Rightarrow> tvar set" 
  where "parTVars J \<equiv> RecP J (paralpha par parbeta)"


lemma sfilter_eq_singleton_compl_Vagree: "sfilter \<nu> (-{(h, ch)}) = sfilter \<omega> (-{(h, ch)}) \<Longrightarrow> Vagree \<nu> \<omega> (\<iota>\<^sub>T (-{h}))"
  using Vagree_sfilter_singleton_compl Vagree_sym by (metis Vagree_only_trans)

lemma CNV_VBot [simp]: "CNV J \<bottom>\<^sub>V = {}" by (simp add: CNV_def)
lemma CNV_VRConst [simp]: "CNV J (VRConst X) = {}" by (simp add: CNV_def)



lemma CNE_Proj_rec: "CNE J (Proj (TVar rec) Y\<^sub>3) \<subseteq> { rec } \<times> (BConsts\<^sub>\<Omega> J) chset3"
  using CNE_Proj_rec unfolding CNC_def by fastforce


lemma CNE_parAC_overapprox: "CNE J (Psymb i \<bottom>\<^sub>V [ TArg (Proj (TVar rec) Y\<^sub>3) ]) `` {rec} \<subseteq> (BConsts\<^sub>\<Omega> J) chset3"
  using CNE_Psymb CNE_Proj_rec by fastforce

lemma CNE_parP_overapprox: "CNE J parP `` {rec} \<subseteq> (BConsts\<^sub>\<Omega> J) chset3"
  using CNE_Psymb CNE_Proj_rec by fastforce

lemma tvars_vspace_sem_recX1: "\<pi>\<^sub>T (vspace_sem J0 recX\<^sub>1) = {rec}" by (simp add: pi_tvars_def)
lemma tvars_vspace_sem_injectableVars: "\<pi>\<^sub>T (vspace_sem J0 injectableVars) = {rec}" 
  by (simp add: pi_tvars_def gtset_def)

lemma RecP_par: "RecP J (chp1 par parbeta) \<subseteq> {rec}"
proof -
  have "BVP J (chp1 par parbeta) \<subseteq> BVP J chp1 \<union> BVP J parbeta" using BVP_par_bound by simp
  hence "BVP J (chp1 par parbeta) \<subseteq> vspace_sem J recX\<^sub>1 \<union> vspace_sem J injectableVars" 
    using BVP_Chp by blast
  hence "\<pi>\<^sub>T (BVP J (chp1 par parbeta)) \<subseteq> {rec}" 
    apply (simp add: pi_tvars_def)
    using tvars_vspace_sem_recX1 tvars_vspace_sem_injectableVars by fastforce
  thus "RecP J (chp1 par parbeta) \<subseteq> {rec}" using RecP_in_BVP by auto
qed


  




(* lemma X\<^sub>1_rspace [simp]: "X\<^sub>1 \<in> rspace" by (simp add: rspace.intros(4)) *)

lemma X\<^sub>1_rspace [simp, intro]: "X\<^sub>1 \<in> rspace" by (simp add: rspace.intros(4))
lemma X\<^sub>3_rspace [simp, intro]: "X\<^sub>3 \<in> rspace" by (simp add: rspace.intros(4))

lemma X\<^sub>1_compl_rspace [simp, intro]: "(-\<^sub>R X\<^sub>1) \<in> rspace" by (simp add: rspace.intros(6))
lemma X\<^sub>3_compl_rspace [simp, intro]: "-\<^sub>R X\<^sub>3 \<in> rspace" by (simp add: rspace.intros(6))


lemma X1_fgtime_rspace [simp, intro!]: "X\<^sub>1 \<inter>\<^sub>V (-\<^sub>V \<mu>f) \<in> rspace" by (simp add: rspace.intros(5)) 
lemma X1_compl_fgtime_rspace [simp, intro!]: "(-\<^sub>R X\<^sub>1) \<inter>\<^sub>V (-\<^sub>V \<mu>f) \<in> rspace" using X\<^sub>1_compl_rspace rspace.intros(5) by blast











lemma noninter_par: "noninterference I parbeta paralpha parA \<and> 
                         noninterference I parbeta paralpha parC \<and> 
                         noninterference I parbeta paralpha parP"
  using FVE_parAC_overapprox FVE_parP_overapprox BVP_parbeta_overapprox CNE_parAC_overapprox CNE_parP_overapprox
  unfolding noninterference_def    
  apply simp
  using CNE_parAC_overapprox RecP_par by blast



paragraph \<open>Actual proof\<close>



lemma assm_transfers_over_injection:
  assumes rel: "prefrel rel"
  assumes run: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I (paralpha par parbeta)"
  assumes assmA: "g_assm_set rel \<nu> \<tau> \<subseteq> fml_sem I parA"
  shows "g_assm_set rel \<nu> (\<tau> \<down> CN (\<pi>\<^sub>I I) paralpha) \<subseteq> fml_sem I parA"
proof -
  obtain \<omega>\<^sub>\<alpha> where alpharun: "(\<nu>, \<tau> \<down> CN (\<pi>\<^sub>I I) paralpha, \<omega>\<^sub>\<alpha>) \<in> chp_sem I paralpha" using chp_sem.simps run by auto
  have "\<And>\<tau>\<^sub>\<alpha>'. rel \<tau>\<^sub>\<alpha>' (\<tau> \<down> CN (\<pi>\<^sub>I I) paralpha) \<Longrightarrow> \<nu> @@ \<tau>\<^sub>\<alpha>' \<in> fml_sem I parA"
  proof - 
    fix \<tau>\<^sub>\<alpha>'
    assume "rel \<tau>\<^sub>\<alpha>' (\<tau> \<down> CN (\<pi>\<^sub>I I) paralpha)"
    then obtain \<tau>' where 0: "rel \<tau>' \<tau> \<and> \<tau>\<^sub>\<alpha>' = \<tau>' \<down> CN (\<pi>\<^sub>I I) paralpha" using unfiltered_sprefix_exists rel unfolding tfilter_def strict_prefix_def by blast
    hence "\<nu> @@ \<tau>' \<in> fml_sem I parA" using assmA unfolding g_assm_set_def by blast
    moreover have "(\<nu>, \<tau>', NonFin) \<in> chp_sem I (paralpha par parbeta)" using 0 chp_sem_total_and_pc obspref_alt pc.cases prefix_order.strict_implies_order rel run by meson
    ultimately show "\<nu> @@ \<tau>\<^sub>\<alpha>' \<in> fml_sem I parA" using 0 noninterference_com_formulas noninter_par by blast
  qed
  thus ?thesis unfolding g_assm_set_def by blast
qed

lemma ac_par_valid: "valid ac_par_axiom"
proof (unfold ac_par_axiom_def, unfold valid_impl, clarify)
  fix I \<nu>
  assume satAlpha: "\<nu> \<in> fml_sem I (AcBox paralpha parA parC parP)"
  show "\<nu> \<in> fml_sem I (AcBox (paralpha par parbeta) parA parC parP)"
  proof (rule ac_box_by_ac_casesI, goal_cases commit post)
    case (commit \<tau> \<omega>)
    then obtain \<omega>\<^sub>\<alpha> where "(\<nu>, \<tau> \<down> CN (\<pi>\<^sub>I I) paralpha, \<omega>\<^sub>\<alpha>) \<in> chp_sem I paralpha" unfolding chp_sem.simps by blast
    moreover have "strict_assm_set \<nu> (\<tau> \<down> CN (\<pi>\<^sub>I I) paralpha) \<subseteq> fml_sem I parA" using commit assm_transfers_over_injection by blast
    ultimately have "\<nu> @@ (\<tau> \<down> CN (\<pi>\<^sub>I I) paralpha) \<in> fml_sem I parC" using satAlpha unfolding fml_sem.simps(8) by blast
    thus "\<nu> @@ \<tau> \<in> fml_sem I parC" using noninterference_com_formulas noninter_par commit(1) by blast
  next
    case (post \<tau> \<omega>)
    then obtain \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> where 
      alpha: "(\<nu>, \<tau> \<down> CN (\<pi>\<^sub>I I) paralpha, Fin \<omega>\<^sub>\<alpha>) \<in> chp_sem I paralpha"
      and beta: "(\<nu>, \<tau> \<down> CN (\<pi>\<^sub>I I) parbeta, Fin \<omega>\<^sub>\<beta>) \<in> chp_sem I parbeta"
      and merge: "\<omega> = lmerge \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> (BVP (\<pi>\<^sub>I I) paralpha)"
      and tsync: "Vagree \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> \<V>\<^sub>\<mu>" by blast

    have "assm_set \<nu> (\<tau> \<down> CN (\<pi>\<^sub>I I) paralpha) \<subseteq> fml_sem I parA" using post assm_transfers_over_injection by blast
    hence "\<omega>\<^sub>\<alpha> @@ (\<tau> \<down> CN (\<pi>\<^sub>I I) paralpha) \<in> fml_sem I parP" using alpha satAlpha unfolding fml_sem.simps(8) by fastforce
    thus "\<omega> @@ \<tau> \<in> fml_sem I parP" using noninterference_post noninter_par post(1) alpha beta merge tsync by blast
  qed
qed





subsection \<open>Soundness of Axioms for Liveness of Parallel CHPs\<close>



lemma byrec_all_empty_but_one: "(\<And>h. h \<noteq> h\<^sub>0 \<Longrightarrow> byrec \<tau> h = []) \<Longrightarrow> byrec \<tau> h\<^sub>0 = tflat \<tau>"
  apply (induction \<tau>)
   apply (simp_all add: byrec_dist_cons)
  by (metis list.simps(2))

lemma urec_Vagree_sttconc: "byrec \<tau> h = tflat \<tau> \<Longrightarrow> Vagree \<nu> (\<nu> @@ \<tau>) (-{Tv h})"
  apply (rule Vagree_by_sortI)
  apply simp
  by (simp add: eqon_def sttconc_def urec_byrec_other)

lemma Vagree_upds: "Vagree \<nu> (upds \<nu> (Tv h) (Tp \<tau>)) (-\<iota>\<^sub>T {h})"
  apply (rule Vagree_by_sortI)
  by (simp_all add: eqon_def)


lemma iota_subsetq [simp, intro]: "\<iota>\<^sub>T X \<subseteq> \<iota>\<^sub>T \<V>\<^sub>T" by auto

lemma upds_Tv_Vagree_other: "Vagree \<nu> (trepv \<nu> h \<tau>) (-\<iota>\<^sub>T \<V>\<^sub>T)"
  apply (rule Vagree_by_sortI)
  by simp_all

lemma fml_sem_Exists_EqT_by_Exists: 
  "fml_sem I (Exists_EqT h te \<psi>) = fml_sem I (Exists (Tv h) (TVar h =\<^sub>T te && \<psi>))"
  by (auto simp add: Exists_EqT_def Forall_EqT_def Forall_def Implies_def)

lemma ttrm_sem_fresh_tvar: 
  "Tv h \<notin> FVE (\<pi>\<^sub>I I) te \<Longrightarrow> ttrm_sem I te (upds \<omega> (Tv h) (Tp d)) = ttrm_sem I te \<omega>"
  using Vagree_def coincidence_ttrm_FVE trepv_access upds.simps(2) by presburger

lemma fml_sem_Forall_EqT: 
  assumes "Tv h \<notin> FVE (\<pi>\<^sub>I I) te"
  shows "fml_sem I (Forall_EqT h te \<psi>) = {\<omega>. upds \<omega> (Tv h) (Tp (ttrm_sem I te \<omega>)) \<in> fml_sem I \<psi> }"
  unfolding Forall_EqT_def
  apply rule
  using ttrm_sem_fresh_tvar assms apply fastforce
  using assms sorteq_def ttrm_sem_fresh_tvar by fastforce

lemma fml_sem_Exists_EqT: "Tv h \<notin> FVE (\<pi>\<^sub>I I) te \<Longrightarrow> fml_sem I (Exists_EqT h te \<psi>) 
    = {\<omega>. upds \<omega> (Tv h) (Tp (ttrm_sem I te \<omega>)) \<in> fml_sem I \<psi> }"
  using Exists_EqT_def fml_sem_Forall_EqT by auto

lemma fml_sem_SyncQ: "fml_sem I (SyncQ \<psi>)
  = {\<omega>. \<exists>\<tau>. \<tau> = \<tau> \<down> (cspace_sem (\<pi>\<^sub>I I) (Y\<^sub>1 \<union>\<^sub>\<Omega> Y\<^sub>2)) \<and> (upds (upds \<omega> (Tv his) (Tp \<tau>)) (Tv hid0) (Tp (stT \<omega> rec))) \<in> fml_sem I \<psi> }"
  unfolding SyncQ_def fml_sem_Exists_EqT_by_Exists 
  by (auto simp add: sorteq_def FVE_TVar fml_sem_Forall_EqT)
  
lemma fml_sem_SyncDiaC0: "fml_sem I (SyncDiaC \<alpha> Y \<psi>) = {\<omega>. upds \<omega> (Tv rec) (Tp []) \<in> fml_sem I (AcDia \<alpha> TT (TVar rec =\<^sub>T Proj (TVar his) Y && \<psi>) FF)}" 
  by (simp add: SyncDiaC_def fml_sem_Forall_EqT)

lemma fml_sem_SyncDiaC: "fml_sem I (SyncDiaC \<alpha> Y \<psi>)
 = {\<nu>. \<exists>\<tau> \<omega>. (upds \<nu> (Tv rec) (Tp []), \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<and> (upds \<nu> (Tv rec) (Tp [])) @@ \<tau> \<in> fml_sem I (TVar rec =\<^sub>T Proj (TVar his) Y && \<psi>)}" 
  by (simp add: SyncDiaC_def fml_sem_Forall_EqT)

lemma fml_sem_SyncDiaP: "fml_sem I (SyncDiaP \<alpha> Y \<psi>)
 = {\<nu>. \<exists>\<tau> \<omega>. (upds \<nu> (Tv rec) (Tp []), \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha> \<and> (trepv \<omega> rec []) @@ \<tau> \<in> fml_sem I (TVar rec =\<^sub>T Proj (TVar his) Y && \<psi>)}" 
proof -
  have 0: "\<And>\<nu> \<tau> \<omega>. (trepv \<nu> rec [], \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> \<omega> = trepv \<omega> rec []"
  proof -
    fix \<nu> \<tau> \<omega>
    assume "(trepv \<nu> rec [], \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha>"
    hence "eqon (stT (trepv \<nu> rec [])) (stT \<omega>) (\<pi>\<^sub>T (\<iota>\<^sub>T \<V>\<^sub>T))" using bound_effect_on_state(2) Vagree_stT_E by blast
    hence "eqon (stT (trepv \<nu> rec [])) (stT \<omega>) \<V>\<^sub>T" by simp
    hence "stT \<omega> rec = []" by (metis UNIV_I eqon_def trepv_stT_access)
    thus "\<omega> = trepv \<omega> rec []" by (metis trepv_self)
  qed
  have "fml_sem I (SyncDiaP \<alpha> Y \<psi>)
    = {\<nu>. \<exists>\<tau> \<omega>. (trepv \<nu> rec [], \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha> \<and> \<omega> @@ \<tau> \<in> fml_sem I (TVar rec =\<^sub>T Proj (TVar his) Y && \<psi>)}"
    by (simp add: SyncDiaP_def fml_sem_Forall_EqT)
  thus ?thesis using 0 by fastforce
qed





lemma rvars_inter_tvars_empty: "X \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R \<Longrightarrow> X \<inter> \<iota>\<^sub>T \<V>\<^sub>T = {}" 
  apply (simp add: iota_rvars_def iota_tvars_def) by blast

(* not simp to protect proofs *)
lemma pi_tvars_gtset: "\<pi>\<^sub>T \<V>\<^sub>\<mu> = {}" by (auto simp add: gtset_def)



lemma byrec_rChp_trace: "X \<in> rspace \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> chp_sem I (rChp a Y X) \<Longrightarrow> byrec \<tau> rec = tflat \<tau>"
proof -
  assume "X \<in> rspace"
  moreover have "\<pi>\<^sub>T (BVP (\<pi>\<^sub>I I) (rChp a Y X)) \<subseteq> {rec} \<union> \<pi>\<^sub>T (vspace_sem (\<pi>\<^sub>I I) (gtVars \<union>\<^sub>V X))"
    unfolding rChp_def using BVP_Chp by fastforce
  ultimately have "RecP (\<pi>\<^sub>I I) (rChp a Y X) \<subseteq> {rec}" using RecP_in_BVP by (auto simp add: pi_tvars_gtset)
  moreover assume "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I (rChp a Y X)"
  ultimately have "\<And>h. h \<noteq> rec \<Longrightarrow> byrec \<tau> h = []" unfolding RecP_def by blast
  thus "byrec \<tau> rec = tflat \<tau>" using byrec_all_empty_but_one by blast
qed

lemma other_rec_empty_rChp: "X \<in> rspace \<Longrightarrow> h \<noteq> rec \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> chp_sem I (rChp a Y X) \<Longrightarrow> byrec \<tau> h = []"
  by (simp add: urec_byrec_other byrec_rChp_trace)

lemma fml_sem_SyncDiaC_rChp: "X \<in> rspace \<Longrightarrow> fml_sem I (SyncDiaC (rChp a Y X) Y \<psi>)
 = {\<nu>. \<exists>\<tau> \<omega>. (trepv \<nu> rec [], \<tau>, \<omega>) \<in> chp_sem I (rChp a Y X) \<and> byrec \<tau> rec = ((stT \<nu>) his) \<down> (cspace_sem (\<pi>\<^sub>I I) Y) \<and> (upds \<nu> (Tv rec) (Tp [])) @@ \<tau> \<in> fml_sem I \<psi>}" 
  by (auto simp add: fml_sem_SyncDiaC stT_sttconc_dist other_rec_empty_rChp)

lemma fin_stT [simp]: "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> stT \<omega> = stT \<nu>"
  using DiffD_reach_stT DiffD_chp_sem by fastforce

lemma fml_sem_SyncDiaP_rChp: "X \<in> rspace \<Longrightarrow> fml_sem I (SyncDiaP (rChp a Y X) Y \<psi>)
 = {\<nu>. \<exists>\<tau> \<omega>. (trepv \<nu> rec [], \<tau>, Fin \<omega>) \<in> chp_sem I (rChp a Y X) 
    \<and> byrec \<tau> rec = ((stT \<nu>) his) \<down> (cspace_sem (\<pi>\<^sub>I I) Y) \<and> (trepv \<omega> rec []) @@ \<tau> \<in> fml_sem I \<psi>}"
  by (fastforce simp add: fml_sem_SyncDiaP stT_sttconc_dist other_rec_empty_rChp)

lemma gtime_fresh [simp]: "distinct [\<mu>, \<mu>p, \<mu>\<^sub>0, \<mu>\<^sub>0p, \<mu>\<^sub>1, \<mu>\<^sub>1p]"
  by (simp_all add: gtime_def gtime0_def gtime1_def gtime_pace_def gtime0_pace_def gtime1_pace_def)

lemma gtime_fresh0 [simp]: 
  shows "\<mu> \<noteq> \<mu>\<^sub>1" and "\<mu> \<noteq> \<mu>\<^sub>1p" and "\<mu>\<^sub>0 \<noteq> \<mu>p" and "\<mu>\<^sub>1 \<noteq> \<mu>p" and "\<mu> \<noteq> \<mu>\<^sub>0p" and "\<mu>\<^sub>1p \<noteq> \<mu>\<^sub>0" and "\<mu>\<^sub>1p \<noteq> \<mu>\<^sub>0p" and "\<mu>\<^sub>1 \<noteq> \<mu>\<^sub>0" and "\<mu>\<^sub>1 \<noteq> \<mu>\<^sub>0p"
  by (simp_all add: gtime_def gtime0_def gtime1_def gtime_pace_def gtime0_pace_def gtime1_pace_def)



definition gtset0 :: "variable set" ("\<V>\<^sub>\<mu>\<^sub>0")
  where "gtset0 = { Rv \<mu>\<^sub>0, Rv \<mu>\<^sub>0p }"

definition gtset1 :: "variable set" ("\<V>\<^sub>\<mu>\<^sub>1")
  where "gtset1 = { Rv \<mu>\<^sub>1, Rv \<mu>\<^sub>1p }"

abbreviation gtsetf :: "variable set" ("\<V>\<^sub>\<mu>\<^sub>f")
  where "gtsetf \<equiv> \<V>\<^sub>\<mu>\<^sub>0 \<union> \<V>\<^sub>\<mu>\<^sub>1" 

lemma gtime_disjoint: "\<V>\<^sub>\<mu> \<subseteq> -\<V>\<^sub>\<mu>\<^sub>0 \<inter> -\<V>\<^sub>\<mu>\<^sub>1"
  unfolding gtset_def gtset0_def gtset1_def using gtime_fresh by auto

lemma vspace_sem_gtfresh [simp]: "vspace_sem J \<mu>f = \<V>\<^sub>\<mu>\<^sub>f" 
  by (auto simp add: fresh_gtime_def gtset0_def gtset1_def)

lemma BVP_live_par_alpha: "BVP J live_par_alpha \<subseteq> {Tv rec} \<union> \<V>\<^sub>\<mu> \<union> (\<iota>\<^sub>R (BConsts\<^sub>R\<^sub>V J xvar1) \<inter> -\<V>\<^sub>\<mu>\<^sub>f)"
  unfolding rChp_def using BVP_Chp vspace_sem_gtfresh vspace_sem_VRConst_only_rvars by fastforce
                                                 
lemma BVP_live_par_beta: "BVP J live_par_beta \<subseteq> {Tv rec} \<union> \<V>\<^sub>\<mu> \<union> ((-(\<iota>\<^sub>R (BConsts\<^sub>R\<^sub>V J xvar1)) \<inter> \<iota>\<^sub>R \<V>\<^sub>R) \<inter> -\<V>\<^sub>\<mu>\<^sub>f)"
  unfolding rChp_def using BVP_Chp vspace_sem_gtfresh vspace_sem_VRConst_only_rvars by fastforce

lemma wf_rChp [simp, intro]: "wf_chp \<L> (rChp a Y X)"
  by (simp add: rChp_def)

lemma BVP_rChp_VRConst: "BVP J (rChp a Y (VRConst X)) \<subseteq> {Tv rec} \<union> \<V>\<^sub>\<mu> \<union> \<iota>\<^sub>R (BConsts\<^sub>R\<^sub>V J X)"
  unfolding rChp_def using BVP_Chp by fastforce

lemma BVP_rChp_BRCompl_VRConst: "BVP J (rChp a Y (-\<^sub>R (VRConst X))) \<subseteq> {Tv rec} \<union> \<V>\<^sub>\<mu> \<union> -\<iota>\<^sub>R (BConsts\<^sub>R\<^sub>V J X)"
  unfolding rChp_def using BVP_Chp by fastforce

lemma BVP_pi_of_BND: "BVP J \<alpha> = \<pi>\<^sub>V (BNP J \<alpha>)" using BNP_partition by simp

lemma BVP\<^sub>\<L>_sem_stat_sem: "BVP\<^sub>\<L> (\<L>\<^sub>0 J) = BVP J"
  unfolding BVP\<^sub>\<L>_def BVP_pi_of_BND
  by (simp add:  sem_stat_sem_def)
  

lemma wf_rChp_par: "wf_chp (\<L>\<^sub>0 J) ((rChp chpid1 Y\<^sub>1 X\<^sub>1) par (rChp chpid2 Y\<^sub>2 (-\<^sub>R X\<^sub>1)))"
  apply (simp add: BVP\<^sub>\<L>_sem_stat_sem)
  using BVP_rChp_VRConst[of J chpid1 Y\<^sub>1] BVP_rChp_BRCompl_VRConst[of J chpid2 Y\<^sub>2]
  by fastforce








lemma ac_live_parC_valid: "valid ac_live_parC"
proof (unfold ac_live_parC_def valid_impl, clarify)
  fix I \<nu>
  let ?\<nu>\<^sub>0 = "\<lambda>\<tau>. (trepv (trepv \<nu> his \<tau>) hid0 (stT \<nu> rec))"

  assume "\<nu> \<in> fml_sem I (SyncQ (SyncDiaC (rChp chpid1 Y\<^sub>1 X\<^sub>1) Y\<^sub>1 TT 
            && SyncDiaC (rChp chpid2 Y\<^sub>2 (-\<^sub>R X\<^sub>1)) Y\<^sub>2 TT && Cof ((TVar hid0) \<circ>\<^sub>T (TVar his))))"

  then obtain \<tau> 
    where nojunk: "\<tau> = \<tau> \<down> (cspace_sem (\<pi>\<^sub>I I) (Y\<^sub>1 \<union>\<^sub>\<Omega> Y\<^sub>2))"
      and "(?\<nu>\<^sub>0 \<tau>) \<in> fml_sem I (SyncDiaC (rChp chpid1 Y\<^sub>1 X\<^sub>1) Y\<^sub>1 TT 
          && SyncDiaC (rChp chpid2 Y\<^sub>2 (-\<^sub>R X\<^sub>1)) Y\<^sub>2 TT)"
      and commit: "(?\<nu>\<^sub>0 \<tau>) \<in> fml_sem I (Cof ((TVar hid0) \<circ>\<^sub>T (TVar his)))"
    using fml_sem_SyncQ by auto

  (* there are runs of the subprograms whose communication matches the overall communication 
    history \<tau> on the channels of the subprogram modulo the recorder *)
  then obtain \<tau>\<^sub>1 \<tau>\<^sub>2 
    where run1: "(trepv (?\<nu>\<^sub>0 \<tau>) rec [], \<tau>\<^sub>1, NonFin) \<in> chp_sem I (rChp chpid1 Y\<^sub>1 X\<^sub>1)"
      and com1: "(byrec \<tau>\<^sub>1 rec) = ((stT (?\<nu>\<^sub>0 \<tau>)) his) \<down> (cspace_sem (\<pi>\<^sub>I I) Y\<^sub>1)"
      and run2: "(trepv (?\<nu>\<^sub>0 \<tau>) rec [], \<tau>\<^sub>2, NonFin) \<in> chp_sem I (rChp chpid2 Y\<^sub>2 (-\<^sub>R X\<^sub>1))"
      and com2: "(byrec \<tau>\<^sub>2 rec) = ((stT (?\<nu>\<^sub>0 \<tau>)) his) \<down> (cspace_sem (\<pi>\<^sub>I I) Y\<^sub>2)"
    using fml_sem_SyncDiaC_rChp lower_run by fastforce

  (* the overall history \<tau> matches the communication of the subprograms when resetting the recorder *) 
  hence "tflat \<tau>\<^sub>1 = \<tau> \<down> (cspace_sem (\<pi>\<^sub>I I) Y\<^sub>1)" and "tflat \<tau>\<^sub>2 = \<tau> \<down> (cspace_sem (\<pi>\<^sub>I I) Y\<^sub>2)" 
    using byrec_rChp_trace run1 run2 com1 com2 X\<^sub>1_rspace X\<^sub>1_compl_rspace by auto
  hence "\<tau>\<^sub>1 = addrec \<tau> rec \<down> (cspace_sem (\<pi>\<^sub>I I) Y\<^sub>1)" and "\<tau>\<^sub>2 = addrec \<tau> rec \<down> (cspace_sem (\<pi>\<^sub>I I) Y\<^sub>2)"
    using addrec_tfilter_commute addrec_urec_tflat byrec_rChp_trace run1 run2 X\<^sub>1_rspace X\<^sub>1_compl_rspace by metis+
  hence com1: "\<tau>\<^sub>1 = addrec \<tau> rec \<down> CN (\<pi>\<^sub>I I) (rChp chpid1 Y\<^sub>1 X\<^sub>1)"
    and com2: "\<tau>\<^sub>2 = addrec \<tau> rec \<down> CN (\<pi>\<^sub>I I) (rChp chpid2 Y\<^sub>2 (-\<^sub>R X\<^sub>1))" by (simp_all add: rChp_def gtVars_def)

  have "addrec (\<tau> \<down> (CN (\<pi>\<^sub>I I) (rChp chpid1 Y\<^sub>1 X\<^sub>1) \<union> CN (\<pi>\<^sub>I I) (rChp chpid2 Y\<^sub>2 (-\<^sub>R X\<^sub>1)))) rec = addrec \<tau> rec"
    using nojunk by (simp add: rChp_def gtVars_def)
  hence "(addrec \<tau> rec) \<down> (CN (\<pi>\<^sub>I I) (rChp chpid1 Y\<^sub>1 X\<^sub>1) \<union> CN (\<pi>\<^sub>I I) (rChp chpid2 Y\<^sub>2 (-\<^sub>R X\<^sub>1))) = addrec \<tau> rec"
    by simp

  (* there is a run with the joint communication history \<tau> *) 
  hence "(trepv (?\<nu>\<^sub>0 \<tau>) rec [], addrec \<tau> rec, NonFin) \<in> chp_sem I ((rChp chpid1 Y\<^sub>1 X\<^sub>1) par (rChp chpid2 Y\<^sub>2 (-\<^sub>R X\<^sub>1)))"
    using run1 run2 com1 com2 lower_run by blast

  (* rebase the run *)
  moreover have "Vagree (trepv (?\<nu>\<^sub>0 \<tau>) rec []) \<nu> (-\<iota>\<^sub>T \<V>\<^sub>T)"
    using upds_Tv_Vagree_other by (meson Vagree_sym_rel Vagree_only_trans)
  ultimately obtain \<omega>' where "(\<nu>, addrec \<tau> rec, \<omega>') \<in> chp_sem I ((rChp chpid1 Y\<^sub>1 X\<^sub>1) par (rChp chpid2 Y\<^sub>2 (-\<^sub>R X\<^sub>1)))"
    by (metis wf_rChp_par coincidence_chp FVP_no_tvars)
  
  moreover have "\<nu> @@ (addrec \<tau> rec) \<in> fml_sem I (Cof (TVar rec))"
    using commit by (simp add: args_sem_def sttconc_addrec)
 
  ultimately show "\<nu> \<in> fml_sem I (AcDia (rChp chpid1 Y\<^sub>1 X\<^sub>1 par rChp chpid2 Y\<^sub>2 (-\<^sub>R X\<^sub>1)) TT (Cof (TVar rec)) FF)"
    using fml_sem_AcDia_commitI by auto
qed



paragraph \<open>Run-existence to a Final State\<close>

lemma FVP_rChp: "FVP J (rChp a Y (X \<inter>\<^sub>V (-\<^sub>V \<mu>f))) \<subseteq> \<V>\<^sub>\<mu> \<union> (vspace_sem J X \<inter> (\<iota>\<^sub>R \<V>\<^sub>R) \<inter> -\<V>\<^sub>\<mu>\<^sub>0 \<inter> -\<V>\<^sub>\<mu>\<^sub>1)"
  unfolding rChp_def using FVP_Chp by fastforce

lemma vspace_sem_LivePar: "vspace_sem J (X\<^sub>3 \<inter>\<^sub>V (-\<^sub>V \<mu>f)) \<subseteq> -(\<iota>\<^sub>T \<V>\<^sub>T) \<inter> -\<V>\<^sub>\<mu>\<^sub>f"
  using BConsts\<^sub>R\<^sub>V_correct by (simp add: inf.coboundedI1 inf.coboundedI2)

(* lemma wf_rSys [simp, intro]: "wf_chp \<L> (rSys a Y X)"
  by (simp add: rSys_def) *)

lemma wf_live_par: "wf_chp (\<L>\<^sub>0 J) (live_par_alpha par live_par_beta)"
  apply (simp add: BVP\<^sub>\<L>_sem_stat_sem)
  using BVP_live_par_alpha[of J] BVP_live_par_beta[of J] by fastforce
  
lemma gtime_bounds: 
  shows "\<V>\<^sub>\<mu> \<subseteq> -{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>f" and "\<V>\<^sub>\<mu>\<^sub>f \<subseteq> -{Tv rec} \<inter> -\<V>\<^sub>\<mu>"
  unfolding gtset_def gtset0_def gtset1_def using gtime_fresh by fastforce+

lemma disjoint_state_live_par: "BVP J live_par_alpha \<inter> BVP J live_par_beta \<subseteq> {Tv rec} \<union> \<V>\<^sub>\<mu>"
  using BVP_live_par_alpha BVP_live_par_beta by blast



lemma ac_live_parP_valid: "valid ac_live_parP"
proof (unfold ac_live_parP_def valid_impl, clarify)
  fix I \<nu>
  let ?\<nu>\<^sub>0 = "\<lambda>\<tau>. (trepv (trepv \<nu> his \<tau>) hid0 (stT \<nu> rec))"

  let ?savetime = "\<mu>\<^sub>0 := RVar \<mu> ;; \<mu>\<^sub>0p := RVar \<mu>p"
  let ?restore = "\<mu>\<^sub>1 := RVar \<mu> ;; \<mu>\<^sub>1p := RVar \<mu>p ;; \<mu> := RVar \<mu>\<^sub>0 ;; \<mu>p := RVar \<mu>\<^sub>0p"
  
  assume "\<nu> \<in> fml_sem I (SyncQ (Diamond ?savetime (SyncDiaP live_par_alpha Y\<^sub>1 (Diamond ?restore
    (SyncDiaP live_par_beta Y\<^sub>2 (Diamond (? ((RVar \<mu>) =\<^sub>R (RVar \<mu>\<^sub>1) && (RVar \<mu>p) =\<^sub>R (RVar \<mu>\<^sub>1p)))
        (LiveParP ((TVar hid0) \<circ>\<^sub>T (TVar his)))))))))"

  then obtain \<tau> 
    where nojunk: "\<tau> = \<tau> \<down> (cspace_sem (\<pi>\<^sub>I I) (Y\<^sub>1 \<union>\<^sub>\<Omega> Y\<^sub>2))"
      and seq: "(?\<nu>\<^sub>0 \<tau>) \<in> fml_sem I (Diamond ?savetime (SyncDiaP live_par_alpha Y\<^sub>1 (Diamond ?restore
    (SyncDiaP live_par_beta Y\<^sub>2 (Diamond (? ((RVar \<mu>) =\<^sub>R (RVar \<mu>\<^sub>1) && (RVar \<mu>p) =\<^sub>R (RVar \<mu>\<^sub>1p)))
        (LiveParP ((TVar hid0) \<circ>\<^sub>T (TVar his))))))))"
    using fml_sem_SyncQ by auto

  let ?\<nu>\<^sub>\<alpha> = "rrepv (rrepv (?\<nu>\<^sub>0 \<tau>) \<mu>\<^sub>0 (stR (?\<nu>\<^sub>0 \<tau>) \<mu>)) \<mu>\<^sub>0p (stR (?\<nu>\<^sub>0 \<tau>) \<mu>p)"

  from seq have "?\<nu>\<^sub>\<alpha> \<in> fml_sem I (SyncDiaP live_par_alpha Y\<^sub>1 (Diamond ?restore 
    (SyncDiaP live_par_beta Y\<^sub>2 (Diamond (? ((RVar \<mu>) =\<^sub>R (RVar \<mu>\<^sub>1) && (RVar \<mu>p) =\<^sub>R (RVar \<mu>\<^sub>1p)))
        (LiveParP ((TVar hid0) \<circ>\<^sub>T (TVar his)))))))"
    by simp

  (* there is a run of subprogram \<alpha> whose communication matches the overall communication 
    history \<tau> on \<alpha>'s channels modulo the recorder *)
  then obtain \<tau>\<^sub>1 \<omega>\<^sub>1 where run1: "(trepv ?\<nu>\<^sub>\<alpha> rec [], \<tau>\<^sub>1, Fin \<omega>\<^sub>1) \<in> chp_sem I live_par_alpha"
    and com1: "byrec \<tau>\<^sub>1 rec = ((stT ?\<nu>\<^sub>\<alpha>) his) \<down> (cspace_sem (\<pi>\<^sub>I I) Y\<^sub>1)"
    and seq: "(trepv \<omega>\<^sub>1 rec []) @@ \<tau>\<^sub>1 \<in> fml_sem I (Diamond ?restore 
    (SyncDiaP live_par_beta Y\<^sub>2 (Diamond (? ((RVar \<mu>) =\<^sub>R (RVar \<mu>\<^sub>1) && (RVar \<mu>p) =\<^sub>R (RVar \<mu>\<^sub>1p)))
        (LiveParP ((TVar hid0) \<circ>\<^sub>T (TVar his))))))"
    using fml_sem_SyncDiaP_rChp by blast
                                      
  
  let ?\<omega>fin = "(upds \<omega>\<^sub>1 (Tv rec) (Tp [])) @@ \<tau>\<^sub>1"

  let ?\<nu>\<^sub>\<beta> = "rrepv (rrepv (rrepv (rrepv ?\<omega>fin \<mu>\<^sub>1 (stR ?\<omega>fin \<mu>)) \<mu>\<^sub>1p (stR ?\<omega>fin \<mu>p)) \<mu> (stR ?\<omega>fin \<mu>\<^sub>0)) \<mu>p (stR ?\<omega>fin \<mu>\<^sub>0p)"

  (* ?\<nu>\<^sub>\<beta> saves and restores the time after running \<alpha> *)
  from seq have "?\<nu>\<^sub>\<beta> \<in> fml_sem I 
    (SyncDiaP live_par_beta Y\<^sub>2 (Diamond (? ((RVar \<mu>) =\<^sub>R (RVar \<mu>\<^sub>1) && (RVar \<mu>p) =\<^sub>R (RVar \<mu>\<^sub>1p)))
        (LiveParP ((TVar hid0) \<circ>\<^sub>T (TVar his)))))"
    by simp

  (* there is a run of subprogram \<beta> whose communication matches the overall communication 
    history \<tau> on \<beta>'s channels modulo the recorder *)
  then obtain \<tau>\<^sub>2 \<omega>\<^sub>2 where run2: "(trepv ?\<nu>\<^sub>\<beta> rec [], \<tau>\<^sub>2, Fin \<omega>\<^sub>2) \<in> chp_sem I live_par_beta"
    and com2: "byrec \<tau>\<^sub>2 rec = ((stT ?\<nu>\<^sub>\<beta>) his) \<down> (cspace_sem (\<pi>\<^sub>I I) Y\<^sub>2)"
    and seq: "(trepv \<omega>\<^sub>2 rec []) @@ \<tau>\<^sub>2 \<in> fml_sem I 
        (Diamond (? ((RVar \<mu>) =\<^sub>R (RVar \<mu>\<^sub>1) && (RVar \<mu>p) =\<^sub>R (RVar \<mu>\<^sub>1p)))
        (LiveParP ((TVar hid0) \<circ>\<^sub>T (TVar his))))"
    using fml_sem_SyncDiaP_rChp by blast

  have vagree_fin_ini: "Vagree \<omega>\<^sub>1 ?\<nu>\<^sub>\<beta> (-{Tv rec} \<inter> (-\<V>\<^sub>\<mu> \<inter> -\<V>\<^sub>\<mu>\<^sub>1))"
  proof -                                           
    have "byrec \<tau>\<^sub>1 rec = tflat \<tau>\<^sub>1" using byrec_rChp_trace run1 X1_fgtime_rspace by blast
    hence "Vagree (trepv \<omega>\<^sub>1 rec []) ?\<omega>fin (-{Tv rec})" using urec_Vagree_sttconc by simp
    moreover have "Vagree \<omega>\<^sub>1 (trepv \<omega>\<^sub>1 rec []) (-{Tv rec})" using Vagree_trepv by simp
    ultimately have "Vagree \<omega>\<^sub>1 ?\<omega>fin (-{Tv rec})" using Vagree_only_trans by blast
    moreover have "Vagree ?\<omega>fin ?\<nu>\<^sub>\<beta> (-\<V>\<^sub>\<mu> \<inter> -\<V>\<^sub>\<mu>\<^sub>1)" by (simp add: gtset_def gtset1_def Vagree_def)
    ultimately show "Vagree \<omega>\<^sub>1 ?\<nu>\<^sub>\<beta> (-{Tv rec} \<inter> (-\<V>\<^sub>\<mu> \<inter> -\<V>\<^sub>\<mu>\<^sub>1))" using Vagree_trans by blast
  qed

  have inis_agree_on_ghost_tvars: "Vagree ?\<nu>\<^sub>\<alpha> ?\<nu>\<^sub>\<beta> (\<iota>\<^sub>T (-{rec}))"
  proof - 
    have "\<iota>\<^sub>T (-{rec}) \<subseteq> -{Tv rec} \<inter> (-\<V>\<^sub>\<mu> \<inter> -\<V>\<^sub>\<mu>\<^sub>1)" unfolding gtset_def gtset1_def by auto 
    hence "Vagree \<omega>\<^sub>1 ?\<nu>\<^sub>\<beta> (\<iota>\<^sub>T (-{rec}))" using vagree_fin_ini Vagree_antimon by blast
    moreover have "Vagree (trepv ?\<nu>\<^sub>\<alpha> rec []) \<omega>\<^sub>1 (\<iota>\<^sub>T (-{rec}))"
      using bound_effect_on_state(2) run1 by (meson Vagree_antimon iota_subsetq)
    ultimately have "Vagree (trepv ?\<nu>\<^sub>\<alpha> rec []) ?\<nu>\<^sub>\<beta> (\<iota>\<^sub>T (-{rec}))" using Vagree_only_trans by blast
    moreover have "Vagree ?\<nu>\<^sub>\<alpha> (trepv ?\<nu>\<^sub>\<alpha> rec []) (\<iota>\<^sub>T (-{rec}))"  
      using Vagree_trepv apply (rule Vagree_antimon) by simp 
    ultimately show "Vagree ?\<nu>\<^sub>\<alpha> ?\<nu>\<^sub>\<beta> (\<iota>\<^sub>T (-{rec}))" using Vagree_only_trans by blast
  qed

  hence "eqon (stT ?\<nu>\<^sub>\<alpha>) (stT ?\<nu>\<^sub>\<beta>) (-{rec})" using Vagree_T_onlyE by blast
  hence "\<forall>z. (z\<noteq>rec \<longrightarrow> (stT ?\<nu>\<^sub>\<alpha>)(z) = (stT ?\<nu>\<^sub>\<beta>)(z))" by (simp add: eqon_def)
  hence "(stT ?\<nu>\<^sub>\<alpha>)(his) = (stT ?\<nu>\<^sub>\<beta>)(his)" by blast

  (* the overall history \<tau> matches the communication of the subprograms when resetting the recorder *)
  hence "tflat \<tau>\<^sub>1 = \<tau> \<down> (cspace_sem (\<pi>\<^sub>I I) Y\<^sub>1)" and com2: "tflat \<tau>\<^sub>2 = \<tau> \<down> (cspace_sem (\<pi>\<^sub>I I) Y\<^sub>2)" 
    using byrec_rChp_trace run1 run2 com1 com2 by fastforce+
  hence "\<tau>\<^sub>1 = addrec \<tau> rec \<down> (cspace_sem (\<pi>\<^sub>I I) Y\<^sub>1)" 
    using addrec_tfilter_commute addrec_urec_tflat byrec_rChp_trace run1 by fastforce
  moreover have "\<tau>\<^sub>2 = addrec \<tau> rec \<down> (cspace_sem (\<pi>\<^sub>I I) Y\<^sub>2)"
    using addrec_tfilter_commute addrec_urec_tflat byrec_rChp_trace run2 com2 by fastforce
  ultimately have 
        com1: "\<tau>\<^sub>1 = addrec \<tau> rec \<down> CN (\<pi>\<^sub>I I) live_par_alpha"
    and com2: "\<tau>\<^sub>2 = addrec \<tau> rec \<down> CN (\<pi>\<^sub>I I) live_par_beta" 
    using com1 com2 by (simp_all add: rChp_def gtVars_def)

  have "addrec (\<tau> \<down> (CN (\<pi>\<^sub>I I) live_par_alpha \<union> CN (\<pi>\<^sub>I I) live_par_beta)) rec = addrec \<tau> rec"
    using nojunk by (simp add: rChp_def gtVars_def)
  hence nojunk: "(addrec \<tau> rec) \<down> (CN (\<pi>\<^sub>I I) live_par_alpha \<union> CN (\<pi>\<^sub>I I) live_par_beta) = addrec \<tau> rec"
    by simp

  let ?X\<^sub>1 = "vspace_sem (\<pi>\<^sub>I I) X\<^sub>1"
  let ?BV\<alpha> = "BVP (\<pi>\<^sub>I I) live_par_alpha"
  let ?BV\<beta> = "BVP (\<pi>\<^sub>I I) live_par_beta"

  have inis_agree: "Vagree (?\<nu>\<^sub>0 \<tau>) (trepv ?\<nu>\<^sub>\<alpha> rec []) (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>0)"
      apply (rule Vagree_by_sortI) by (simp_all add: eqon_def gtset0_def)

  (* rebase \<alpha>-run *)
  have alpha_rebased: "\<exists>\<omega>\<^sub>1'. (?\<nu>\<^sub>0 \<tau>, \<tau>\<^sub>1, Fin \<omega>\<^sub>1') \<in> chp_sem I live_par_alpha
    \<and> Vagree \<omega>\<^sub>1 \<omega>\<^sub>1' (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>0)"
  proof -
    have "FVP (\<pi>\<^sub>I I) live_par_alpha \<subseteq> -\<V>\<^sub>\<mu>\<^sub>0" using FVP_rChp gtime_disjoint by blast
    moreover have "FVP (\<pi>\<^sub>I I) live_par_alpha \<subseteq> -{Tv rec}"        
      using FVP_no_tvars wf_chp.simps(2) rChp_def by fastforce
    ultimately have "FVP (\<pi>\<^sub>I I) live_par_alpha \<subseteq> -{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>0" by blast
    thus "\<exists>\<omega>\<^sub>1'. (?\<nu>\<^sub>0 \<tau>, \<tau>\<^sub>1, Fin \<omega>\<^sub>1') \<in> chp_sem I live_par_alpha \<and> Vagree \<omega>\<^sub>1 \<omega>\<^sub>1' (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>0)" 
      using inis_agree run1 Vagree_sym coincidence_chp_fin by blast
  qed

  (* rebase \<beta>-run *)
  have beta_rebased: "\<exists>\<omega>\<^sub>2'. (?\<nu>\<^sub>0 \<tau>, \<tau>\<^sub>2, Fin \<omega>\<^sub>2') \<in> chp_sem I live_par_beta 
    \<and> Vagree \<omega>\<^sub>2 \<omega>\<^sub>2' (\<V>\<^sub>\<mu> \<union> (-{Tv rec} \<inter> -?X\<^sub>1 \<inter> -\<V>\<^sub>\<mu>\<^sub>f))"
  proof -
    have "Vagree (trepv ?\<nu>\<^sub>\<alpha> rec []) (\<omega>\<^sub>1 @@ \<tau>\<^sub>1) (-?BV\<alpha>)"
      using run1 bound_effect_on_state by simp
    hence bep: "Vagree (trepv ?\<nu>\<^sub>\<alpha> rec []) (\<omega>\<^sub>1 @@ \<tau>\<^sub>1) (-{Tv rec} \<inter> -\<V>\<^sub>\<mu> \<inter> (-?X\<^sub>1 \<union> \<V>\<^sub>\<mu>\<^sub>f))"
      apply (rule Vagree_antimon) using BVP_live_par_alpha by fastforce

    moreover have "Vagree (?\<nu>\<^sub>0 \<tau>) (trepv ?\<nu>\<^sub>\<alpha> rec []) (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>0)"
      apply (rule Vagree_by_sortI) by (simp_all add: gtset0_def eqon_def)                                                          
    ultimately have "Vagree (?\<nu>\<^sub>0 \<tau>) (\<omega>\<^sub>1 @@ \<tau>\<^sub>1) (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>0 \<inter> (-{Tv rec} \<inter> -\<V>\<^sub>\<mu> \<inter> (-?X\<^sub>1 \<union> \<V>\<^sub>\<mu>\<^sub>f)))"
      using Vagree_trans by blast
    hence "Vagree (?\<nu>\<^sub>0 \<tau>) (\<omega>\<^sub>1 @@ \<tau>\<^sub>1) (-\<V>\<^sub>\<mu>\<^sub>0 \<inter> (-{Tv rec} \<inter> -\<V>\<^sub>\<mu> \<inter> (-?X\<^sub>1 \<union> \<V>\<^sub>\<mu>\<^sub>1)))"
      apply (rule Vagree_eq) by blast

    moreover have "Vagree (\<omega>\<^sub>1 @@ \<tau>\<^sub>1) ?\<nu>\<^sub>\<beta> (-{Tv rec} \<inter> -\<V>\<^sub>\<mu> \<inter> -\<V>\<^sub>\<mu>\<^sub>1)"
      apply (rule Vagree_by_sortI)
      by (simp_all add: eqon_def gtset_def gtset0_def gtset1_def stT_sttconc_dist)
    ultimately have agree_beta: "Vagree (?\<nu>\<^sub>0 \<tau>) ?\<nu>\<^sub>\<beta> (-{Tv rec} \<inter> -\<V>\<^sub>\<mu> \<inter> -\<V>\<^sub>\<mu>\<^sub>f \<inter> -?X\<^sub>1)"
      apply (rule Vagree_trans_eq) by blast

    have "Vagree (?\<nu>\<^sub>0 \<tau>) ?\<nu>\<^sub>\<beta> \<V>\<^sub>\<mu>"
    proof -
      have "Vagree (trepv ?\<nu>\<^sub>\<alpha> rec []) (\<omega>\<^sub>1 @@ \<tau>\<^sub>1) \<V>\<^sub>\<mu>\<^sub>0"
        using bep Vagree_antimon gtime_bounds by blast
      hence bep: "eqon (stR ?\<nu>\<^sub>\<alpha>) (stR \<omega>\<^sub>1) {\<mu>\<^sub>0, \<mu>\<^sub>0p}"
        unfolding gtset0_def Vagree_def eqon_def by auto
  
      have "(?\<nu>\<^sub>0 \<tau>) $$ (Rv \<mu>) = (trepv ?\<nu>\<^sub>\<alpha> rec []) $$ (Rv \<mu>\<^sub>0)" using gtime_fresh by auto
      also have "... = (\<omega>\<^sub>1 @@ \<tau>\<^sub>1) $$ (Rv \<mu>\<^sub>0)" using bep by (auto simp add: eqon_def)
      also have "... = ?\<nu>\<^sub>\<beta> $$ (Rv \<mu>)" using gtime_fresh by auto
      finally have mu: "(?\<nu>\<^sub>0 \<tau>) $$ (Rv \<mu>) = ?\<nu>\<^sub>\<beta> $$ (Rv \<mu>)" .
  
      have "(?\<nu>\<^sub>0 \<tau>) $$ (Rv \<mu>p) = (trepv ?\<nu>\<^sub>\<alpha> rec []) $$ (Rv \<mu>\<^sub>0p)" using gtime_fresh by auto
      also have "... = (\<omega>\<^sub>1 @@ \<tau>\<^sub>1) $$ (Rv \<mu>\<^sub>0p)" using bep by (auto simp add: eqon_def)
      also have "... = ?\<nu>\<^sub>\<beta> $$ (Rv \<mu>p)" using gtime_fresh by auto
      finally have mup: "(?\<nu>\<^sub>0 \<tau>) $$ (Rv \<mu>p) = ?\<nu>\<^sub>\<beta> $$ (Rv \<mu>p)" .

      show "Vagree (?\<nu>\<^sub>0 \<tau>) ?\<nu>\<^sub>\<beta> \<V>\<^sub>\<mu>" apply (rule Vagree_by_sortI) 
        using mu mup by (simp_all add: eqon_def gtset_def)
    qed

    hence "Vagree (?\<nu>\<^sub>0 \<tau>) ?\<nu>\<^sub>\<beta> ((-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>f \<inter> -?X\<^sub>1) \<union> \<V>\<^sub>\<mu>)"
      using agree_beta apply (rule Vagree_union_antimon) by blast
    moreover have "Vagree ?\<nu>\<^sub>\<beta> (trepv ?\<nu>\<^sub>\<beta> rec []) (-{Tv rec})" using Vagree_trepv by simp
    ultimately have "Vagree (?\<nu>\<^sub>0 \<tau>) (trepv ?\<nu>\<^sub>\<beta> rec []) (\<V>\<^sub>\<mu> \<union> (-{Tv rec} \<inter> -?X\<^sub>1 \<inter> -\<V>\<^sub>\<mu>\<^sub>f))"
      apply (rule Vagree_trans_eq) using gtime_bounds(1) by force 

    moreover have "FVP (\<pi>\<^sub>I I) live_par_beta \<subseteq> \<V>\<^sub>\<mu> \<union> (-{Tv rec} \<inter> -?X\<^sub>1 \<inter> -\<V>\<^sub>\<mu>\<^sub>f)"
      using FVP_rChp by fastforce

    ultimately show "\<exists>\<omega>\<^sub>2'. (?\<nu>\<^sub>0 \<tau>, \<tau>\<^sub>2, Fin \<omega>\<^sub>2') \<in> chp_sem I live_par_beta 
      \<and> Vagree \<omega>\<^sub>2 \<omega>\<^sub>2' (\<V>\<^sub>\<mu> \<union> (-{Tv rec} \<inter> -?X\<^sub>1 \<inter> -\<V>\<^sub>\<mu>\<^sub>f))" 
      using run2 Vagree_sym coincidence_chp_fin by blast
  qed

  then obtain \<omega>\<^sub>1' where alpha_rebased: "(?\<nu>\<^sub>0 \<tau>, \<tau>\<^sub>1, Fin \<omega>\<^sub>1') \<in> chp_sem I live_par_alpha
    \<and> Vagree \<omega>\<^sub>1 \<omega>\<^sub>1' (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>0)" using alpha_rebased by auto
  obtain \<omega>\<^sub>2' where beta_rebased: "(?\<nu>\<^sub>0 \<tau>, \<tau>\<^sub>2, Fin \<omega>\<^sub>2') \<in> chp_sem I live_par_beta 
      \<and> Vagree \<omega>\<^sub>2 \<omega>\<^sub>2' (\<V>\<^sub>\<mu> \<union> (-{Tv rec} \<inter> -?X\<^sub>1 \<inter> -\<V>\<^sub>\<mu>\<^sub>f))" using beta_rebased by auto  

  let ?\<omega>\<^sub>0 = "lmerge \<omega>\<^sub>1' \<omega>\<^sub>2' ?BV\<alpha>"
  obtain \<omega>\<^sub>0 where omega0: "\<omega>\<^sub>0 = ?\<omega>\<^sub>0" by simp

  have seq_fin_agree_time: "Vagree \<omega>\<^sub>1 \<omega>\<^sub>2 \<V>\<^sub>\<mu>"
  proof -
    have "\<V>\<^sub>\<mu>\<^sub>f \<subseteq> -BVP (\<pi>\<^sub>I I) live_par_beta" using BVP_live_par_beta gtime_bounds by blast
    hence "Vagree (trepv ?\<nu>\<^sub>\<beta> rec []) \<omega>\<^sub>2 \<V>\<^sub>\<mu>\<^sub>1" using run2 bound_effect_property_short Vagree_antimon by blast
    moreover have "Vagree ?\<nu>\<^sub>\<beta> (trepv ?\<nu>\<^sub>\<beta> rec []) \<V>\<^sub>\<mu>\<^sub>1" using Vagree_trepv gtime_bounds Vagree_antimon by blast
    ultimately have "Vagree ?\<nu>\<^sub>\<beta> \<omega>\<^sub>2 \<V>\<^sub>\<mu>\<^sub>1" using Vagree_only_trans by blast
    hence 0: "eqon (stR ?\<nu>\<^sub>\<beta>) (stR \<omega>\<^sub>2) (\<pi>\<^sub>R \<V>\<^sub>\<mu>\<^sub>1)" using Vagree_stR_E by blast

    have 1: "\<omega>\<^sub>2 \<in> fml_sem I ((RVar \<mu>) =\<^sub>R (RVar \<mu>\<^sub>1) && (RVar \<mu>p) =\<^sub>R (RVar \<mu>\<^sub>1p))" using seq by simp
    
    have "stR ?\<nu>\<^sub>\<beta> \<mu>\<^sub>1 = stR \<omega>\<^sub>1 \<mu>" using gtime_fresh by auto
    moreover have "stR ?\<nu>\<^sub>\<beta> \<mu>\<^sub>1 = stR \<omega>\<^sub>2 \<mu>\<^sub>1" using 0 unfolding eqon_def gtset1_def by auto
    moreover have "stR \<omega>\<^sub>2 \<mu>\<^sub>1 = stR \<omega>\<^sub>2 \<mu>" using 1 by simp
    ultimately have mu: "stR \<omega>\<^sub>1 \<mu> = stR \<omega>\<^sub>2 \<mu>" by auto
    
    have "stR ?\<nu>\<^sub>\<beta> \<mu>\<^sub>1p = stR \<omega>\<^sub>1 \<mu>p" using gtime_fresh by auto
    moreover have "stR ?\<nu>\<^sub>\<beta> \<mu>\<^sub>1p = stR \<omega>\<^sub>2 \<mu>\<^sub>1p" using 0 unfolding eqon_def gtset1_def by auto
    moreover have "stR \<omega>\<^sub>2 \<mu>\<^sub>1p = stR \<omega>\<^sub>2 \<mu>p" using 1 by simp
    ultimately have "stR \<omega>\<^sub>1 \<mu>p = stR \<omega>\<^sub>2 \<mu>p" by auto

    thus ?thesis using mu Vagree_def by (simp add: gtset_def)
  qed
    
  have alt_fin_agree_time: "Vagree \<omega>\<^sub>1' \<omega>\<^sub>2' \<V>\<^sub>\<mu>"
  proof -
    have "Vagree \<omega>\<^sub>1' \<omega>\<^sub>1 \<V>\<^sub>\<mu>" using alpha_rebased Vagree_antimon Vagree_sym gtime_bounds by auto
    hence "Vagree \<omega>\<^sub>1' \<omega>\<^sub>2 \<V>\<^sub>\<mu>" using seq_fin_agree_time Vagree_only_trans by blast
    moreover have "Vagree \<omega>\<^sub>2 \<omega>\<^sub>2' \<V>\<^sub>\<mu>" using beta_rebased Vagree_antimon by blast
    ultimately show "Vagree \<omega>\<^sub>1' \<omega>\<^sub>2' \<V>\<^sub>\<mu>" using Vagree_only_trans by blast
  qed
  hence "Vagreebot (Fin \<omega>\<^sub>1') (Fin \<omega>\<^sub>2') \<V>\<^sub>\<mu>" using Vagreebot_def by simp

  hence run: "(?\<nu>\<^sub>0 \<tau>, addrec \<tau> rec, Fin ?\<omega>\<^sub>0) \<in> chp_sem I (live_par_alpha par live_par_beta)"
    using nojunk com1 com2 alpha_rebased beta_rebased by fastforce

  have seq_alt_agree_time: "Vagree \<omega>\<^sub>2 ?\<omega>\<^sub>0 \<V>\<^sub>\<mu>"
  proof -
    have "Vagree \<omega>\<^sub>1 \<omega>\<^sub>1' \<V>\<^sub>\<mu>" using alpha_rebased gtime_bounds by auto  
    hence "Vagree \<omega>\<^sub>2 \<omega>\<^sub>1' \<V>\<^sub>\<mu>" using seq_fin_agree_time Vagree_only_trans Vagree_sym by blast
    moreover have "Vagree \<omega>\<^sub>2 \<omega>\<^sub>2' \<V>\<^sub>\<mu>" using beta_rebased by auto
    ultimately show ?thesis using lmerge_bound_vars by (metis (no_types, lifting) Int_absorb)
  qed

  have fin_states_on_alpha: "Vagree \<omega>\<^sub>1 \<omega>\<^sub>2 (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>f \<inter> ?BV\<alpha> \<inter> -\<V>\<^sub>\<mu>)"
  proof -
    have "Vagree \<omega>\<^sub>1 ?\<nu>\<^sub>\<beta> (-{Tv rec} \<inter> (-\<V>\<^sub>\<mu> \<inter> -\<V>\<^sub>\<mu>\<^sub>f))" 
      using vagree_fin_ini apply (rule Vagree_antimon) by blast
    hence "Vagree \<omega>\<^sub>1 (trepv ?\<nu>\<^sub>\<beta> rec []) ((-{Tv rec} \<inter> (-\<V>\<^sub>\<mu> \<inter> -\<V>\<^sub>\<mu>\<^sub>f)) \<inter> (-{Tv rec}))"
      using Vagree_trepv Vagree_trans by blast
    moreover have "Vagree (trepv ?\<nu>\<^sub>\<beta> rec []) \<omega>\<^sub>2 (-BVP(\<pi>\<^sub>I I) live_par_beta)"
      using bound_effect_property_short run2 by presburger
    ultimately show "Vagree \<omega>\<^sub>1 \<omega>\<^sub>2 (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>f \<inter> ?BV\<alpha> \<inter> -\<V>\<^sub>\<mu>)"
      apply (rule Vagree_trans_antimon) using gtime_bounds disjoint_state_live_par by blast
  qed

  (* transfer postcondition *)
  have post: "?\<omega>\<^sub>0 @@ (addrec \<tau> rec) \<in> fml_sem I (LiveParP ((TVar hid0) \<circ>\<^sub>T (TVar his)))"
  proof -
    have "Vagree ((trepv \<omega>\<^sub>2 rec []) @@ \<tau>\<^sub>2) (trepv \<omega>\<^sub>2 rec []) (-{Tv rec})"
      by (metis Vagree_sym Vagree_trepv com2 addrec_tfilter_commute sttconc_addrec)
    moreover have "Vagree (trepv \<omega>\<^sub>2 rec []) ?\<omega>\<^sub>0 (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>f)"
    proof -
      (* bound by \<alpha> *)
      have "Vagree \<omega>\<^sub>1' ?\<omega>\<^sub>0 ?BV\<alpha>" using Vagree_sym lmerge_vagree by blast
      hence "Vagree \<omega>\<^sub>1 ?\<omega>\<^sub>0 (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>0 \<inter> ?BV\<alpha>)" using alpha_rebased Vagree_trans by blast
      hence on_alpha: "Vagree \<omega>\<^sub>2 ?\<omega>\<^sub>0 (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>f \<inter> ?BV\<alpha> \<inter> -\<V>\<^sub>\<mu>)" 
        using fin_states_on_alpha by (simp add: Vagree_def)

      (* not bound by \<alpha> but bound by \<beta> *)
      have "Vagree \<omega>\<^sub>2 \<omega>\<^sub>2' (\<V>\<^sub>\<mu> \<union> (-{Tv rec} \<inter> -?X\<^sub>1 \<inter> -\<V>\<^sub>\<mu>\<^sub>f))" using beta_rebased by simp
      hence "Vagree \<omega>\<^sub>2 \<omega>\<^sub>2' (?BV\<beta> \<inter> -{Tv rec} \<inter> -\<V>\<^sub>\<mu>)" 
        apply (rule Vagree_antimon) using BVP_live_par_beta by fastforce
      moreover have "Vagree \<omega>\<^sub>2' ?\<omega>\<^sub>0 (-?BV\<alpha>)" 
        using lmerge_vagree Vagree_sym by blast
      ultimately have "Vagree \<omega>\<^sub>2 ?\<omega>\<^sub>0 ((?BV\<beta> \<inter> -{Tv rec} \<inter> -\<V>\<^sub>\<mu>) \<inter> (-?BV\<alpha>))"
        using Vagree_trans by blast

      (* not bound by \<alpha> and \<beta> *)
      moreover have "Vagree ?\<omega>\<^sub>0 \<omega>\<^sub>2 (-?BV\<alpha> \<inter> -?BV\<beta> \<inter> (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>0 \<inter> -\<V>\<^sub>\<mu> \<inter> -\<V>\<^sub>\<mu>\<^sub>1))"
      proof -
        have "Vagree ?\<omega>\<^sub>0 \<omega>\<^sub>2' (-?BV\<alpha>)" using lmerge_vagree by blast
        moreover have "Vagree (?\<nu>\<^sub>0 \<tau>) \<omega>\<^sub>2' (-?BV\<beta>)"
          using beta_rebased bound_effect_property_short by blast
        ultimately have "Vagree ?\<omega>\<^sub>0 (?\<nu>\<^sub>0 \<tau>) (-?BV\<alpha> \<inter> -?BV\<beta>)"
          using Vagree_trans Vagree_sym by blast
        hence "Vagree ?\<omega>\<^sub>0 (trepv ?\<nu>\<^sub>\<alpha> rec []) (-?BV\<alpha> \<inter> -?BV\<beta> \<inter> (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>0))" 
          using inis_agree Vagree_trans by blast
        hence "Vagree ?\<omega>\<^sub>0 \<omega>\<^sub>1 (-?BV\<alpha> \<inter> -?BV\<beta> \<inter> (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>0) \<inter> -?BV\<alpha>)"
          using bound_effect_property_short run1 Vagree_trans by blast
        hence "Vagree ?\<omega>\<^sub>0 \<omega>\<^sub>1 (-?BV\<alpha> \<inter> -?BV\<beta> \<inter> (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>0))"
          apply (rule Vagree_eq) by auto
        hence "Vagree ?\<omega>\<^sub>0 ?\<nu>\<^sub>\<beta> (-?BV\<alpha> \<inter> -?BV\<beta> \<inter> (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>0) \<inter> (-{Tv rec} \<inter> (-\<V>\<^sub>\<mu> \<inter> -\<V>\<^sub>\<mu>\<^sub>1)))"
          using vagree_fin_ini Vagree_trans by blast
        hence "Vagree ?\<omega>\<^sub>0 (trepv ?\<nu>\<^sub>\<beta> rec []) (-?BV\<alpha> \<inter> -?BV\<beta> \<inter> (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>0) \<inter> (-{Tv rec} \<inter> (-\<V>\<^sub>\<mu> \<inter> -\<V>\<^sub>\<mu>\<^sub>1)) \<inter> (-{Tv rec}))"
          using Vagree_trans Vagree_trepv by blast
        hence "Vagree ?\<omega>\<^sub>0 \<omega>\<^sub>2 (-?BV\<alpha> \<inter> -?BV\<beta> \<inter> (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>0) \<inter> (-{Tv rec} \<inter> (-\<V>\<^sub>\<mu> \<inter> -\<V>\<^sub>\<mu>\<^sub>1)) \<inter> (-{Tv rec}) \<inter> -?BV\<beta>)"
          using bound_effect_property_short run2 Vagree_trans by blast
        thus "Vagree ?\<omega>\<^sub>0 \<omega>\<^sub>2 (-?BV\<alpha> \<inter> -?BV\<beta> \<inter> (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>0 \<inter> -\<V>\<^sub>\<mu> \<inter> -\<V>\<^sub>\<mu>\<^sub>1))"
          apply (rule Vagree_eq) by auto
      qed

      ultimately have "Vagree ?\<omega>\<^sub>0 \<omega>\<^sub>2 (((?BV\<beta> \<inter> -{Tv rec} \<inter> -\<V>\<^sub>\<mu>) \<inter> (-?BV\<alpha>)) \<union> (-?BV\<alpha> \<inter> -?BV\<beta> \<inter> (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>0 \<inter> -\<V>\<^sub>\<mu> \<inter> -\<V>\<^sub>\<mu>\<^sub>1)))"
        using Vagree_sym Vagree_union by blast
      hence on_alpha_compl: "Vagree ?\<omega>\<^sub>0 \<omega>\<^sub>2 (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>f \<inter> -?BV\<alpha> \<inter> -\<V>\<^sub>\<mu>)"
        apply (rule Vagree_antimon) by auto

      hence "Vagree ?\<omega>\<^sub>0 \<omega>\<^sub>2 ((-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>f \<inter> -?BV\<alpha> \<inter> -\<V>\<^sub>\<mu>) \<union> (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>f \<inter> ?BV\<alpha> \<inter> -\<V>\<^sub>\<mu>))" 
        using on_alpha Vagree_union Vagree_sym by blast
      hence "Vagree ?\<omega>\<^sub>0 \<omega>\<^sub>2 (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>f \<inter> -\<V>\<^sub>\<mu>)"
        apply (rule Vagree_eq) by auto

      hence "Vagree ?\<omega>\<^sub>0 \<omega>\<^sub>2 (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>f \<inter> -\<V>\<^sub>\<mu> \<union> \<V>\<^sub>\<mu>)" 
        using Vagree_union Vagree_sym seq_alt_agree_time by blast
      hence "Vagree ?\<omega>\<^sub>0 \<omega>\<^sub>2 (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>f)" apply (rule Vagree_antimon) by auto
                                                                              
      thus "Vagree (trepv \<omega>\<^sub>2 rec []) ?\<omega>\<^sub>0 (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>f)" by (simp add: Vagree_def) 
    qed
 
    ultimately have "Vagree ((trepv \<omega>\<^sub>2 rec []) @@ \<tau>\<^sub>2) ?\<omega>\<^sub>0 (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>f)"
      apply (rule Vagree_trans_antimon) by simp
    moreover have "Vagree ?\<omega>\<^sub>0 (?\<omega>\<^sub>0 @@ (addrec \<tau> rec)) (-{Tv rec})"
      using Vagree_trepv sttconc_addrec by simp
    ultimately have "Vagree ((trepv \<omega>\<^sub>2 rec []) @@ \<tau>\<^sub>2) (?\<omega>\<^sub>0 @@ (addrec \<tau> rec)) (-{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>f)"
      apply (rule Vagree_trans_antimon) by simp

    moreover have "FVE (\<pi>\<^sub>I I) (LiveParP ((TVar hid0) \<circ>\<^sub>T (TVar his))) \<subseteq> -{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>f"
    proof -
      have 0: "FVE (\<pi>\<^sub>I I) ((TVar hid0) \<circ>\<^sub>T (TVar his)) \<subseteq> -{Tv rec} \<inter> -\<V>\<^sub>\<mu>\<^sub>f" 
        using FVE_Concat_TVars unfolding gtset0_def gtset1_def by auto
      show ?thesis using FVE_Psymb apply (rule subset_trans) using 0 unfolding FVV_def by auto
    qed
  
    ultimately have "Vagree ((trepv \<omega>\<^sub>2 rec []) @@ \<tau>\<^sub>2) (?\<omega>\<^sub>0 @@ (addrec \<tau> rec)) (FVE (\<pi>\<^sub>I I) (LiveParP ((TVar hid0) \<circ>\<^sub>T (TVar his))))"
      using Vagree_antimon by blast
  
    moreover have "(trepv \<omega>\<^sub>2 rec []) @@ \<tau>\<^sub>2 \<in> fml_sem I (LiveParP ((TVar hid0) \<circ>\<^sub>T (TVar his)))" 
      using seq by auto
 
    ultimately show "?\<omega>\<^sub>0 @@ (addrec \<tau> rec) \<in> fml_sem I (LiveParP ((TVar hid0) \<circ>\<^sub>T (TVar his)))"
      using coincidence_fml_FVE seq by blast
  qed

  have 0: "stT ?\<omega>\<^sub>0 = stT (?\<nu>\<^sub>0 \<tau>)" by (metis Vagree_alltvars bound_effect_on_state(2) run)
  have "?\<omega>\<^sub>0 = trepv (trepv (trepv \<omega>\<^sub>0 his \<tau>) hid0 (stT \<nu> rec)) rec (stT \<nu> rec)"
    apply (rule state_eq_by_sortI) using 0 omega0 by auto
  hence post: "?\<omega>\<^sub>0 @@ (addrec \<tau> rec) \<in> fml_sem I (LiveParP (TVar rec))"
    using post by (simp add: args_sem_def sttconc_addrec)

  have "Vagree (?\<nu>\<^sub>0 \<tau>) \<nu> (-{Tv hid0, Tv his})" using Vagree_def by auto
  moreover have "-{Tv hid0, Tv his} \<supseteq> FVP (\<pi>\<^sub>I I) (live_par_alpha par live_par_beta)"  
  proof -
    have "FVP (\<pi>\<^sub>I I) (live_par_alpha par live_par_beta) \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R" using wf_live_par FVP_bound_rvars by blast
    thus ?thesis by auto
  qed
  ultimately obtain \<omega> where run: "(\<nu>, addrec \<tau> rec, Fin \<omega>) \<in> chp_sem I (live_par_alpha par live_par_beta)
    \<and> Vagree ?\<omega>\<^sub>0 \<omega> (-{Tv hid0, Tv his})"
    using run coincidence_chp_fin by blast

  have "Vagree ?\<omega>\<^sub>0 \<omega> (FVE (\<pi>\<^sub>I I) (LiveParP (TVar rec)))"
  proof -
    have 0: "FVE (\<pi>\<^sub>I I) (TVar rec) \<subseteq> -{Tv his, Tv hid0}" using FVE_TVar by auto
    have "FVE (\<pi>\<^sub>I I) (LiveParP (TVar rec)) \<subseteq> -(\<iota>\<^sub>T \<V>\<^sub>T) \<union> -{Tv his, Tv hid0}"
      using FVE_Psymb apply (rule subset_trans) using 0 unfolding FVV_def by auto
    hence "FVE (\<pi>\<^sub>I I) (LiveParP (TVar rec)) \<subseteq> -{Tv his, Tv hid0}" by auto
    thus ?thesis using Vagree_antimon run by blast
  qed

  hence "\<omega> @@ (addrec \<tau> rec) \<in> fml_sem I (LiveParP (TVar rec))"
    using post Vagree_sttconc_cong coincidence_fml_FVE by blast

  thus "\<nu> \<in> fml_sem I (\<langle> live_par_alpha par live_par_beta \<rangle> LiveParP (TVar rec))" 
    using run by auto
qed

end