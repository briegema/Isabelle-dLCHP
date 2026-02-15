theory "Computable_Static_Semantics"
imports
  "Syntax"
  "Denotational_Semantics"
  "Least_Static_Semantics"
begin

section \<open>Computable Static Semantics\<close>

text \<open>The theory Static_Semantics provides a precise definition of the notions of free and bound
names by characterizing freeness and boundedness semantically. By the theorem of Rice, these 
notions, however, are not computable. Since the bound effect property and the coincidence properties
continue to hold for any superset, soundness of axioms and uniform substitution continues to hold 
for every overapproximation.

This theory provides the computable static semantics, which overapproximates the 
semantically-defined static semantics. While the sementically-defined static semantics precisely
determines the soundenss of axioms and uniform substitution, the computable static semantics can
be used for the implementation of dLCHP in a theorem prover.\<close>

paragraph \<open>Static Semantics of Spaces\<close>

text \<open>A concrete cspace contains no constant symbols\<close>
fun concrete_cspace :: "cspace \<Rightarrow> bool"
  where
  "concrete_cspace \<top>\<^sub>\<Omega> = True"
| "concrete_cspace (CChan ch) = True"
| "concrete_cspace (CConst i) = False"
| "concrete_cspace (-\<^sub>\<Omega> X) = concrete_cspace X"
| "concrete_cspace (X \<inter>\<^sub>\<Omega> Z) = (concrete_cspace X \<and> concrete_cspace Z)"

fun CN\<^sub>C :: "chan set \<Rightarrow> cspace \<Rightarrow> chan set"
  where
  "CN\<^sub>C X \<top>\<^sub>\<Omega> = UNIV"
| "CN\<^sub>C X (CChan ch) = { ch }"
| "CN\<^sub>C X (CConst i) = X"
 (* Complementation reverses the subset relation of the overapproximation of cspace_sem by CN_cspace, 
    but for concrete cspaces equality holds such that the complementation is correct *)
| "CN\<^sub>C X (-\<^sub>\<Omega> C) = (if concrete_cspace C then -CN\<^sub>C X C else X)"
| "CN\<^sub>C X (Y \<inter>\<^sub>\<Omega> C) = (CN\<^sub>C X Y \<inter> CN\<^sub>C X C)"

text \<open>Over-approximation of channel spaces\<close>
abbreviation OCN\<^sub>C :: "cspace \<Rightarrow> chan set"
  where "OCN\<^sub>C Y \<equiv> CN\<^sub>C \<Omega> Y"

text \<open>Under-approximation of channel spaces\<close>
abbreviation UCN\<^sub>C :: "cspace \<Rightarrow> chan set"
  where "UCN\<^sub>C Z \<equiv> CN\<^sub>C {} Z"

text \<open>A concrete vspace contains no constant symbols\<close>
fun concrete_vspace :: "vspace \<Rightarrow> bool"
  where
  "concrete_vspace \<top>\<^sub>R = True"
| "concrete_vspace (VRVar x) = True"
| "concrete_vspace (VTVar h) = True"
| "concrete_vspace (VRConst i) = False"
| "concrete_vspace (-\<^sub>V X) = concrete_vspace X"
| "concrete_vspace (X \<inter>\<^sub>V Z) = (concrete_vspace X \<and> concrete_vspace Z)"

lemma concrete_vspace_BTCTop [simp, intro]: "concrete_vspace \<top>\<^sub>T"
  by (simp add: VTTop_def)

lemma concrete_vspace_VTop [simp, intro]: "concrete_vspace \<top>\<^sub>V"
  by (simp add: VTop_def VCup_def)

lemma concrete_vspace_VBot [simp, intro]: "concrete_vspace \<bottom>\<^sub>V"
  by (simp add: VBot_def)

fun FV\<^sub>V :: "rvar set \<Rightarrow> vspace \<Rightarrow> variable set"
  where
  "FV\<^sub>V V \<top>\<^sub>R = \<iota>\<^sub>R \<V>\<^sub>R"
| "FV\<^sub>V V (VRVar x) = {Rv x}"
| "FV\<^sub>V V (VTVar h) = {Tv h}"
| "FV\<^sub>V V (VRConst X) = \<iota>\<^sub>R V"
| "FV\<^sub>V V (-\<^sub>V X) = (-FV\<^sub>V V X \<inter> \<iota>\<^sub>T \<V>\<^sub>T \<union> (if concrete_vspace X then -FV\<^sub>V V X \<inter> \<iota>\<^sub>R \<V>\<^sub>R else (\<iota>\<^sub>R V)))"
| "FV\<^sub>V V (X \<inter>\<^sub>V Z) = FV\<^sub>V V X \<inter> FV\<^sub>V V Z"

text \<open>Over-approximation of variable spaces\<close>
abbreviation UAV\<^sub>V :: "vspace \<Rightarrow> variable set"
  where "UAV\<^sub>V Z \<equiv> FV\<^sub>V \<V>\<^sub>R Z"

text \<open>Under-approximation of variable spaces\<close>
abbreviation LAV\<^sub>V :: "vspace \<Rightarrow> variable set"
  where "LAV\<^sub>V Z \<equiv> FV\<^sub>V {} Z"

lemma partitionI: "\<pi>\<^sub>V Z = X \<Longrightarrow> \<pi>\<^sub>C Z = Y \<Longrightarrow> Z = \<iota>\<^sub>V X \<union> \<iota>\<^sub>C Y"
  apply (auto simp add: pi_vars_def pi_comtar_def iota_vars_def iota_comtar_def)
  by (metis bindr.exhaust)

lemma \<pi>\<^sub>V_setminus [simp]: "\<pi>\<^sub>V (U - W) = \<pi>\<^sub>V U - \<pi>\<^sub>V W" by (auto simp add: pi_vars_def)
lemma \<pi>\<^sub>C_setminus [simp]: "\<pi>\<^sub>C (U - W) = \<pi>\<^sub>C U - \<pi>\<^sub>C W" by (auto simp add: pi_comtar_def)


lemma FV\<^sub>V_VTop [simp, intro]: "FV\<^sub>V V \<top>\<^sub>V = \<V>"
  by (auto simp add: VTop_def VCup_def VTTop_def compose_allvars)

lemma FV\<^sub>V_VBot [simp, intro]: "FV\<^sub>V V \<bottom>\<^sub>V = {}"
  by (simp add: VBot_def)
 



definition CN\<^sub>V :: "vspace \<Rightarrow> comtar set"
  where "CN\<^sub>V Z = { (h, ch) | h ch. Tv h \<in> UAV\<^sub>V Z }"


lemma CN\<^sub>V_VBot_def [simp]: "CN\<^sub>V \<bottom>\<^sub>V = {}"
  by (simp add: CN\<^sub>V_def)



subsection \<open>Static Semantics of Terms\<close>

text \<open>Free variables of terms\<close>
fun FV\<^sub>R :: "rtrm \<Rightarrow> variable set" and
    FV\<^sub>T :: "ttrm \<Rightarrow> variable set" and
    FV\<^sub>A :: "arg \<Rightarrow> variable set"
  where
  "FV\<^sub>R (RVar x) = {Rv x}" 
| "FV\<^sub>R (RConst b c n) = {}" 
| "FV\<^sub>R (RFunc b f Z \<Theta>) = (UAV\<^sub>V Z \<union> (\<Union>e\<in>(set \<Theta>). FV\<^sub>A e))"
| "FV\<^sub>R (Number l) = {}"
| "FV\<^sub>R (Plus \<theta> \<eta>) = FV\<^sub>R \<theta> \<union> FV\<^sub>R \<eta>"
| "FV\<^sub>R (Times \<theta> \<eta>) = FV\<^sub>R \<theta> \<union> FV\<^sub>R \<eta>"
| "FV\<^sub>R (ChanOf te) = FV\<^sub>T te"
| "FV\<^sub>R (ValOf te) = FV\<^sub>T te"
| "FV\<^sub>R (TimeOf te) = FV\<^sub>T te"
| "FV\<^sub>R (LenT te) = FV\<^sub>T te"

| "FV\<^sub>T (TVar h) = {Tv h}"
| "FV\<^sub>T (TConst c n) = {}"
| "FV\<^sub>T (TFunc f Z \<Theta>) = (UAV\<^sub>V Z \<union> (\<Union>e\<in>(set \<Theta>). FV\<^sub>A e))"
| "FV\<^sub>T Empty = {}"
| "FV\<^sub>T (Concat te\<^sub>1 te\<^sub>2) = FV\<^sub>T te\<^sub>1 \<union> FV\<^sub>T te\<^sub>2"
| "FV\<^sub>T (Proj te Y) = FV\<^sub>T te"
| "FV\<^sub>T (ComItm ch \<eta>\<^sub>1 \<eta>\<^sub>2) = FV\<^sub>R \<eta>\<^sub>1 \<union> FV\<^sub>R \<eta>\<^sub>2"
| "FV\<^sub>T (Access te \<theta>) = FV\<^sub>T te \<union> FV\<^sub>R \<theta>"

| "FV\<^sub>A (RArg \<eta>) = FV\<^sub>R \<eta>"
| "FV\<^sub>A (TArg te) = FV\<^sub>T te" 

text \<open>Accessed channels of terms\<close>

text \<open>An access free trace term contains no access operation\<close>
fun access_free :: "ttrm \<Rightarrow> bool"
  where 
  "access_free (TVar h) = True"
| "access_free (TConst c n) = True"
| "access_free (TFunc f Z \<Theta>) = False"
| "access_free Empty = True"
| "access_free (ComItm ch \<eta>\<^sub>1 \<eta>\<^sub>2) = True" 
| "access_free (Concat te\<^sub>1 te\<^sub>2) = (access_free te\<^sub>1 \<and> access_free te\<^sub>2)" 
| "access_free (Proj te Y) = access_free te"
| "access_free (Access te \<theta>) = False"

fun CN\<^sub>R :: "rtrm \<Rightarrow> comtar set" and
    CN\<^sub>T :: "ttrm \<Rightarrow> comtar set" and
    CN\<^sub>A :: "arg \<Rightarrow> comtar set"
  where
  "CN\<^sub>R (RVar x) = {}"
| "CN\<^sub>R (RConst b c n) = {}"
| "CN\<^sub>R (RFunc b f Z \<Theta>) = (CN\<^sub>V Z \<union> (\<Union>e\<in>(set \<Theta>). CN\<^sub>A e))"
| "CN\<^sub>R (Number l) = {}"
| "CN\<^sub>R (Plus \<theta> \<eta>) = CN\<^sub>R \<theta> \<union> CN\<^sub>R \<eta>"
| "CN\<^sub>R (Times \<theta> \<eta>) = CN\<^sub>R \<theta> \<union> CN\<^sub>R \<eta>"
| "CN\<^sub>R (ChanOf te) = CN\<^sub>T te"
| "CN\<^sub>R (ValOf te) = CN\<^sub>T te"
| "CN\<^sub>R (TimeOf te) = CN\<^sub>T te"
| "CN\<^sub>R (LenT te) = CN\<^sub>T te"

| "CN\<^sub>T (TVar h) = {h} \<times> \<Omega>" 
| "CN\<^sub>T (TConst c n) = {}"
| "CN\<^sub>T (TFunc f Z \<Theta>) = (CN\<^sub>V Z \<union> (\<Union>e\<in>(set \<Theta>). CN\<^sub>A e))"
| "CN\<^sub>T Empty = {}"
| "CN\<^sub>T (Concat te\<^sub>1 te\<^sub>2) = CN\<^sub>T te\<^sub>1 \<union> CN\<^sub>T te\<^sub>2"
| "CN\<^sub>T (Proj te Y) = (if access_free te then CN\<^sub>T te \<inter> (\<V>\<^sub>T \<times> OCN\<^sub>C Y) else CN\<^sub>T te)"
| "CN\<^sub>T (ComItm ch \<eta>\<^sub>1 \<eta>\<^sub>2) = {}"
| "CN\<^sub>T (Access te \<theta>) = CN\<^sub>T te \<union> CN\<^sub>R \<theta>"

| "CN\<^sub>A (RArg \<eta>) = CN\<^sub>R \<eta>"
| "CN\<^sub>A (TArg te) = CN\<^sub>T te"



subsection \<open>Static Semantics for Formulas and Communicating Hybrid Programs (CHPs)\<close>

paragraph \<open>Bound Names of CHPs\<close>

text \<open>Bound variables of CHPs\<close>
fun BV :: "chp \<Rightarrow> variable set"
  where
  "BV (Chp a Z Y) = UAV\<^sub>V Z"
| "BV (x := \<theta>) = { Rv x }"
| "BV (x := *) = { Rv x }"
| "BV (Test \<phi>) = {}"
| "BV (Evolution x \<theta> \<phi>) = bvrident x"
| "BV (Choice \<alpha> \<beta>) = BV \<alpha> \<union> BV \<beta>"
| "BV (Compose \<alpha> \<beta>) = BV \<alpha> \<union> BV \<beta>"
| "BV (Loop \<alpha>) = BV \<alpha>"
| "BV (Send ch h \<theta>) = { Tv h }"
| "BV (Receive ch h x) = { Tv h, Rv x }"
| "BV (\<alpha> par \<beta>) = BV \<alpha> \<union> BV \<beta>"

text \<open>Bound recorder-channel pairs of CHPs\<close>
fun TCN\<^sub>P :: "chp \<Rightarrow> comtar set"
  where 
  "TCN\<^sub>P (Chp a Z Y) = \<pi>\<^sub>T (UAV\<^sub>V Z) \<times> OCN\<^sub>C Y"
| "TCN\<^sub>P (x := \<theta>) = {}"  
| "TCN\<^sub>P (x := *) = {}"
| "TCN\<^sub>P (Test \<phi>) = {}"
| "TCN\<^sub>P (Evolution x \<theta> \<phi>) = {}"
| "TCN\<^sub>P (Choice \<alpha> \<beta>) = TCN\<^sub>P \<alpha> \<union> TCN\<^sub>P \<beta>"
| "TCN\<^sub>P (Compose \<alpha> \<beta>) = TCN\<^sub>P \<alpha> \<union> TCN\<^sub>P \<beta>"
| "TCN\<^sub>P (Loop \<alpha>) = TCN\<^sub>P \<alpha>"
| "TCN\<^sub>P (Send ch h \<theta>) = { (h, ch) }"
| "TCN\<^sub>P (Receive ch h x) = { (h, ch) }"
| "TCN\<^sub>P (\<alpha> par \<beta>) = TCN\<^sub>P \<alpha> \<union> TCN\<^sub>P \<beta>"

text \<open>Bound recorder-channel pairs of CHPs\<close>
fun CN\<^sub>P :: "chp \<Rightarrow> chan set"
  where 
  "CN\<^sub>P (Chp a Z Y) = OCN\<^sub>C Y"
| "CN\<^sub>P (x := \<theta>) = {}"  
| "CN\<^sub>P (x := *) = {}"
| "CN\<^sub>P (Test \<phi>) = {}"
| "CN\<^sub>P (Evolution x \<theta> \<phi>) = {}"
| "CN\<^sub>P (Choice \<alpha> \<beta>) = CN\<^sub>P \<alpha> \<union> CN\<^sub>P \<beta>"
| "CN\<^sub>P (Compose \<alpha> \<beta>) = CN\<^sub>P \<alpha> \<union> CN\<^sub>P \<beta>"
| "CN\<^sub>P (Loop \<alpha>) = CN\<^sub>P \<alpha>"
| "CN\<^sub>P (Send ch h \<theta>) = { ch }"
| "CN\<^sub>P (Receive ch h x) = { ch }"
| "CN\<^sub>P (\<alpha> par \<beta>) = CN\<^sub>P \<alpha> \<union> CN\<^sub>P \<beta>"

text \<open>Must-bound variables are those variables that are overwritten on each execution path. For real
variables, this is equivalent to be bound on each execution path. However, recorder variables are
never overwritten, because the communication is appended to them. Consequently, recorder variables
are not must-bound variables.\<close>
fun MBV :: "chp \<Rightarrow> variable set"
  where
  "MBV (Chp a Z Y) = {}"
| "MBV (x := \<theta>) = {Rv x}"
| "MBV (x := *) = {Rv x}"
| "MBV (Test \<phi>) = {}"
| "MBV (Evolution x \<theta> \<phi>) = bvrident x"
| "MBV (Choice \<alpha> \<beta>) = MBV \<alpha> \<inter> MBV \<beta>"
| "MBV (Compose \<alpha> \<beta>) = MBV \<alpha> \<union> MBV \<beta>"
| "MBV (Loop \<alpha>) = {}"
| "MBV (Send ch h \<theta>) = {}"
| "MBV (Receive ch h x) = {Rv x}"
| "MBV (\<alpha> par \<beta>) = MBV \<alpha> \<union> MBV \<beta>"



subparagraph \<open>Free Names of Chps and Formulas\<close>

fun FV\<^sub>P :: "chp \<Rightarrow> variable set" and
    FV\<^sub>F :: "fml \<Rightarrow> variable set" 
  where
  "FV\<^sub>P (Chp a Z Y) = UAV\<^sub>V Z \<inter> \<iota>\<^sub>R \<V>\<^sub>R"
| "FV\<^sub>P (x := \<theta>) = FV\<^sub>R \<theta>"
| "FV\<^sub>P (x := *) = {}"
| "FV\<^sub>P (Test \<phi>) = FV\<^sub>F \<phi>"
| "FV\<^sub>P (Evolution x \<theta> \<phi>) = {Rv (RVarName x)} \<union> FV\<^sub>R \<theta> \<union> FV\<^sub>F \<phi>"
| "FV\<^sub>P (Choice \<alpha> \<beta>) = FV\<^sub>P \<alpha> \<union> FV\<^sub>P \<beta>"
| "FV\<^sub>P (Compose \<alpha> \<beta>) = FV\<^sub>P \<alpha> \<union> (FV\<^sub>P \<beta> - MBV \<alpha>)"
| "FV\<^sub>P (Loop \<alpha>) = FV\<^sub>P \<alpha>" 
| "FV\<^sub>P (Send ch h \<theta>) = {Rv \<mu>} \<union> FV\<^sub>R \<theta>"
| "FV\<^sub>P (Receive ch h x) = {Rv \<mu>}"
| "FV\<^sub>P (\<alpha> par \<beta>) = \<V>\<^sub>\<mu> \<union> FV\<^sub>P \<alpha> \<union> FV\<^sub>P \<beta>"

| "FV\<^sub>F (GPsymb b p Z \<Theta>) = (UAV\<^sub>V Z \<union> (\<Union>e\<in>(set \<Theta>). FV\<^sub>A e))"
| "FV\<^sub>F (Geq \<theta> \<eta>) = FV\<^sub>R \<theta> \<union> FV\<^sub>R \<eta>"
| "FV\<^sub>F (Pref \<theta> \<eta>) = FV\<^sub>T \<theta> \<union> FV\<^sub>T \<eta>"
| "FV\<^sub>F (Not \<phi>) = FV\<^sub>F \<phi>"
| "FV\<^sub>F (And \<phi> \<psi>) = FV\<^sub>F \<phi> \<union> FV\<^sub>F \<psi>"
| "FV\<^sub>F (Exists z \<phi>) = FV\<^sub>F \<phi> - {z}"
| "FV\<^sub>F (Box \<alpha> \<psi>) = FV\<^sub>P \<alpha> \<union> (FV\<^sub>F \<psi> - MBV \<alpha>)"
| "FV\<^sub>F (AcBox \<alpha> A C \<psi>) = FV\<^sub>P \<alpha> \<union> FV\<^sub>F A \<union> FV\<^sub>F C \<union> (FV\<^sub>F \<psi> - MBV \<alpha>)" 
| "FV\<^sub>F (ChanIn \<theta> Y) = FV\<^sub>R \<theta>"



text \<open>Accessed channels for formulas\<close>

fun CN\<^sub>F :: "fml \<Rightarrow> comtar set"
  where
  "CN\<^sub>F (GPsymb b p Z \<Theta>) = (CN\<^sub>V Z \<union> (\<Union>e\<in>(set \<Theta>). CN\<^sub>A e))"
| "CN\<^sub>F (Geq \<theta> \<eta>) = CN\<^sub>R \<theta> \<union> CN\<^sub>R \<eta>"
| "CN\<^sub>F (Pref \<theta> \<eta>) = CN\<^sub>T \<theta> \<union> CN\<^sub>T \<eta>"
| "CN\<^sub>F (Not \<phi>) = CN\<^sub>F \<phi>"
| "CN\<^sub>F (And \<phi> \<psi>) = CN\<^sub>F \<phi> \<union> CN\<^sub>F \<psi>"
| "CN\<^sub>F (Exists z \<phi>) = CN\<^sub>F \<phi>"
| "CN\<^sub>F (Box \<alpha> \<psi>) = CN\<^sub>F \<psi>"
| "CN\<^sub>F (AcBox \<alpha> A C \<psi>) = CN\<^sub>F A \<union> CN\<^sub>F C \<union> CN\<^sub>F \<psi>"
| "CN\<^sub>F (ChanIn \<theta> Y) = CN\<^sub>R \<theta>"



subsection \<open>Simple Upper Bounds for Well-formed Formulas and Programs\<close>

text \<open>The following upper bounds on the static semantics hold for all terms, formulas, or programs
because they are consequences of their well-formedness.\<close>

lemma FV\<^sub>R_QRpolynom_only_rvars:
  assumes "isQRpolynom \<theta>"
    shows "FV\<^sub>R \<theta> \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R"
  apply (induction rule: QRpolynom_induct)
  by (auto simp add: assms QRConst_def QRFunc_def)

lemma FV\<^sub>F_FOL\<^sub>R_only_rvars:
  assumes "isFOL\<^sub>R \<phi>"
  shows "FV\<^sub>F \<phi> \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R"
  apply (induction \<phi> rule: FOL\<^sub>R_induct)
  using assms FV\<^sub>R_QRpolynom_only_rvars by (auto simp add: QRGPsymb_def)

lemma CN_QRPolynom_empty:
  assumes "isQRpolynom \<theta>" 
    shows "CN\<^sub>R \<theta> = {}"
proof (induction \<theta> rule: QRpolynom_induct)
  case IsQRPoly
  thus ?case using assms by auto
next
  case (QRConst c n)
  thus ?case by (simp add: QRConst_def)
next
  case (QRFunc f \<Theta>)
  thus  ?case by (simp add: QRFunc_def) 
qed (simp_all)

lemma FV\<^sub>P_wf_chp_only_rvars: "wf_chp \<L>\<^sub>C \<alpha> \<Longrightarrow> FV\<^sub>P \<alpha> \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R" 
  apply (induction rule: chp_induct)
  using FV\<^sub>R_QRpolynom_only_rvars FV\<^sub>F_FOL\<^sub>R_only_rvars by auto

lemma MBV_subset_BV: "MBV \<alpha> \<subseteq> BV \<alpha>"
  by (induction rule: chp_induct) (simp_all, auto)

lemma MBV_only_rvars: "MBV \<alpha> \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R"
  by (induction rule: chp_induct) (simp_all, auto)



section \<open>Soundness of the Computable Static Semantics\<close>

text \<open>The computable static semantics is sound if it over-approximates the semantically-defined 
static semantics (see theory Static_Semantics). This is shown by proving that the computable static 
semantics also fulfills the coincidence properties.\<close>

subsection \<open>Correctness of the Static Semantics for Spaces\<close>

lemma CN\<^sub>C_concrete_cspace: "concrete_cspace Y \<Longrightarrow> CN\<^sub>C X Y = cspace_sem J Y"
  by (induction Y) (auto)




lemma FV\<^sub>V_concrete_vspace [simp]: "concrete_vspace Z \<Longrightarrow> FV\<^sub>V V Z = vspace_sem J Z"
  apply (induction Z)
  by (simp_all add: CN\<^sub>C_concrete_cspace tvars_rvars_disjoint_union) 

lemma FV\<^sub>V_tvars: "FV\<^sub>V V Z \<inter> \<iota>\<^sub>T \<V>\<^sub>T = vspace_sem J Z \<inter> \<iota>\<^sub>T \<V>\<^sub>T"
  apply (induction Z)
  apply (simp_all add: iota_rvars_def iota_tvars_def)
  using FV\<^sub>V_concrete_vspace by blast+
                       
lemma OCN\<^sub>C_overapprox: "OCN\<^sub>C Y \<supseteq> cspace_sem J Y"
  apply (induction Y)
  using CN\<^sub>C_concrete_cspace apply simp_all by blast

lemma UCN\<^sub>C_underapprox: "UCN\<^sub>C Y \<subseteq> cspace_sem J Y"
  apply (induction Y)
  using CN\<^sub>C_concrete_cspace apply simp_all by blast+

lemma split_overapprox: "X \<subseteq> Z \<Longrightarrow> X \<subseteq> Z \<inter> \<iota>\<^sub>T \<V>\<^sub>T \<union> \<iota>\<^sub>R \<V>\<^sub>R"
  apply rule
  apply (simp_all add: iota_tvars_def iota_rvars_def)
  using variable.exhaust_sel by blast

lemma UAV\<^sub>V_overapprox: "UAV\<^sub>V Z \<supseteq> vspace_sem J Z"
proof (induction Z)
  case (VCompl Z)
  then show ?case
    apply (simp_all add: tvars_rvars_disjoint_union)
    using FV\<^sub>V_tvars split_overapprox by fast
qed (auto)

lemma LAV\<^sub>V_underapprox: "LAV\<^sub>V Z \<subseteq> vspace_sem J Z"
proof (induction Z)
  case (VCompl Z)
  then show ?case
    apply (cases "concrete_vspace Z")
    using FV\<^sub>V_concrete_vspace apply fastforce
    using FV\<^sub>V_tvars by fastforce
qed (auto) 




lemma FV\<^sub>V_subseteq_CN\<^sub>V: "Tv h \<in> UAV\<^sub>V Z \<Longrightarrow> {h} \<times> \<Omega> \<subseteq> CN\<^sub>V Z"
  unfolding CN\<^sub>V_def by blast



subsection \<open>Coincidence Property for Terms\<close>

text \<open>Projection push down leaves the well-formedness of terms untouched\<close>

lemma list_all_mapI: "(\<And>\<theta>. \<theta> \<in> set \<Theta> \<Longrightarrow> p \<theta> \<Longrightarrow> p (f \<theta>)) \<Longrightarrow> list_all p \<Theta> \<Longrightarrow> list_all p (map f \<Theta>)"
  by (metis (mono_tags, lifting) Ball_set_list_all image_iff list.set_map)


paragraph \<open>Auxiliary Properties for Coincidence Properties of Terms\<close>

text \<open>Set theoretic Property of \<open>Vagree\<close> within \<open>CN\<close> and \<open>FV\<close>\<close>

lemma Vagree_subset: (* in use *)
  "Vagree (sfilter \<nu> (C \<union> Y)) (sfilter \<omega> (C \<union> Y)) (V \<union> X) 
  \<Longrightarrow> Vagree (sfilter \<nu> C) (sfilter \<omega> C) V \<and> Vagree (sfilter \<nu> Y) (sfilter \<omega> Y) X" 
  by (metis Un_Int_eq(1) Un_Int_eq(2) Vagree_and Vagree_sfilter_cong sfilter_trans)

lemma Vagree_subset1: (* in use *)
  "Vagree (sfilter \<nu> ((C\<^sub>1 \<union> C\<^sub>2) \<inter> (\<V>\<^sub>T \<times> Y))) (sfilter \<omega> ((C\<^sub>1 \<union> C\<^sub>2) \<inter> (\<V>\<^sub>T \<times> Y))) (V \<union> X) 
  \<Longrightarrow> Vagree (sfilter \<nu> (C\<^sub>1 \<inter> (\<V>\<^sub>T \<times> Y))) (sfilter \<omega> (C\<^sub>1 \<inter> (\<V>\<^sub>T \<times> Y))) V 
    \<and> Vagree (sfilter \<nu> (C\<^sub>2 \<inter> (\<V>\<^sub>T \<times> Y))) (sfilter \<omega> (C\<^sub>2 \<inter> (\<V>\<^sub>T \<times> Y))) X"
  apply (simp add: Int_Un_distrib2)
  using Vagree_subset by blast






subparagraph \<open>Auxiliaries for \<open>RFunc\<close> and \<open>TFunc\<close>\<close>

lemma RFunc_arg_CN_subset: "\<theta>\<in>set \<Theta> \<Longrightarrow> (CN\<^sub>A \<theta>) \<subseteq> (CN\<^sub>R (RFunc b f Z \<Theta>))" by auto

lemma RFunc_arg_FV_subset: "\<theta>\<in>set \<Theta> \<Longrightarrow> (FV\<^sub>A \<theta>) \<subseteq> (FV\<^sub>R (RFunc b f Z \<Theta>))" by auto

lemma RFunc_Vagree_args:
  assumes "Vagree (sfilter \<nu> (CN\<^sub>R (RFunc b f Z \<Theta>))) (sfilter \<nu>' (CN\<^sub>R (RFunc b f Z \<Theta>))) (FV\<^sub>R (RFunc b f Z \<Theta>))"
    shows "\<theta>\<in>set \<Theta> \<Longrightarrow> Vagree (sfilter \<nu> (CN\<^sub>A \<theta>)) (sfilter \<nu>' (CN\<^sub>A \<theta>)) (FV\<^sub>A \<theta>)"
  by (metis Vagree_or Vagree_sfilter_cong_inter RFunc_arg_CN_subset RFunc_arg_FV_subset assms inf.absorb2)


lemma TFunc_arg_CN_subset:
  "\<forall>\<theta>\<in>set \<Theta>. (CN\<^sub>A \<theta>) \<subseteq> (CN\<^sub>T (TFunc f Z \<Theta>))" by auto

lemma TFunc_arg_FV_subset:
  "\<forall>\<theta>\<in>set \<Theta>. (FV\<^sub>A \<theta>) \<subseteq> (FV\<^sub>T (TFunc f Z \<Theta>))" by auto

lemma TFunc_Vagree_args:
  assumes "Vagree (sfilter \<nu> (CN\<^sub>T (TFunc f Z \<Theta>))) (sfilter \<nu>' (CN\<^sub>T (TFunc f Z \<Theta>))) (FV\<^sub>T (TFunc f Z \<Theta>))"
    shows "\<And>\<theta>. \<theta>\<in>set \<Theta> \<Longrightarrow> Vagree (sfilter \<nu> (CN\<^sub>A \<theta>)) (sfilter \<nu>' (CN\<^sub>A \<theta>)) (FV\<^sub>A \<theta>)"
  by (metis Vagree_or Vagree_sfilter_cong_inter TFunc_arg_CN_subset TFunc_arg_FV_subset assms inf.absorb2)

lemma CN\<^sub>V_image_all_chans: "{z} \<times> \<Omega> \<subseteq> CN\<^sub>V Z \<Longrightarrow> CN\<^sub>V Z `` {z} = \<Omega>"
  by blast

lemma sfilter_CN\<^sub>V_all_chans: "{z} \<times> \<Omega> \<subseteq> CN\<^sub>V Z \<Longrightarrow>  stT (sfilter \<nu> (CN\<^sub>V Z)) z = stT \<nu> z"
  by (simp add: sfilter_def tsfilter_def CN\<^sub>V_image_all_chans)

  

paragraph \<open>Coincidence Property for Terms\<close>

text \<open>The proof of the coincidence property for trace terms requires a generalization of the IH,
which takes into account that a trace term may be in the context of a projection. This generalized
IH must not apply to trace terms, which contain trace access.\<close>

lemma shows rtrm_coincidence:
  "wf_rtrm \<theta> 
  \<Longrightarrow> Vagree (sfilter \<nu> (CN\<^sub>R \<theta>)) (sfilter \<omega> (CN\<^sub>R \<theta>)) (FV\<^sub>R \<theta>) 
  \<Longrightarrow> rtrm_sem I \<theta> \<nu> = rtrm_sem I \<theta> \<omega>" 
  and ttrm_coincidence_proj: "wf_ttrm te
  \<Longrightarrow> Vagree (sfilter \<nu> (CN\<^sub>T (Proj te C))) (sfilter \<omega> (CN\<^sub>T (Proj te C))) (FV\<^sub>T te) 
  \<Longrightarrow> ttrm_sem I (Proj te C) \<nu> = ttrm_sem I (Proj te C) \<omega>" 
  and arg_coincidence: "wf_arg e
  \<Longrightarrow> Vagree (sfilter \<nu> (CN\<^sub>A e)) (sfilter \<omega> (CN\<^sub>A e)) (FV\<^sub>A e) 
  \<Longrightarrow> arg_sem I e \<nu> = arg_sem I e \<omega>"
proof (induction \<theta> and te and e arbitrary: C and C and C)
  case (RVar x)
  thus ?case by (simp add: Vagree_def sfilter_def)
next
  case (RConst b c n)
  thus ?case by simp
next
  case (RFunc b f Z \<Theta>)
  let ?I = "AllRFuncs I b f"
  let ?Z = "vspace_sem (\<pi>\<^sub>I I) Z"

  have "(args_sem_pre I \<Theta> arg_sem \<nu>) = (args_sem_pre I \<Theta> arg_sem \<omega>)"
  proof -
    have "\<forall>\<theta> \<in> set \<Theta>. wf_arg \<theta>" using RFunc.prems(1) by (simp add: Ball_set_list_all)    
    moreover have "\<And>\<theta>. \<theta> \<in> set \<Theta> \<Longrightarrow> Vagree (sfilter \<nu> (CN\<^sub>A \<theta>)) (sfilter \<omega> (CN\<^sub>A \<theta>)) (FV\<^sub>A \<theta>)"   
      using RFunc.prems(2) RFunc_Vagree_args by blast
    ultimately have "\<forall>\<theta> \<in> set \<Theta>. arg_sem I \<theta> \<nu> = arg_sem I \<theta> \<omega>" using RFunc.IH by blast
    thus ?thesis using args_sem_pre_def by simp
  qed

  moreover have "Vagree \<nu> \<omega> ?Z"
  proof -
    have "eqon (stR \<nu>) (stR \<omega>) (\<pi>\<^sub>R (FV\<^sub>R (RFunc b f Z \<Theta>)))" using RFunc Vagree_stR_E stR_sfilter by metis
    moreover have "\<pi>\<^sub>R (vspace_sem (\<pi>\<^sub>I I) Z) \<subseteq> \<pi>\<^sub>R (FV\<^sub>R (RFunc b f Z \<Theta>))" 
      using UAV\<^sub>V_overapprox by (auto simp add: pi_rvars_def)
    ultimately have 0: "eqon (stR \<nu>) (stR \<omega>) (\<pi>\<^sub>R (vspace_sem (\<pi>\<^sub>I I) Z))" by (auto simp add: eqon_def)
  
    have "eqon (stT (sfilter \<nu> (CN\<^sub>R (RFunc b f Z \<Theta>)))) (stT (sfilter \<omega> (CN\<^sub>R (RFunc b f Z \<Theta>)))) (\<pi>\<^sub>T (FV\<^sub>R (RFunc b f Z \<Theta>)))" 
      using RFunc Vagree_stT_E by blast
    hence "eqon (stT (sfilter \<nu> (CN\<^sub>R (RFunc b f Z \<Theta>)))) (stT (sfilter \<omega> (CN\<^sub>R (RFunc b f Z \<Theta>)))) (\<pi>\<^sub>T (UAV\<^sub>V Z))"
      by (simp add: eqon_def)
    hence "eqon (stT \<nu>) (stT \<omega>) (\<pi>\<^sub>T (UAV\<^sub>V Z))" by (simp add: eqon_def tsfilter_access Image_def CN\<^sub>V_def)
    hence 1: "eqon (stT \<nu>) (stT \<omega>) (\<pi>\<^sub>T (vspace_sem (\<pi>\<^sub>I I) Z))"
      using UAV\<^sub>V_overapprox apply (simp add: eqon_def) by blast

    show ?thesis using 0 1 Vagree_by_sortI by simp
  qed
   
  ultimately have "PInterp ?I ?Z \<nu> (args_sem_pre I \<Theta> arg_sem \<nu>) = PInterp ?I ?Z \<omega> (args_sem_pre I \<Theta> arg_sem \<omega>)"
    by (metis (full_types) PInterp_correct is_pinterp_alt)
  thus ?case by simp
next
  case (Number l)
  thus ?case by simp
next
  case (Plus \<theta> \<eta>)
  hence "\<And>e. e\<in>{\<theta>,\<eta>} \<Longrightarrow> Vagree (sfilter \<nu> (CN\<^sub>R e)) (sfilter \<omega> (CN\<^sub>R e)) (FV\<^sub>R e)"  
    by (metis CN\<^sub>R.simps(5) FV\<^sub>R.simps(5) Vagree_subset insertE singleton_iff)
  thus ?case using Plus by simp
next
  case (Times \<theta> \<eta>)
  hence "\<And>e. e\<in>{\<theta>,\<eta>} \<Longrightarrow> Vagree (sfilter \<nu> (CN\<^sub>R e)) (sfilter \<omega> (CN\<^sub>R e)) (FV\<^sub>R e)"
    by (metis CN\<^sub>R.simps(6) FV\<^sub>R.simps(6) Vagree_subset insert_iff singletonD)
  thus ?case using Times by simp
next
  case (ChanOf te)
  hence "Vagree (sfilter \<nu> (CN\<^sub>T (Proj te \<top>\<^sub>\<Omega>))) (sfilter \<omega> (CN\<^sub>T (Proj te \<top>\<^sub>\<Omega>))) (FV\<^sub>T te)" by fastforce
  moreover have "wf_ttrm te" using ChanOf(2) by simp
  ultimately have "ttrm_sem I (Proj te \<top>\<^sub>\<Omega>) \<nu> = ttrm_sem I (Proj te \<top>\<^sub>\<Omega>) \<omega>" using ChanOf.IH by blast
  thus ?case by simp
next
  case (ValOf te)
  hence "Vagree (sfilter \<nu> (CN\<^sub>T (Proj te \<top>\<^sub>\<Omega>))) (sfilter \<omega> (CN\<^sub>T (Proj te \<top>\<^sub>\<Omega>))) (FV\<^sub>T te)" by fastforce
  moreover have "wf_ttrm te" using ValOf(2) by simp
  ultimately have "ttrm_sem I (Proj te \<top>\<^sub>\<Omega>) \<nu> = ttrm_sem I (Proj te \<top>\<^sub>\<Omega>) \<omega>" using ValOf.IH by blast
  thus ?case by simp
next
  case (TimeOf te)
  hence "Vagree (sfilter \<nu> (CN\<^sub>T (Proj te \<top>\<^sub>\<Omega>))) (sfilter \<omega> (CN\<^sub>T (Proj te \<top>\<^sub>\<Omega>))) (FV\<^sub>T te)" by fastforce
  moreover have "wf_ttrm te" using TimeOf(2) by simp
  ultimately have "ttrm_sem I (Proj te \<top>\<^sub>\<Omega>) \<nu> = ttrm_sem I (Proj te \<top>\<^sub>\<Omega>) \<omega>" using TimeOf.IH by blast
  thus ?case by simp
next
  case (LenT te)
  hence "Vagree (sfilter \<nu> (CN\<^sub>T (Proj te \<top>\<^sub>\<Omega>))) (sfilter \<omega> (CN\<^sub>T (Proj te \<top>\<^sub>\<Omega>))) (FV\<^sub>T te)" by fastforce
  moreover have "wf_ttrm te" using LenT(2) by simp
  ultimately have "ttrm_sem I (Proj te \<top>\<^sub>\<Omega>) \<nu> = ttrm_sem I (Proj te \<top>\<^sub>\<Omega>) \<omega>" using LenT.IH by blast
  thus ?case by simp
next
  case (TVar h)
  show ?case
  proof (cases "access_free (TVar h)")
    case True
    then show ?thesis using TVar 
      apply (simp add: Vagree_def tsfilter_access Image_def)
      by (meson OCN\<^sub>C_overapprox tfilter_cong_antimon)
  next
    case False
    then show ?thesis by auto
  qed
next
  case (TConst c n)
  thus ?case by simp
next
  case (TFunc f Z \<Theta>)
  let ?I = "TFuncs I f"
  let ?Z = "vspace_sem (\<pi>\<^sub>I I) Z"

  have "(args_sem_pre I \<Theta> arg_sem \<nu>) = (args_sem_pre I \<Theta> arg_sem \<omega>)"
  proof -
    have "\<forall>\<theta> \<in> set \<Theta>. wf_arg \<theta>" using TFunc.prems(1) by (simp add: Ball_set_list_all)    
    moreover have "\<And>\<theta>. \<theta> \<in> set \<Theta> \<Longrightarrow> Vagree (sfilter \<nu> (CN\<^sub>A \<theta>)) (sfilter \<omega> (CN\<^sub>A \<theta>)) (FV\<^sub>A \<theta>)"   
      using TFunc.prems(2) TFunc_Vagree_args by fastforce
    ultimately have "\<forall>\<theta> \<in> set \<Theta>. arg_sem I \<theta> \<nu> = arg_sem I \<theta> \<omega>" using TFunc.IH by blast
    thus ?thesis using args_sem_pre_def by simp
  qed

  moreover have "Vagree \<nu> \<omega> ?Z"
  proof -
    have "eqon (stR \<nu>) (stR \<omega>) (\<pi>\<^sub>R (FV\<^sub>T (TFunc f Z \<Theta>)))" using TFunc Vagree_stR_E stR_sfilter by metis
    moreover have "\<pi>\<^sub>R (vspace_sem (\<pi>\<^sub>I I) Z) \<subseteq> \<pi>\<^sub>R (FV\<^sub>T (TFunc f Z \<Theta>))" 
      using UAV\<^sub>V_overapprox by (auto simp add: pi_rvars_def)
    ultimately have 0: "eqon (stR \<nu>) (stR \<omega>) (\<pi>\<^sub>R (vspace_sem (\<pi>\<^sub>I I) Z))" by (auto simp add: eqon_def)
  
    have "eqon (stT (sfilter \<nu> (CN\<^sub>T (TFunc f Z \<Theta>)))) (stT (sfilter \<omega> (CN\<^sub>T (TFunc f Z \<Theta>)))) (\<pi>\<^sub>T (FV\<^sub>T (TFunc f Z \<Theta>)))" 
      using TFunc Vagree_stT_E by force
    hence "eqon (stT (sfilter \<nu> (CN\<^sub>T  (TFunc f Z \<Theta>)))) (stT (sfilter \<omega> (CN\<^sub>T (TFunc f Z \<Theta>)))) (\<pi>\<^sub>T (UAV\<^sub>V Z))"
      by (simp add: eqon_def)
    hence "eqon (stT \<nu>) (stT \<omega>) (\<pi>\<^sub>T (UAV\<^sub>V Z))" by (simp add: eqon_def tsfilter_access Image_def CN\<^sub>V_def)
    hence 1: "eqon (stT \<nu>) (stT \<omega>) (\<pi>\<^sub>T (vspace_sem (\<pi>\<^sub>I I) Z))"
      using UAV\<^sub>V_overapprox apply (simp add: eqon_def) by blast

    show ?thesis using 0 1 Vagree_by_sortI by simp
  qed

  ultimately have "PInterp ?I ?Z \<nu> (args_sem_pre I \<Theta> arg_sem \<nu>) = PInterp ?I ?Z \<omega> (args_sem_pre I \<Theta> arg_sem \<omega>)"
    by (metis (full_types) PInterp_correct is_pinterp_alt)
  thus ?case by simp
next
  case Empty
  thus ?case by simp
next
  case (Concat te\<^sub>1 te\<^sub>2)
  have wf: "wf_ttrm te\<^sub>1 \<and> wf_ttrm te\<^sub>2" using Concat(3) by simp
  have "Vagree (sfilter \<nu> (CN\<^sub>T (Proj te\<^sub>1 C))) (sfilter \<omega> (CN\<^sub>T (Proj te\<^sub>1 C))) (FV\<^sub>T te\<^sub>1)"
    apply (cases "access_free (Concat te\<^sub>1 te\<^sub>2)")
    using Concat(4) apply (simp add: Int_Un_distrib2)
    using Vagree_subset apply blast
    using Concat(4) apply (simp add: Int_Un_distrib2) using Vagree_subset 
    by (smt (verit, ccfv_SIG) CN\<^sub>T.simps(5) Vagree_sfilter_cong_inter)
  moreover have "Vagree (sfilter \<nu> (CN\<^sub>T (Proj te\<^sub>2 C))) (sfilter \<omega> (CN\<^sub>T (Proj te\<^sub>2 C))) (FV\<^sub>T te\<^sub>2)"
      apply (cases "access_free (Concat te\<^sub>1 te\<^sub>2)")
    using Concat(4) apply (simp add: Int_Un_distrib2)
    using Vagree_subset apply blast
    using Concat(4) apply (simp add: Int_Un_distrib2) using Vagree_subset 
    by (smt (verit, ccfv_SIG) CN\<^sub>T.simps(5) Vagree_sfilter_cong_inter)
  
  ultimately show ?case using Concat.IH wf by simp
next
  case (Proj te Y)
  have wf: "wf_ttrm te" using Proj(2) by simp
  have "access_free te \<Longrightarrow> CN\<^sub>T (Proj te Y) \<inter> (\<V>\<^sub>T \<times> OCN\<^sub>C C) = CN\<^sub>T te \<inter> (\<V>\<^sub>T \<times> OCN\<^sub>C (Y \<inter>\<^sub>\<Omega> C))" by auto
  hence "Vagree (sfilter \<nu> (CN\<^sub>T (Proj te (Y \<inter>\<^sub>\<Omega> C)))) (sfilter \<omega> (CN\<^sub>T (Proj te (Y \<inter>\<^sub>\<Omega> C)))) (FV\<^sub>T te)"
    apply (cases "access_free te")
    using Proj by simp_all
  hence "ttrm_sem I (Proj te (Y \<inter>\<^sub>\<Omega> C)) \<nu> = ttrm_sem I (Proj te (Y \<inter>\<^sub>\<Omega> C)) \<omega>"
    using wf Proj.IH Proj(2) by blast
  thus ?case by simp
next
  case (ComItm ch \<theta> \<eta>)
  have "Vagree (sfilter \<nu> (CN\<^sub>R \<theta>)) (sfilter \<omega> (CN\<^sub>R \<theta>)) (FV\<^sub>R \<theta>)"
    using CN_QRPolynom_empty ComItm(4) ComItm.prems(1) by auto
  moreover have "Vagree (sfilter \<nu> (CN\<^sub>R \<eta>)) (sfilter \<omega> (CN\<^sub>R \<eta>)) (FV\<^sub>R \<eta>)"
    using CN_QRPolynom_empty ComItm(4) ComItm.prems(1) by auto
  moreover have "wf_rtrm \<theta>" and "wf_rtrm \<eta>" using ComItm.prems(1) QRpolynom_is_wf_rtrm by auto
  ultimately show ?case using ComItm(1,2) ttrm_sem.simps(5,7) by presburger
next
  case (Access te \<theta>)
  have "ttrm_sem I te \<nu> = ttrm_sem I te \<omega>"
  proof -
    have "Vagree (sfilter \<nu> (CN\<^sub>T te)) (sfilter \<omega> (CN\<^sub>T te)) (FV\<^sub>T te)"
      using Access by (metis CN\<^sub>T.simps(6,8) FV\<^sub>T.simps(8) Vagree_subset access_free.simps(8))      
    moreover have "wf_ttrm te" using Access(3) by simp
    ultimately have "ttrm_sem I (Proj te \<top>\<^sub>\<Omega>) \<nu> = ttrm_sem I (Proj te \<top>\<^sub>\<Omega>) \<omega>"
      using Access(1) CN\<^sub>T.simps(6) Vagree_sfilter_cong_inter by presburger
    thus ?thesis by simp
  qed
  moreover have "rtrm_sem I \<theta> \<nu> = rtrm_sem I \<theta> \<omega>"
  proof -
    have "Vagree (sfilter \<nu> (CN\<^sub>R \<theta>)) (sfilter \<omega> (CN\<^sub>R \<theta>)) (FV\<^sub>R \<theta>)"
      using Access by (metis CN\<^sub>T.simps(6,8) FV\<^sub>T.simps(8) Vagree_subset access_free.simps(8))      
    moreover have "wf_rtrm \<theta>" using Access(3) by simp
    ultimately show ?thesis using Access(2) by simp
  qed
  ultimately show ?case by simp
next
  case (RArg \<eta>) 
  thus ?case by auto
next
  case (TArg te)
  hence "Vagree (sfilter \<nu> (CN\<^sub>T (Proj te \<top>\<^sub>\<Omega>))) (sfilter \<omega> (CN\<^sub>T (Proj te \<top>\<^sub>\<Omega>))) (FV\<^sub>T te)" by simp
  moreover have "wf_ttrm te" using TArg by simp
  ultimately have "ttrm_sem I (Proj te \<top>\<^sub>\<Omega>) \<nu> = ttrm_sem I (Proj te \<top>\<^sub>\<Omega>) \<omega>" 
    using TArg.IH by blast
  thus ?case by simp
qed

corollary ttrm_coincidence: "wf_ttrm te
  \<Longrightarrow> Vagree (sfilter \<nu> (CN\<^sub>T te)) (sfilter \<omega> (CN\<^sub>T te)) (FV\<^sub>T te) 
  \<Longrightarrow> ttrm_sem I te \<nu> = ttrm_sem I te \<omega>"
  using arg_coincidence[of "TArg te" "\<nu>" "\<omega>" "I"] by simp

subsection \<open>Correctness of the Computable Bound Variables\<close>


lemma Evolution_nocom: "nocom_denotation (chp_sem I (Evolution x \<theta> \<phi>))"
  by fastforce



lemma BVP_overapprox:
  "BVP J \<alpha> \<subseteq> BV \<alpha>"
proof (induction \<alpha> rule: chp_induct)
  case (Chp a Z)
  thus ?case using BVP_Chp UAV\<^sub>V_overapprox by fastforce 
next
  case (Assign x \<theta>)
  have "\<exists>J. (if (\<forall>I \<omega>. \<pi>\<^sub>I I = J \<longrightarrow> rtrm_sem I \<theta> \<omega> = stR \<omega> x) then {} else {Rv x}) \<subseteq> {Rv x}" by simp
  thus ?case using BVP_assign BV.simps(3) by auto
next
  case (Nondet x)
  thus ?case unfolding BVP_def BV.simps(3) using BVP_elem BVP_nondet by blast
next
  case (Test \<phi>)
  thus ?case by (simp add: BVP_test)
next
  case (Evolution x \<theta> \<phi>)
  thus ?case using BVP_Evolution by simp
next
  case (Choice \<alpha> \<beta>)
  thus ?case using BV.simps(6) BVP_choice_bound by blast
next
  case (Compose \<alpha> \<beta>)
  thus ?case using BV.simps(7) BVP_compose_bound by blast
next
  case (Loop \<alpha>)
  thus ?case using BV.simps(8) BVP_loop_bound by blast
next
  case (Send ch h \<theta>)
  thus ?case using BV.simps(9) BVP_send by blast
next
  case (Receive ch h x)
  thus ?case using BV.simps(10) BVP_receive by blast
next
  case (Par \<alpha> \<beta>)
  thus ?case using BV.simps(11) BVP_par_bound by blast
qed

lemma CNP_overapprox:
  "CNP J \<alpha> \<subseteq> TCN\<^sub>P \<alpha>"
proof (induction \<alpha> rule: chp_induct)
  case (Chp a Z Y)   
  thus ?case using CNP_Chp UAV\<^sub>V_overapprox OCN\<^sub>C_overapprox by fastforce
next
  case (Assign x \<theta>)
  then show ?case by simp
next
  case (Nondet x)
  then show ?case by simp
next
  case (Test \<phi>)
  then show ?case by simp
next
  case (Evolution ode \<phi>)
  then show ?case by simp
next
  case (Choice \<alpha> \<beta>)
  then show ?case using TCN\<^sub>P.simps(6) CNP_choice_bound by blast
next
  case (Compose \<alpha> \<beta>)
  thus ?case using TCN\<^sub>P.simps(7) CNP_compose_bound by blast
next
  case (Loop \<alpha>)
  thus ?case using TCN\<^sub>P.simps(8) CNP_loop_bound by blast
next
  case (Send ch h \<theta>)
  thus ?case using TCN\<^sub>P.simps(9) CNP_send by blast
next
  case (Receive ch h x)
  thus ?case using TCN\<^sub>P.simps(10) CNP_receive by blast
next
  case (Par \<alpha> \<beta>)
  thus ?case using TCN\<^sub>P.simps(11) CNP_par_bound by blast
qed




   
subsection \<open>Auxiliary Properties for \<open>Par\<close> within \<open>BV\<close>\<close> 

text \<open>Semantics for parallel CHPs parameterized in the notion of bound variables used for merging 
the final states.\<close>
definition chp_alt_sem_par :: "stat_sem \<Rightarrow> interp \<Rightarrow> chp \<Rightarrow> chp \<Rightarrow> chp_domain set"
  where "chp_alt_sem_par \<L> I \<alpha> \<beta> = {(\<nu>, \<tau>, \<omega>) | \<nu> \<tau> \<omega>. \<exists>\<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta>. 
    (\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha>), \<omega>\<^sub>\<alpha>) \<in> chp_sem I \<alpha> \<and> (\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<beta>), \<omega>\<^sub>\<beta>) \<in> chp_sem I \<beta> \<and>
    (Vagreebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> \<V>\<^sub>\<mu>) \<and> (\<omega> = lmergebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> (BVP\<^sub>\<L> \<L> \<alpha>)) \<and> \<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha> \<union> CN (\<pi>\<^sub>I I) \<beta>) = \<tau>}"

lemma lmerge_BVP_cong_soundBV:
  assumes soundBV: "\<And>\<alpha>. BVP\<^sub>\<L> \<L> \<alpha> \<supseteq> BVP (\<pi>\<^sub>I I) \<alpha>"
      and disjoint: "BVP\<^sub>\<L> \<L> \<alpha> \<inter> BVP\<^sub>\<L> \<L> \<beta> \<subseteq> \<V>\<^sub>\<mu> \<union> (\<iota>\<^sub>T \<V>\<^sub>T)"
      and alpha: "(\<nu>, \<tau>\<^sub>\<alpha>, Fin \<omega>\<^sub>\<alpha>) \<in> chp_sem I \<alpha>"
      and beta:  "(\<nu>, \<tau>\<^sub>\<beta>, Fin \<omega>\<^sub>\<beta>) \<in> chp_sem I \<beta>"
      and gtime: "Vagree \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> \<V>\<^sub>\<mu>"
    shows "lmerge \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> (BVP (\<pi>\<^sub>I I) \<alpha>) = lmerge \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> (BVP\<^sub>\<L> \<L> \<alpha>)"
proof (rule state_eq_by_sortI, goal_cases stR stT)
  case stR
  thus ?case
  proof
    fix x
    show "stR (lmerge \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> (BVP (\<pi>\<^sub>I I) \<alpha>)) x = stR (lmerge \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> (BVP\<^sub>\<L> \<L> \<alpha>)) x"   
    proof (cases "Rv x \<in> BVP (\<pi>\<^sub>I I) \<alpha> \<or> Rv x \<notin> BVP\<^sub>\<L> \<L> \<alpha>")
      case True
      thus ?thesis using lmerge_def soundBV by fastforce
    next
      case False
      hence Rv: "Rv x \<notin> BVP (\<pi>\<^sub>I I) \<beta> \<or> Rv x \<in> \<V>\<^sub>\<mu>" using soundBV disjoint by fastforce
      have stR_alpha: "stR \<nu> x = stR \<omega>\<^sub>\<alpha> x" using False BVP_elem alpha by force
      show ?thesis
      proof  (cases "Rv x \<in> \<V>\<^sub>\<mu>")
        case True
        then show ?thesis using Vagree_def gtime lmerge_def by auto
      next
        case False
        hence stR: "stR \<nu> x = stR \<omega>\<^sub>\<beta> x" using Rv BVP_elem beta by force
        then show ?thesis using stR_alpha lmerge_def by simp
      qed
    qed
  qed
next
  case stT  
  have "Vagree \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> (\<iota>\<^sub>T \<V>\<^sub>T)" 
    by (meson Vagree_sym Vagree_only_trans alpha beta bound_effect_on_state(2))
  hence "stT \<omega>\<^sub>\<alpha> = stT \<omega>\<^sub>\<beta>" using Vagree_alltvars by blast
  thus ?case unfolding lmerge_def by auto
qed      

lemma chp_sem_eq_alt_sem:
  assumes soundBV: "\<And>\<alpha>. BVP\<^sub>\<L> \<L> \<alpha> \<supseteq> BVP (\<pi>\<^sub>I I) \<alpha>"
      and "BVP\<^sub>\<L> \<L> \<alpha> \<inter> BVP\<^sub>\<L> \<L> \<beta> \<subseteq> \<V>\<^sub>\<mu> \<union> (\<iota>\<^sub>T \<V>\<^sub>T)"
    shows "chp_sem I (Par \<alpha> \<beta>) = chp_alt_sem_par \<L> I \<alpha> \<beta>"
proof (rule eq3I)
  fix \<nu> \<tau> \<omega>
  show "((\<nu>, \<tau>, \<omega>) \<in> chp_sem I (\<alpha> par \<beta>)) = ((\<nu>, \<tau>, \<omega>) \<in> chp_alt_sem_par \<L> I \<alpha> \<beta>)"
  proof (cases \<omega>)
    case (Fin \<omega>')
    show ?thesis
    proof (rule, goal_cases forward backward)
      case forward
      assume "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I (\<alpha> par \<beta>)"
      then obtain \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta>
        where alpha: "(\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha>), \<omega>\<^sub>\<alpha>) \<in> chp_sem I \<alpha>"
          and beta:  "(\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<beta>), \<omega>\<^sub>\<beta>) \<in> chp_sem I \<beta>"
          and gtimebot: "Vagreebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> \<V>\<^sub>\<mu>"
          and mergebot: "\<omega> = lmergebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> (BVP (\<pi>\<^sub>I I) \<alpha>)"
          and nojunk: "\<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha> \<union> CN (\<pi>\<^sub>I I) \<beta>) = \<tau>"
        by auto 
      then obtain \<omega>\<^sub>\<alpha>' \<omega>\<^sub>\<beta>' where alphafin: "\<omega>\<^sub>\<alpha> = Fin \<omega>\<^sub>\<alpha>'" and betafin: "\<omega>\<^sub>\<beta> = Fin \<omega>\<^sub>\<beta>'" 
        using Fin mergebot lmergebot_Exists_Fin by metis
      hence merge: "\<omega>' = lmerge \<omega>\<^sub>\<alpha>' \<omega>\<^sub>\<beta>' (BVP (\<pi>\<^sub>I I) \<alpha>)" using Fin mergebot by simp
      hence gtime: "Vagree \<omega>\<^sub>\<alpha>' \<omega>\<^sub>\<beta>' \<V>\<^sub>\<mu>" using gtimebot Vagreebot_only_Fin alphafin betafin by blast
      hence "\<omega>' = lmerge \<omega>\<^sub>\<alpha>' \<omega>\<^sub>\<beta>' (BVP\<^sub>\<L> \<L> \<alpha>)"
        using alpha alphafin assms beta betafin lmerge_BVP_cong_soundBV merge by blast     
      thus "(\<nu>, \<tau>, \<omega>) \<in> chp_alt_sem_par \<L> I \<alpha> \<beta>" 
        unfolding chp_alt_sem_par_def 
        using Fin alpha alphafin beta betafin nojunk gtimebot mergebot lmergebot_fin by blast
    next
      case backward
      assume "(\<nu>, \<tau>, \<omega>) \<in> chp_alt_sem_par \<L> I \<alpha> \<beta>"
      then obtain \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta>
        where alpha: "(\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha>), \<omega>\<^sub>\<alpha>) \<in> chp_sem I \<alpha>"
          and beta:  "(\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<beta>), \<omega>\<^sub>\<beta>) \<in> chp_sem I \<beta>"
          and gtimebot: "Vagreebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> \<V>\<^sub>\<mu>"
          and mergebot: "\<omega> = lmergebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> (BVP\<^sub>\<L> \<L> \<alpha>)"
          and nojunk: "\<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha> \<union> CN (\<pi>\<^sub>I I) \<beta>) = \<tau>"
        using chp_alt_sem_par_def by auto
      then obtain \<omega>\<^sub>\<alpha>' \<omega>\<^sub>\<beta>' where alphafin: "\<omega>\<^sub>\<alpha> = Fin \<omega>\<^sub>\<alpha>'" and betafin: "\<omega>\<^sub>\<beta> = Fin \<omega>\<^sub>\<beta>'" 
        using Fin mergebot lmergebot_Exists_Fin by metis
      hence merge: "\<omega>' = lmerge \<omega>\<^sub>\<alpha>' \<omega>\<^sub>\<beta>' (BVP\<^sub>\<L> \<L> \<alpha>)" using Fin mergebot by simp
      have gtime: "Vagree \<omega>\<^sub>\<alpha>' \<omega>\<^sub>\<beta>' \<V>\<^sub>\<mu>" using gtimebot Vagreebot_only_Fin alphafin betafin by blast  
      hence "\<omega>' = lmerge \<omega>\<^sub>\<alpha>' \<omega>\<^sub>\<beta>' (BVP (\<pi>\<^sub>I I) \<alpha>)" 
        using alpha alphafin assms beta betafin lmerge_BVP_cong_soundBV merge by metis
      thus ?case using Fin alpha alphafin beta betafin nojunk gtimebot lmergebot_fin by blast
    qed   
  next
    case NonFin
    thus ?thesis unfolding chp_alt_sem_par_def by simp
  qed
qed

              





subsection \<open>Coincidence Properties for Formulas and CHPs\<close>

paragraph \<open>Auxiliaries from \<open>state\<close> to \<open>state-updating\<close> within \<open>sfilter\<close> for \<open>Exists\<close>\<close>









paragraph \<open>Auxiliaries for \<open>Box\<close> and \<open>AcBox\<close>\<close>

lemma Vagree_tvars_cong_runs: (* in use *)
  "Vagree (sfilter \<nu> C) (sfilter \<nu>' C) (X \<inter> \<iota>\<^sub>T \<V>\<^sub>T) 
  \<Longrightarrow> (\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha> 
  \<Longrightarrow> (\<nu>', \<tau>, Fin \<omega>') \<in> chp_sem I \<alpha>
  \<Longrightarrow> Vagree (sfilter \<omega> C) (sfilter \<omega>' C) (X \<inter> \<iota>\<^sub>T \<V>\<^sub>T)" 
  apply (rule Vagree_by_sortI)
   apply (simp add: pi_rvars_def)
using Vagree_T_onlyE proof (goal_cases stT)
  case stT
  hence "Vagree \<nu> \<omega> (\<iota>\<^sub>T \<V>\<^sub>T)" using bound_effect_on_state(2) by auto 
  thus ?case by (metis Vagree_alltvars Vagree_stT_E bound_effect_on_state(2) stT(1,3) stT_sfilter)
qed


paragraph \<open>Auxiliaries for \<open>GPsymb\<close>\<close>

lemma GPsymb_arg_CN_subset: (* in use *)
  "\<forall>\<theta>\<in>set \<Theta>. (CN\<^sub>A \<theta>) \<subseteq> (CN\<^sub>F (GPsymb b p Z \<Theta>))" by auto

lemma GPsymb_arg_FV_subset: (* in use *)
  "\<forall>\<theta>\<in>set \<Theta>. (FV\<^sub>A \<theta>) \<subseteq> (FV\<^sub>F (GPsymb b p Z \<Theta>))" by auto

lemma GPsymb_Vagree_args: (* in use *)
  assumes "Vagree (sfilter \<nu> (CN\<^sub>F (GPsymb b p Z \<Theta>))) (sfilter \<nu>' (CN\<^sub>F (GPsymb b p Z \<Theta>))) (FV\<^sub>F (GPsymb b p Z \<Theta>))"
    shows "\<And>\<theta>. \<theta>\<in>set \<Theta> \<Longrightarrow> Vagree (sfilter \<nu> (CN\<^sub>A \<theta>)) (sfilter \<nu>' (CN\<^sub>A \<theta>)) (FV\<^sub>A \<theta>)"
  by (metis Vagree_or Vagree_sfilter_cong_inter GPsymb_arg_CN_subset GPsymb_arg_FV_subset assms inf.absorb2)







paragraph \<open>Coincidence Properties for Formulas and CHPs\<close>

section \<open>Uniform Substitution\<close>

paragraph \<open>Minimal Static Semantics\<close>

fun FVE\<^sub>C :: "expr \<Rightarrow> variable set"
  where
  "FVE\<^sub>C (Ertrm \<theta>) = FV\<^sub>R \<theta>"
| "FVE\<^sub>C (Ettrm te) = FV\<^sub>T te"
| "FVE\<^sub>C (Earg e) = FV\<^sub>A e"
| "FVE\<^sub>C (Efml \<phi>) = FV\<^sub>F \<phi>"

fun CNE\<^sub>C :: "expr \<Rightarrow> comtar set"
  where
  "CNE\<^sub>C (Ertrm \<theta>) = CN\<^sub>R \<theta>"
| "CNE\<^sub>C (Ettrm te) = CN\<^sub>T te"
| "CNE\<^sub>C (Earg e) = CN\<^sub>A e"
| "CNE\<^sub>C (Efml \<phi>) = CN\<^sub>F \<phi>"

definition BN :: "chp \<Rightarrow> bindr set"
  where "BN \<alpha> = \<iota>\<^sub>V (BV \<alpha>) \<union> \<iota>\<^sub>C (TCN\<^sub>P \<alpha>)"

definition FNE\<^sub>C :: "expr \<Rightarrow> bindr set"
  where "FNE\<^sub>C e = \<iota>\<^sub>V (FVE\<^sub>C e) \<union> \<iota>\<^sub>C (CNE\<^sub>C e)"
  
definition computable_stat_sem :: "stat_sem" ("\<L>\<^sub>C")
  where "computable_stat_sem = \<lparr> FNE\<^sub>\<L> = FNE\<^sub>C, BNP\<^sub>\<L> = BN, FVP\<^sub>\<L> = FV\<^sub>P, 
    CNC\<^sub>\<L> = OCN\<^sub>C, UACN\<^sub>\<L> = UCN\<^sub>C, FVV\<^sub>\<L> = UAV\<^sub>V, UAV\<^sub>\<L> = LAV\<^sub>V \<rparr>"


lemma BVP_comptuable_stat_sem [simp]: "BVP\<^sub>\<L> \<L>\<^sub>C \<alpha> = BV \<alpha>"
  unfolding computable_stat_sem_def BVP\<^sub>\<L>_def BN_def by simp

lemma shows computable_coincidence_fml: "wf_fml \<L>\<^sub>C \<phi>
  \<Longrightarrow> Vagree (sfilter \<nu> (CN\<^sub>F \<phi>)) (sfilter \<nu>' (CN\<^sub>F \<phi>)) (FV\<^sub>F \<phi>) 
  \<Longrightarrow> (\<nu> \<in> (fml_sem I \<phi>) \<Longrightarrow> \<nu>' \<in> (fml_sem I \<phi>))" 
  and computable_coincidence_chp: "wf_chp \<L>\<^sub>C \<alpha> 
  \<Longrightarrow> X \<supseteq> (FV\<^sub>P \<alpha>) \<Longrightarrow> Vagree \<nu> \<nu>' X \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> 
  \<Longrightarrow> \<exists>\<omega>'. (\<nu>', \<tau>, \<omega>') \<in> chp_sem I \<alpha> \<and> Vagreebot \<omega> \<omega>' (X \<union> MBV \<alpha>)" 
proof (induction \<phi> and \<alpha> arbitrary: \<nu> \<nu>' and \<nu> \<nu>' X \<tau> \<omega>)
  case (GPsymb b p Z \<Theta>)
  let ?I = "AllPsymbs I b p"
  let ?Z = "vspace_sem (\<pi>\<^sub>I I) Z"

  have "(args_sem_pre I \<Theta> arg_sem \<nu>) = (args_sem_pre I \<Theta> arg_sem \<nu>')"
  proof -
    have "\<forall>\<theta> \<in> set \<Theta>. wf_arg \<theta>" using GPsymb.prems(1) by (simp add: Ball_set_list_all)    
    moreover have "\<And>\<theta>. \<theta> \<in> set \<Theta> \<Longrightarrow> Vagree (sfilter \<nu> (CN\<^sub>A \<theta>)) (sfilter \<nu>' (CN\<^sub>A \<theta>)) (FV\<^sub>A \<theta>)"   
      using GPsymb.prems(2) GPsymb_Vagree_args by blast
    ultimately have "\<forall>\<theta> \<in> set \<Theta>. arg_sem I \<theta> \<nu> = arg_sem I \<theta> \<nu>'" using arg_coincidence by blast
    thus ?thesis using args_sem_pre_def by simp
  qed

  moreover have "Vagree \<nu> \<nu>' ?Z"
  proof -
    have "eqon (stR \<nu>) (stR \<nu>') (\<pi>\<^sub>R (FV\<^sub>F (GPsymb b p Z \<Theta>)))" using GPsymb Vagree_stR_E stR_sfilter by metis
    moreover have "\<pi>\<^sub>R (vspace_sem (\<pi>\<^sub>I I) Z) \<subseteq> \<pi>\<^sub>R (FV\<^sub>F (GPsymb b p Z \<Theta>))" 
      using UAV\<^sub>V_overapprox by (auto simp add: pi_rvars_def)
    ultimately have 0: "eqon (stR \<nu>) (stR \<nu>') (\<pi>\<^sub>R (vspace_sem (\<pi>\<^sub>I I) Z))" by (auto simp add: eqon_def)
  
    have "eqon (stT (sfilter \<nu> (CN\<^sub>F (GPsymb b p Z \<Theta>)))) (stT (sfilter \<nu>' (CN\<^sub>F (GPsymb b p Z \<Theta>)))) (\<pi>\<^sub>T (FV\<^sub>F (GPsymb b p Z \<Theta>)))" 
      using GPsymb Vagree_stT_E by force
    hence "eqon (stT (sfilter \<nu> (CN\<^sub>F (GPsymb b p Z \<Theta>)))) (stT (sfilter \<nu>' (CN\<^sub>F (GPsymb b p Z \<Theta>)))) (\<pi>\<^sub>T (UAV\<^sub>V Z))"
      by (simp add: eqon_def)
    hence "eqon (stT \<nu>) (stT \<nu>') (\<pi>\<^sub>T (UAV\<^sub>V Z))" by (simp add: eqon_def tsfilter_access Image_def CN\<^sub>V_def)
    hence 1: "eqon (stT \<nu>) (stT \<nu>') (\<pi>\<^sub>T (vspace_sem (\<pi>\<^sub>I I) Z))"
      using UAV\<^sub>V_overapprox apply (simp add: eqon_def) by blast

    show ?thesis using 0 1 Vagree_by_sortI by simp
  qed

  ultimately have "PInterp ?I ?Z \<nu> (args_sem_pre I \<Theta> arg_sem \<nu>) = PInterp ?I ?Z \<nu>' (args_sem_pre I \<Theta> arg_sem \<nu>')"
    by (metis (full_types) PInterp_correct is_pinterp_alt)
  thus ?case using GPsymb by simp
next
  case (Geq \<theta>\<^sub>1 \<theta>\<^sub>2)
  hence "\<And>\<theta>. \<theta> \<in> {\<theta>\<^sub>1,\<theta>\<^sub>2} \<Longrightarrow> Vagree (sfilter \<nu> (CN\<^sub>R \<theta>)) (sfilter \<nu>' (CN\<^sub>R \<theta>))(FV\<^sub>R \<theta>)" 
    by (metis CN\<^sub>F.simps(2) FV\<^sub>F.simps(2) Vagree_subset insertE singletonD)
  hence "(rtrm_sem I \<theta>\<^sub>1 \<nu> = rtrm_sem I \<theta>\<^sub>1 \<nu>') \<and> (rtrm_sem I \<theta>\<^sub>2 \<nu> = rtrm_sem I \<theta>\<^sub>2 \<nu>')" 
    by (meson Geq.prems(1) insert_iff rtrm_coincidence wf_fml.simps(2))
  thus ?case using Geq.prems(3) by force
next
  case (Pref te\<^sub>1 te\<^sub>2)
  hence "\<And>te. te \<in> {te\<^sub>1,te\<^sub>2} \<Longrightarrow> Vagree (sfilter \<nu> (CN\<^sub>T te)) (sfilter \<nu>' (CN\<^sub>T te))(FV\<^sub>T te)" 
    by (metis CN\<^sub>F.simps(3) FV\<^sub>F.simps(3) Pref.prems(2) Vagree_subset insert_iff singletonD)
  hence "(ttrm_sem I te\<^sub>1 \<nu> = ttrm_sem I te\<^sub>1 \<nu>') \<and> (ttrm_sem I te\<^sub>2 \<nu> = ttrm_sem I te\<^sub>2 \<nu>')" 
    by (meson Pref.prems(1) insertCI ttrm_coincidence wf_fml.simps(3)) 
  thus ?case using Pref.prems(3) by force
next
  case (Not \<phi>)
  thus ?case using Vagree_sym by auto
next
  case (And \<phi> \<psi>)
  hence "\<forall>\<xi> \<in> {\<phi>,\<psi>}. Vagree (sfilter \<nu> (CN\<^sub>F \<xi>)) (sfilter \<nu>' (CN\<^sub>F \<xi>)) (FV\<^sub>F \<xi>)" 
    by (metis CN\<^sub>F.simps(5) FV\<^sub>F.simps(5) Vagree_subset insertE singletonD)
  hence "\<forall>\<xi> \<in> {\<phi>,\<psi>}. \<not>(\<nu> \<in> fml_sem I \<xi>) \<or> (\<nu>' \<in> fml_sem I \<xi>)" 
    by (metis And.IH And.prems(1) insert_iff singletonD wf_fml.simps(5))
  thus ?case using And.prems(3) by auto
next
  case (Exists z \<phi>)
  assume "\<nu> \<in> fml_sem I (Exists z \<phi>)"
  then obtain d where sorteq: "sorteq z d" and upds: "upds \<nu> z d \<in> fml_sem I \<phi>" 
    by (auto simp add: fml_sem.simps(6)) 
  have "Vagree (sfilter \<nu> (CN\<^sub>F \<phi>)) (sfilter \<nu>' (CN\<^sub>F \<phi>)) ((FV\<^sub>F \<phi>) - {z})"
    using Exists.prems(2) unfolding Vagree_def by simp
  hence "Vagree (sfilter (upds \<nu> z d) (CN\<^sub>F \<phi>)) (sfilter (upds \<nu>' z d) (CN\<^sub>F \<phi>)) (FV\<^sub>F \<phi>)"  
    using Exists.prems(2) sorteq sfilter_state_to_upds unfolding Vagree_def by presburger
  moreover have "wf_fml \<L>\<^sub>C \<phi>" using Exists.prems(1) by force
  ultimately have ?case "upds \<nu>' z d \<in> fml_sem I (Exists z \<phi>)"
    using sorteq upds Exists.IH by (auto simp add: fml_sem.simps(6))
  thus ?case by simp
next
  case (Box \<alpha> \<psi>)
  show ?case
  proof (rule box_by_runsI)
    fix \<tau> \<omega>' (* since \<tau> = \<tau>' *)
    let ?X = "FV\<^sub>F ([[ \<alpha> ]] \<psi>)"
    let ?Y = "CN\<^sub>F ([[ \<alpha> ]] \<psi>)"

    assume a0: "(\<nu>', \<tau>, Fin \<omega>') \<in> chp_sem I \<alpha>"

    (* run starting from \<nu> exists *)                                       
    have "eqon (stR \<nu>) (stR \<nu>') (\<pi>\<^sub>R ?X)" using Box by (metis Vagree_stR_E stR_sfilter)
    hence "Vagree \<nu>' \<nu> (?X \<inter> \<iota>\<^sub>R \<V>\<^sub>R)" 
      unfolding Vagree_def by (metis Box.prems(2) Int_iff Vagree_def Vagree_sfilter_onR) 
    moreover have "FV\<^sub>P \<alpha> \<subseteq> (?X \<inter> \<iota>\<^sub>R \<V>\<^sub>R)" using Box.prems(1) FV\<^sub>P_wf_chp_only_rvars by force
    ultimately have "\<exists>\<omega>. (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<and> Vagreebot (Fin \<omega>') \<omega> ((?X \<inter> \<iota>\<^sub>R \<V>\<^sub>R) \<union> MBV \<alpha>)" 
      using Box a0 by auto
    then obtain \<omega> where run: "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha>" 
      and "Vagreebot (Fin \<omega>') (Fin \<omega>) (?X \<inter> \<iota>\<^sub>R \<V>\<^sub>R)"
      and agreeBV: "Vagreebot (Fin \<omega>') (Fin \<omega>) (MBV \<alpha>)" 
      using Vagree_and Vagreebot_only_Fin Vagreebot_snd_NonFin by blast

    (* final states \<omega>' @@ \<tau> and \<omega> @@ \<tau> coincide *)
    hence "Vagree \<omega>' \<omega> (?X \<inter> \<iota>\<^sub>R \<V>\<^sub>R)" using Vagreebot_only_Fin by simp
    moreover have "Vagree (sfilter \<omega>' ?Y) (sfilter \<omega> ?Y) (?X \<inter> \<iota>\<^sub>T \<V>\<^sub>T)" 
      by (meson Box.prems(2) Vagree_antimon Vagree_sym_rel Vagree_tvars_cong_runs a0 inf.cobounded1 run)
    ultimately have "Vagree (sfilter \<omega> ?Y) (sfilter \<omega>' ?Y) ?X"      
      by (metis Vagree_sfilter_cong Vagree_sym_rel Vagree_union boolean_algebra.conj_disj_distrib boolean_algebra.conj_one_right compose_allvars)    
    hence "Vagree (sfilter \<omega> ?Y) (sfilter \<omega>' ?Y) (FV\<^sub>P \<alpha> \<union> (FV\<^sub>F \<psi> - MBV \<alpha>) \<union> MBV \<alpha>)"
      using agreeBV FV\<^sub>F.simps(7) Vagree_sfilter_cong Vagree_union Vagreebot_only_Fin Vagree_sym_rel by metis 
    hence "Vagree (sfilter (\<omega> @@ \<tau>) (CN\<^sub>F \<psi>)) (sfilter (\<omega>' @@ \<tau>) (CN\<^sub>F \<psi>)) (FV\<^sub>F \<psi>)" 
      by (metis Un_Diff_cancel2 Vagree_and Vagree_sttconc_cong sfilter_dist_sttconc CN\<^sub>F.simps(7))
    moreover have "\<omega> @@ \<tau> \<in> fml_sem I \<psi>" using Box.prems(3) run by fastforce
    ultimately show "\<omega>' @@ \<tau> \<in> fml_sem I \<psi>" using Box.IH(2) Box.prems(1) wf_fml.simps(7) by blast
  qed
next
  case (AcBox \<alpha> A C \<psi>)
  thus ?case
  proof -
    let ?X = "FV\<^sub>P \<alpha> \<union> FV\<^sub>F A \<union> FV\<^sub>F C \<union> (FV\<^sub>F \<psi> - MBV \<alpha>)"
    let ?Y = "CN\<^sub>F A \<union> CN\<^sub>F C \<union> CN\<^sub>F \<psi>" 

    (* Vagree \<nu>' \<nu> (?X \<inter> \<iota>\<^sub>R \<V>\<^sub>R) *)
    have "eqon (stR \<nu>) (stR \<nu>') (\<pi>\<^sub>R ?X)" by (metis AcBox.prems(2) FV\<^sub>F.simps(8) Vagree_stR_E stR_sfilter)
    hence agreeInitRvar: "Vagree \<nu>' \<nu> (?X \<inter> \<iota>\<^sub>R \<V>\<^sub>R)" 
      unfolding Vagree_def by (metis AcBox.prems(2) FV\<^sub>F.simps(8) Int_iff Vagree_def Vagree_sfilter_onR) 

    have agree: "Vagree (sfilter \<nu> ?Y) (sfilter \<nu>' ?Y) ?X" using AcBox.prems(2) by auto
    hence agreeA: "Vagree (sfilter \<nu>' (CN\<^sub>F A)) (sfilter \<nu> (CN\<^sub>F A)) (FV\<^sub>F A)"
      using Vagree_subset CN\<^sub>F.simps(9) FV\<^sub>F.simps(9) by (meson Vagree_sym Vagree_and)
    have wf_alpha: "wf_chp \<L>\<^sub>C \<alpha>" and wf_A: "wf_fml \<L>\<^sub>C A" using AcBox.prems(1) by auto
    hence alpha_Rvar: "FV\<^sub>P \<alpha> \<subseteq> (?X \<inter> \<iota>\<^sub>R \<V>\<^sub>R)" using FV\<^sub>P_wf_chp_only_rvars by force

    show "\<nu>' \<in> fml_sem I (AcBox \<alpha> A C \<psi>)"
    proof (rule ac_box_by_ac_casesI, goal_cases commit post)
      case (commit \<tau> \<omega>')
      then obtain \<omega> where run: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha>"
        and agreeRvar: "Vagreebot \<omega>' \<omega> ((?X \<inter> \<iota>\<^sub>R \<V>\<^sub>R) \<union> MBV \<alpha>)" 
        using AcBox.IH(1) agreeInitRvar wf_alpha alpha_Rvar by blast   

      have "strict_assm_set \<nu> \<tau> \<subseteq> fml_sem I A" unfolding g_assm_set_def
      proof (rule subsetI)                     
        fix \<kappa> 
        assume "\<kappa> \<in> {\<nu> @@ \<tau>'' |\<tau>''. \<tau>'' \<prec> \<tau>}"
        then obtain \<tau>'' where s: "\<kappa> = \<nu> @@ \<tau>''" and strict_pref: "\<tau>'' \<prec> \<tau>" by auto                                                 
        hence "\<nu>' @@ \<tau>'' \<in> strict_assm_set \<nu>' \<tau>" using g_assm_set_def strict_prefix_def by auto
        hence "\<nu>' @@ \<tau>'' \<in> fml_sem I A" using commit(2) by auto
        moreover have "Vagree (sfilter (\<nu>' @@ \<tau>'') (CN\<^sub>F A)) (sfilter (\<nu> @@ \<tau>'') (CN\<^sub>F A)) (FV\<^sub>F A)"
          using Vagree_sttconc_cong agreeA sfilter_dist_sttconc by presburger     
        ultimately have "\<nu> @@ \<tau>'' \<in> fml_sem I A" using AcBox.IH(2) Vagree_sym_rel wf_A by blast
        thus "\<kappa> \<in> fml_sem I A" using s by auto
      qed
      
      hence "\<nu> @@ \<tau> \<in> fml_sem I C" using AcBox.prems(3) ac_box_commit run by blast
      moreover have "Vagree (sfilter (\<nu> @@ \<tau>) (CN\<^sub>F C)) (sfilter (\<nu>' @@ \<tau>) (CN\<^sub>F C)) (FV\<^sub>F C)"         
        using agree FV\<^sub>F.simps(9) CN\<^sub>F.simps(9) Vagree_subset Vagree_sfilter_cong Vagree_sttconc_cong by (metis sfilter_dist_sttconc)
      ultimately show "\<nu>' @@ \<tau> \<in> fml_sem I C" using AcBox.IH(3) AcBox.prems(1) by simp
    next
      case (post \<tau> \<omega>')
      hence "\<exists>\<omega>. (\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha> \<and> Vagreebot (Fin \<omega>') (Fin \<omega>) ((?X \<inter> \<iota>\<^sub>R \<V>\<^sub>R) \<union> MBV \<alpha>)" 
        using AcBox.IH(1) agreeInitRvar wf_alpha alpha_Rvar by (metis Vagreebot_snd_NonFin)
      then obtain \<omega> where run: "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha>"
        and agreeRvarFV: "Vagree \<omega>' \<omega> (?X \<inter> \<iota>\<^sub>R \<V>\<^sub>R)"
        and agreeRvarMBV: "Vagree \<omega>' \<omega> (MBV \<alpha>)"
        using Vagree_and Vagreebot_only_Fin by blast

      have "assm_set \<nu> \<tau> \<subseteq> fml_sem I A" unfolding g_assm_set_def  
      proof (rule subsetI)                  
        fix \<kappa>  
        assume "\<kappa> \<in> {\<nu> @@ \<tau>'' |\<tau>''. \<tau>'' \<preceq> \<tau>}"
        then obtain \<tau>'' where s: "\<kappa> = \<nu> @@ \<tau>''" 
          and pref: "\<tau>'' \<preceq> \<tau>" by blast           
        have "Vagree (sfilter (\<nu>' @@ \<tau>'') (CN\<^sub>F A)) (sfilter (\<nu> @@ \<tau>'') (CN\<^sub>F A)) (FV\<^sub>F A)"
          using Vagree_sttconc_cong agreeA sfilter_dist_sttconc by presburger
        moreover have "\<nu>' @@ \<tau>'' \<in> fml_sem I A"
          using post(2) assm_set_contains_boundary assm_set_prefix pref prefixE subsetD by (metis)                  
        ultimately have "\<nu> @@ \<tau>'' \<in> fml_sem I A" using AcBox.IH(2) AcBox.prems(1) by simp                      
        thus "\<kappa> \<in> fml_sem I A" using s by auto
      qed   
      
      hence "\<omega> @@ \<tau> \<in> fml_sem I \<psi>" using AcBox.prems(3) ac_box_post run by blast
      moreover have "Vagree (sfilter (\<omega> @@ \<tau>) (CN\<^sub>F \<psi>)) (sfilter (\<omega>' @@ \<tau>) (CN\<^sub>F \<psi>)) (FV\<^sub>F \<psi>)"  
      proof -
        have "Vagree (sfilter \<nu> (CN\<^sub>F \<psi>)) (sfilter \<nu>' (CN\<^sub>F \<psi>)) (?X \<inter> \<iota>\<^sub>T \<V>\<^sub>T)" 
          by (metis Un_absorb Vagree_or Vagree_subset agree)
        hence "Vagree (sfilter \<omega> (CN\<^sub>F \<psi>)) (sfilter \<omega>' (CN\<^sub>F \<psi>)) (?X \<inter> \<iota>\<^sub>T \<V>\<^sub>T)"
          using post(1) run Vagree_tvars_cong_runs by metis
        hence agreeTv: "Vagree (sfilter (\<omega> @@ \<tau>) (CN\<^sub>F \<psi>)) (sfilter (\<omega>' @@ \<tau>) (CN\<^sub>F \<psi>)) (?X \<inter> \<iota>\<^sub>T \<V>\<^sub>T)" 
          using Vagree_sttconc_cong sfilter_dist_sttconc by presburger
        moreover have "Vagree (sfilter (\<omega> @@ \<tau>) (CN\<^sub>F \<psi>)) (sfilter (\<omega>' @@ \<tau>) (CN\<^sub>F \<psi>)) (?X \<inter> \<iota>\<^sub>R \<V>\<^sub>R)"
          using agreeTv Vagree_sttconc_cong Vagree_sfilter_cong Vagree_sym Vagree_union agreeRvarFV by presburger
        moreover have "(?X \<inter> \<iota>\<^sub>R \<V>\<^sub>R) \<union> (?X \<inter> \<iota>\<^sub>T \<V>\<^sub>T) = ?X"
          using Int_Un_distrib compose_allvars by (metis Int_absorb2 subset_UNIV) 
        ultimately have "Vagree (sfilter (\<omega> @@ \<tau>) (CN\<^sub>F \<psi>)) (sfilter (\<omega>' @@ \<tau>) (CN\<^sub>F \<psi>)) ?X"
          by (metis Vagree_and)
        moreover have "FV\<^sub>F \<psi> \<subseteq> (?X \<union> (MBV \<alpha>))" by auto
        ultimately show "Vagree (sfilter (\<omega> @@ \<tau>) (CN\<^sub>F \<psi>)) (sfilter (\<omega>' @@ \<tau>) (CN\<^sub>F \<psi>)) (FV\<^sub>F \<psi> )"
          by (meson Vagree_antimon Vagree_sym Vagree_sfilter_cong Vagree_sttconc_cong Vagree_union agreeRvarMBV)
      qed
      ultimately show "\<omega>' @@ \<tau> \<in> fml_sem I \<psi>" using AcBox.IH(4) AcBox.prems(1) by simp
    qed 
  qed
next
  case (ChanIn ch Y)
  hence "rtrm_sem I ch \<nu> = rtrm_sem I ch \<nu>'" using rtrm_coincidence by simp
  thus ?case using ChanIn.prems(3) by simp

(* +++++++++++++++ CHPs below +++++++++++++++++++ *)

next
  case (Chp a Z Y)
  hence vagree: "X \<supseteq> FVP (\<pi>\<^sub>I I) (Chp a Z Y)"
    using FVP_Chp FV\<^sub>P.simps(1) UAV\<^sub>V_overapprox by blast
  then obtain \<omega>\<^sub>0' where "(\<nu>', \<tau>, \<omega>\<^sub>0') \<in> chp_sem I (Chp a Z Y) \<and> Vagreebot \<omega> \<omega>\<^sub>0' X"
    using vagree Chp.prems(3,4) coincidence_chp by blast
  thus ?case by auto
next
  case (Assign x \<theta>)
  hence noCom: "\<tau> = []" by auto
  thus ?case
  proof (cases \<omega>)
    case (Fin \<omega>\<^sub>0)
    hence finState: "\<omega>\<^sub>0 = rrepv \<nu> x (rtrm_sem I \<theta> \<nu>)" using Assign.prems(4) by auto
    
    let ?\<omega>\<^sub>0' = "rrepv \<nu>' x (rtrm_sem I \<theta> \<nu>')"
    
    have "Vagree \<nu> \<nu>' (FV\<^sub>R \<theta>)" by (metis Assign.prems(2) Assign.prems(3) FV\<^sub>P.simps(2) Vagree_antimon)
    hence RHSeqSem: "(rtrm_sem I \<theta> \<nu>') = (rtrm_sem I \<theta> \<nu>)" 
      using Assign.prems(1) wf_chp.simps(2) QRpolynom_is_wf_rtrm
      by (metis Vagree_sfilter_cong rtrm_coincidence)
    hence "Vagreebot (Fin \<omega>\<^sub>0) (Fin ?\<omega>\<^sub>0') (MBV (x := \<theta>))" 
      by (simp add: Vagreebot_def Vagree_def finState)
    moreover have "Vagree \<omega>\<^sub>0 ?\<omega>\<^sub>0' X" using Assign.prems(3) Vagree_def finState RHSeqSem by simp
    moreover have "(\<nu>', \<tau>, Fin ?\<omega>\<^sub>0') \<in> chp_sem I (x := \<theta>)" using noCom by simp
    ultimately show ?thesis using Fin Vagree_and Vagreebot_only_Fin by blast
  next
    case NonFin
    thus ?thesis using noCom by auto
  qed
next
  case (Nondet x)
  hence noCom: "\<tau> = []" by auto
  thus ?case
  proof (cases \<omega>)
    case (Fin \<omega>\<^sub>0)
    then obtain r where finState: "\<omega>\<^sub>0 = rrepv \<nu> x r" using Nondet.prems(4) by auto
    have "Vagreebot (Fin \<omega>\<^sub>0) (Fin (rrepv \<nu>' x r)) (MBV (x := *))" 
      by (simp add: Vagreebot_def Vagree_def finState)
    moreover have "Vagree \<omega>\<^sub>0 (rrepv \<nu>' x r) X" 
      using Nondet.prems(3) by (simp add: Vagree_def finState)
    moreover have "(\<nu>', \<tau>, Fin (rrepv \<nu>' x r)) \<in> chp_sem I (x := *)" using noCom by auto
    ultimately show ?thesis using Fin Vagree_and Vagreebot_only_Fin by blast
  next
    case NonFin
    thus ?thesis using noCom by auto
  qed
next
  case (Test \<phi>)
  hence noCom: "\<tau> = []" by auto
  thus ?case 
  proof (cases \<omega>)
    case (Fin \<omega>\<^sub>0)
    hence finState: "\<omega>\<^sub>0 = \<nu>" using Test.prems(4) by simp

    have "Vagree (sfilter \<nu> (CN\<^sub>F \<phi>)) (sfilter \<nu>' (CN\<^sub>F \<phi>)) (FV\<^sub>F \<phi>)"
      by (metis FV\<^sub>P.simps(4) Test.prems(2) Test.prems(3) Vagree_antimon Vagree_sfilter_cong)   
    moreover have "\<nu> \<in> fml_sem I \<phi>" using Test.prems(4) Fin by simp
    moreover have "wf_fml \<L>\<^sub>C \<phi>" using Test.prems(1) FOL\<^sub>R_is_wf_fml by auto
    ultimately have "\<nu>' \<in> fml_sem I \<phi>" using Test.IH by blast

    hence "(\<nu>', \<tau>, Fin \<nu>') \<in> chp_sem I (? \<phi>)" by (simp add: noCom)
    moreover have "Vagreebot \<omega> (Fin \<nu>') X" 
      using Test.prems(3) finState Fin unfolding Vagreebot_def Vagree_def by blast
    moreover have "Vagreebot \<omega> (Fin \<nu>') (MBV (Test \<phi>))" unfolding Vagreebot_def by (simp add: Fin)
    ultimately show ?thesis by auto
  next
    case NonFin
    thus ?thesis using noCom by auto
  qed
next 
  case (Evolution x \<theta> \<phi>)
  hence noCom: "\<tau> = []" by auto
  thus ?case
  proof (cases \<omega>)
    case (Fin \<omega>\<^sub>0)
    then obtain F T where 0: "Vagree \<nu> (F(0)) (-{Rv (DVarName x)}) \<and> F(T) = \<omega>\<^sub>0 
      \<and> solves_ODE I F x \<theta> \<and> (\<forall>\<zeta>. F(\<zeta>) \<in> fml_sem I \<phi>)"
      using Evolution by auto
    moreover have "Rv (RVarName x) \<in> X" using Evolution by simp
    moreover have "Rv (RVarName x) \<in> -{Rv (DVarName x)}" by blast
    ultimately have "\<nu>' $$ (Rv (RVarName x)) = F(0) $$ (Rv (RVarName x))"
      using Evolution(3,4) unfolding Vagree_def by metis
    hence iniagree: "Vagree \<nu>' ((solution_merge \<nu>' F x)(0)) (-{Rv (DVarName x)})"
      unfolding solution_merge_def Vagree_def by auto

    have QRpoly: "isQRpolynom \<theta>" using Evolution(2) by simp
    hence wf_rtrm: "wf_rtrm \<theta>" using QRpolynom_is_wf_rtrm by blast
    have wf_fml: "wf_fml \<L>\<^sub>C \<phi>" using Evolution(2) by (simp add: FOL\<^sub>R_is_wf_fml)

    have coin: "\<And>\<zeta>. Vagree (F(\<zeta>)) (solution_merge \<nu>' F x \<zeta>) X"
    proof -
      fix \<zeta>
      have "Vagree (F 0) (F \<zeta>) (- bvrident x)" using 0 unfolding solves_ODE_def by auto
      hence "Vagree (F 0) (F \<zeta>) (X\<inter>-{Rv (RVarName x), Rv (DVarName x)})"
        apply (rule Vagree_antimon) by simp
      moreover have "Vagree \<nu> (F 0) (X\<inter>-{Rv (RVarName x), Rv (DVarName x)})" 
        using 0 by (simp add: Vagree_def)
      ultimately have "Vagree \<nu> (F(\<zeta>)) (X\<inter>-{Rv (RVarName x), Rv (DVarName x)})" 
        using Vagree_only_trans by blast 
      moreover have "Vagree \<nu> \<nu>' (X\<inter>-{Rv (RVarName x), Rv (DVarName x)})"
        using Evolution by force
      ultimately have "Vagree (F(\<zeta>)) (solution_merge \<nu>' F x \<zeta>) (X\<inter>-{Rv (RVarName x), Rv (DVarName x)})"
        unfolding solution_merge_def by (simp add: Vagree_def)
      moreover have "Vagree (F(\<zeta>)) (solution_merge \<nu>' F x \<zeta>) ({Rv (RVarName x), Rv (DVarName x)})"
        unfolding Vagree_def solution_merge_def by simp
      moreover have "X\<inter>-{Rv (RVarName x), Rv (DVarName x)} \<union> {Rv (RVarName x), Rv (DVarName x)} = X\<union>{Rv (RVarName x), Rv (DVarName x)}" by blast
      ultimately have "Vagree (F(\<zeta>)) (solution_merge \<nu>' F x \<zeta>) (X\<union>{Rv (RVarName x), Rv (DVarName x)})" 
        using Vagree_and by metis
      thus "Vagree (F(\<zeta>)) (solution_merge \<nu>' F x \<zeta>) X" by (rule Vagree_antimon) (auto)
    qed

    have solves: "solves_ODE I (solution_merge \<nu>' F x) x \<theta>"
    unfolding solves_ODE_def proof 
      fix \<zeta>
      have "Vagree (solution_merge \<nu>' F x 0) (solution_merge \<nu>' F x \<zeta>) (- bvrident x)"
        unfolding Vagree_def solution_merge_def by auto
      moreover have 1: "stR (solution_merge \<nu>' F x \<zeta>) (DVarName x) = deriv (\<lambda>t. stR (solution_merge \<nu>' F x t) (RVarName x)) \<zeta>"
        using 0 unfolding solution_merge_def solves_ODE_def by simp
      moreover have "stR (solution_merge \<nu>' F x \<zeta>) (DVarName x) = rtrm_sem I \<theta> (solution_merge \<nu>' F x \<zeta>)"
      proof -
        have "FV\<^sub>R \<theta> \<subseteq> X" using Evolution by auto
        hence "Vagree (sfilter (F(\<zeta>)) (CN\<^sub>R \<theta>)) (sfilter (solution_merge \<nu>' F x \<zeta>) (CN\<^sub>R \<theta>)) (FV\<^sub>R \<theta>)"
          using coin Vagree_sfilter_cong Vagree_antimon by blast
        moreover have "stR (F \<zeta>) (DVarName x) = deriv (\<lambda>t. stR (F t) (RVarName x)) \<zeta> 
          \<and> stR (F \<zeta>) (DVarName x) = rtrm_sem I \<theta> (F \<zeta>)"
          using 0 unfolding solves_ODE_def by blast 
        ultimately have "stR (F \<zeta>) (DVarName x) = rtrm_sem I \<theta> (solution_merge \<nu>' F x \<zeta>)"
          using rtrm_coincidence wf_rtrm by metis
        thus ?thesis using 0 unfolding solves_ODE_def solution_merge_def by simp
      qed
      ultimately show "Vagree (solution_merge \<nu>' F x 0) (solution_merge \<nu>' F x \<zeta>) (- bvrident x) \<and>
         stR (solution_merge \<nu>' F x \<zeta>) (DVarName x) = deriv (\<lambda>t. stR (solution_merge \<nu>' F x t) (RVarName x)) \<zeta> \<and>
         stR (solution_merge \<nu>' F x \<zeta>) (DVarName x) = rtrm_sem I \<theta> (solution_merge \<nu>' F x \<zeta>)" by blast
    qed

    have "FV\<^sub>F \<phi> \<subseteq> X" using Evolution by auto
    hence "\<And>\<zeta>. Vagree (sfilter (F(\<zeta>)) (CN\<^sub>F \<phi>)) (sfilter ((solution_merge \<nu>' F x)(\<zeta>)) (CN\<^sub>F \<phi>)) (FV\<^sub>F \<phi>)"
      using coin Vagree_sfilter_cong Vagree_antimon by blast
    hence domain: "\<forall>\<zeta>. (solution_merge \<nu>' F x)(\<zeta>) \<in> fml_sem I \<phi>"
      using 0 Evolution.IH wf_fml by blast

    have "(\<nu>', [], Fin ((solution_merge \<nu>' F x)(T))) \<in> chp_sem I (Evolution x \<theta> \<phi>)"
      using iniagree solves domain by auto

    moreover have "Vagreebot \<omega> (Fin ((solution_merge \<nu>' F x)(T))) (X\<union>MBV(Evolution x \<theta> \<phi>))"
    proof -
      have "Vagree \<omega>\<^sub>0 ((solution_merge \<nu>' F x)(T)) (MBV(Evolution x \<theta> \<phi>))"
        using 0 Fin by (simp add: solution_merge_def Vagree_def)
      hence "Vagree \<omega>\<^sub>0 ((solution_merge \<nu>' F x)(T)) (X\<union>MBV(Evolution x \<theta> \<phi>))"
        using coin[where \<zeta>="T"] Vagree_and 0 by blast
      thus ?thesis unfolding Vagreebot_def using Fin by simp
    qed
    ultimately show ?thesis using noCom by blast
  next
    case NonFin
    thus ?thesis using noCom by auto
  qed
next
  case (Choice \<alpha> \<beta>)
  then consider "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha>" | "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<beta>" by auto
  hence "\<exists>\<omega>'. ((\<nu>', \<tau>, \<omega>') \<in> chp_sem I \<alpha> \<and> Vagreebot \<omega> \<omega>' (X \<union> MBV \<alpha>)) 
    \<or> (\<exists>\<omega>'. (\<nu>', \<tau>, \<omega>') \<in> chp_sem I \<beta> \<and> Vagreebot \<omega> \<omega>' (X \<union> MBV \<beta>))"  
    apply (cases)
    using Choice(5) Choice.IH Choice.prems(1,2) by auto
  thus ?case unfolding Vagreebot_def by (auto simp add: sup_inf_distrib1) 
next
  case (Compose \<alpha> \<beta>)
  
  let ?\<alpha> = "chp_sem I \<alpha>"
  let ?\<beta> = "chp_sem I \<beta>"

  consider (bot) "(\<nu>, \<tau>, \<omega>) \<in> botop ?\<alpha>" | (continue) "(\<nu>, \<tau>, \<omega>) \<in> ?\<alpha> \<triangleright> ?\<beta>" using Compose.prems(4) by auto  
  hence "(\<exists>\<omega>'. (\<nu>', \<tau>, \<omega>') \<in> botop ?\<alpha> \<and> Vagreebot \<omega> \<omega>' (X \<union> MBV \<alpha> \<union> MBV \<beta>)) 
    \<or> (\<exists>\<omega>'. (\<nu>', \<tau>, \<omega>') \<in> ?\<alpha> \<triangleright> ?\<beta> \<and> Vagreebot \<omega> \<omega>' (X \<union> MBV \<alpha> \<union> MBV \<beta>))"
  proof (cases)
    case bot
    obtain \<omega>\<^sub>0 where "(\<nu>, \<tau>, \<omega>\<^sub>0) \<in> chp_sem I \<alpha>" using bot by auto
    then obtain \<omega>\<^sub>0' where "(\<nu>', \<tau>, \<omega>\<^sub>0') \<in> chp_sem I \<alpha>" 
       by (metis Compose.IH(1) Compose.prems(1,2,3) FV\<^sub>P.simps(7) sup.bounded_iff wf_chp.simps(7))
    thus ?thesis using Vagreebot_NonFin bot by auto
  next
    case continue
    obtain \<kappa> \<tau>\<^sub>1 \<tau>\<^sub>2 where 
      runA: "(\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> ?\<alpha>" and 
      runB: "(\<kappa>, \<tau>\<^sub>2, \<omega>) \<in> ?\<beta>" and 
      com: "\<tau> = \<tau>\<^sub>1 @ \<tau>\<^sub>2" using continue by auto
    obtain \<kappa>' where runA': "(\<nu>', \<tau>\<^sub>1, Fin \<kappa>') \<in> ?\<alpha>" and "Vagreebot (Fin \<kappa>) (Fin \<kappa>') (X \<union> MBV \<alpha>)"
      by (metis (no_types, lifting) Compose.IH(1) Compose.prems(1) Compose.prems(2) Compose.prems(3) FV\<^sub>P.simps(7) Vagreebot_def runA sup.bounded_iff wf_chp.simps(7))
    hence "Vagree \<kappa> \<kappa>' (X \<union> MBV \<alpha>)" using Vagreebot_only_Fin by blast
    hence "\<exists>\<omega>'. (\<kappa>', \<tau>\<^sub>2, \<omega>') \<in> ?\<beta> \<and> Vagreebot \<omega> \<omega>' (X \<union> MBV \<alpha> \<union> MBV \<beta>)" 
      by (metis Compose.IH(2) Compose.prems(1,2) Diff_subset_conv FV\<^sub>P.simps(7) runB sup.bounded_iff sup_commute wf_chp.simps(7))      
    then obtain \<omega>' where runB': "(\<kappa>', \<tau>\<^sub>2, \<omega>') \<in> ?\<beta>" and "Vagreebot \<omega> \<omega>' (X \<union> MBV \<alpha> \<union> MBV \<beta>)" by auto
    moreover have "(\<nu>', \<tau>, \<omega>') \<in> ?\<alpha> \<triangleright> ?\<beta>" using com runA' runB' by auto
    ultimately show ?thesis by blast
  qed
  thus ?case by (metis MBV.simps(7) UnCI chp_sem.simps(7) sup_assoc)
next
  case (Loop \<alpha>)
  let ?D = "chp_sem I \<alpha>"
  have initAgree: "Vagree \<nu> \<nu>' X" using Loop.prems(3) by auto
  have "\<And>n. (\<nu>, \<tau>, \<omega>) \<in> iterate_linhis n ?D \<Longrightarrow> \<exists>\<omega>'. (\<nu>', \<tau>, \<omega>') \<in> iterate_linhis n ?D \<and> Vagreebot \<omega> \<omega>' X"
  proof -
    fix n   
    assume run: "(\<nu>, \<tau>, \<omega>) \<in> iterate_linhis n ?D"
    have "\<exists>\<omega>'. (\<nu>', \<tau>, \<omega>') \<in> iterate_linhis n ?D \<and> Vagreebot \<omega> \<omega>' X" using initAgree run
    proof (induction n arbitrary: \<nu> \<tau> \<nu>')
      case 0      
      let ?\<omega>' = "if \<omega> = NonFin then NonFin else Fin \<nu>'"
      have "(\<nu>, \<tau>, \<omega>) \<in> (iterate_linhis 0 ?D)" using 0 by auto
      hence noCom: "\<tau> = []" and cases: "\<omega> = NonFin \<or> \<omega> = Fin \<nu>" using iterate_linhis.simps(1) by auto
      hence "(\<nu>', \<tau>, ?\<omega>') \<in> iterate_linhis 0 ?D \<and> Vagreebot \<omega> ?\<omega>' X"
      proof (cases \<omega>)
        case (Fin \<nu>)
        hence "\<omega> = Fin \<nu>" and "?\<omega>' = Fin \<nu>'" by (simp, simp add: Fin)
        hence "(\<nu>', \<tau>, ?\<omega>') \<in> iterate_linhis 0 ?D" using noCom by simp
        moreover have "Vagreebot \<omega> ?\<omega>' X" 
          using 0 Vagreebot_NonFin Vagreebot_only_Fin cases by auto
        ultimately show ?thesis by simp
      next
        case NonFin
        thus ?thesis using noCom chp_sem_Repeat chp_sem_least_computations by simp
      qed        
      thus ?case by blast
    next
      case (Suc n)
      hence cases: "(\<nu>, \<tau>, \<omega>) \<in> (botop ?D) \<or> (\<nu>, \<tau>, \<omega>) \<in> (?D \<triangleright> (iterate_linhis n ?D))" by simp      
      have "\<exists>\<omega>'. (\<nu>', \<tau>, \<omega>') \<in> iterate_linhis (Suc n) ?D \<and> Vagreebot \<omega> \<omega>' X"
      proof (cases "(\<nu>, \<tau>, \<omega>) \<in> botop ?D")
        case True   
        have run: "(\<nu>, \<tau>, \<omega>) \<in> botop ?D" using True by auto
        hence nonfin: "\<omega> = NonFin" by simp
        let ?\<omega>' = "NonFin"
        from run have "(\<nu>, \<tau>, \<omega>) \<in> ?D" using chp_sem_total_and_pc denotations_contain_bot by blast
        hence run': "\<exists>\<omega>'. (\<nu>', \<tau>, \<omega>') \<in> ?D \<and> Vagreebot \<omega> \<omega>' (X \<union> MBV \<alpha>)" 
          by (metis FV\<^sub>P.simps(8) Loop.IH Loop.prems(1) Loop.prems(2) Suc.prems(1) wf_chp.simps(8))         
        hence "(\<nu>', \<tau>, ?\<omega>') \<in> botop ?D" by auto
        moreover have "Vagreebot \<omega> ?\<omega>' X" by (simp add: nonfin)
        ultimately show ?thesis by auto
      next
        case False  (* (\<nu>, \<tau>, \<omega>) \<in> ?D \<triangleright> (iterate_linhis n ?D)" *)
        hence run: "(\<nu>, \<tau>, \<omega>) \<in> (?D \<triangleright> (iterate_linhis n ?D))" using cases by auto
        then obtain \<kappa> \<tau>\<^sub>1 \<tau>\<^sub>2 where 
          runD: "(\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> ?D" and 
          runL: "(\<kappa>, \<tau>\<^sub>2, \<omega>) \<in> (iterate_linhis n ?D)" and com: "\<tau> = \<tau>\<^sub>1 @ \<tau>\<^sub>2" by auto
        then obtain \<kappa>' where runD': "(\<nu>', \<tau>\<^sub>1, Fin \<kappa>') \<in> ?D" and "Vagreebot (Fin \<kappa>) (Fin \<kappa>') (X \<union> MBV \<alpha>)"        
          by (metis FV\<^sub>P.simps(8) Loop.IH Loop.prems(1) Loop.prems(2) Suc.prems(1) Vagreebot_def reachedstate.distinct(1) wf_chp.simps(8))
        hence "Vagree \<kappa> \<kappa>' X" using Vagreebot_only_Fin by simp
        hence "\<exists>\<omega>'. (\<kappa>', \<tau>\<^sub>2, \<omega>') \<in> (iterate_linhis n ?D) \<and> Vagreebot \<omega> \<omega>' X" 
          using runL Suc.IH by blast 
        then obtain \<omega>' where runL': "(\<kappa>', \<tau>\<^sub>2, \<omega>') \<in> (iterate_linhis n ?D)" and "Vagreebot \<omega> \<omega>' X" by blast
        moreover have "(\<nu>', \<tau>, \<omega>') \<in> ?D \<triangleright> (iterate_linhis n ?D)" using com runD' runL' by auto
        ultimately show ?thesis by (metis Un_iff iterate_linhis.simps(2))
      qed 
      thus ?case by simp
    qed
    thus "\<exists>\<omega>'. (\<nu>', \<tau>, \<omega>') \<in> iterate_linhis n ?D \<and> Vagreebot \<omega> \<omega>' X" by auto
  qed
  moreover obtain n where "(\<nu>, \<tau>, \<omega>) \<in> iterate_linhis n ?D" using Loop chp_sem_Loop_by_iterate by fastforce
  ultimately have "\<exists>\<omega>'. (\<nu>', \<tau>, \<omega>') \<in> chp_sem I (\<alpha>**) \<and> Vagreebot \<omega> \<omega>' (X \<union> MBV (Loop \<alpha>))" using linhis_rtcl_eq_iteration by fastforce
  thus ?case by simp
next
  case (Send ch h \<theta>) 
  hence "Vagree (sfilter \<nu> (CN\<^sub>R \<theta>)) (sfilter \<nu>' (CN\<^sub>R \<theta>)) (FV\<^sub>R \<theta>)" using Vagree_antimon Vagree_sfilter_cong by simp
  moreover have "wf_rtrm \<theta>" using Send(1) QRpolynom_is_wf_rtrm by simp
  ultimately have semEq: "(rtrm_sem I \<theta> \<nu>) = (rtrm_sem I \<theta> \<nu>')" using rtrm_coincidence by simp
  have "Vagree \<nu> \<nu>' { Rv \<mu> }" using Send.prems(2) Send.prems(3) Vagree_antimon by simp
  hence timeEq: "(stR \<nu> \<mu>) = (stR \<nu>' \<mu>)" by (simp add: Vagree_def)
  thus ?case 
  proof (cases \<omega>)
    case (Fin \<omega>\<^sub>0)
    hence obs: "(\<tau>, Fin \<omega>\<^sub>0) \<sqsubseteq> ([mkrecevent h ch (rtrm_sem I \<theta> \<nu>) (stR \<nu> \<mu>)], Fin \<nu>)" 
      using Send.prems(4) by simp
    then obtain \<omega>\<^sub>0' where obs': "(\<tau>, Fin \<omega>\<^sub>0') \<sqsubseteq> ([mkrecevent h ch (rtrm_sem I \<theta> \<nu>') (stR \<nu>' \<mu>)], Fin \<nu>')"
      using semEq timeEq by (simp add: obspref_alt)
    hence "(\<nu>', \<tau>, Fin \<omega>\<^sub>0') \<in> chp_sem I (Send ch h \<theta>)" by simp
    moreover have "Vagreebot (Fin \<omega>\<^sub>0) (Fin \<omega>\<^sub>0') X" unfolding Vagreebot_def using obs obs' obspref_alt by (metis Send.prems(3) reachedstate.distinct(1))
    moreover have "Vagreebot (Fin \<omega>\<^sub>0) (Fin \<omega>\<^sub>0') (MBV (Send ch h \<theta>))" by (simp add: Vagreebot_def)
    ultimately show ?thesis unfolding Vagreebot_def using Fin Vagree_union by blast
  next
    case NonFin
    thus ?thesis using timeEq semEq Send.prems(4) by (auto simp add: obspref_alt)
  qed 
next
  case (Receive ch h x)
  hence "Vagree \<nu> \<nu>' { Rv \<mu> }" using Vagree_antimon by simp
  hence timeEq: "(stR \<nu> \<mu>) = (stR \<nu>' \<mu>)" by (simp add: Vagree_def)  
  show ?case 
  proof (cases \<omega>)
    case (Fin \<omega>\<^sub>0)
    hence run: "(\<nu>, \<tau>, Fin \<omega>\<^sub>0) \<in> chp_sem I (Receive ch h x)" using Receive.prems(4) by simp    
    then obtain r where obs: "(\<tau>, Fin \<omega>\<^sub>0) \<sqsubseteq> ([mkrecevent h ch r (stR \<nu> \<mu>)], Fin (rrepv \<nu> x r))" by auto
    from timeEq obs obtain \<omega>\<^sub>0' where otherObs: "(\<tau>, Fin \<omega>\<^sub>0') \<sqsubseteq> ([mkrecevent h ch r (stR \<nu>' \<mu>)], Fin (rrepv \<nu>' x r))" by (simp add: obspref_alt)
    hence run': "(\<nu>', \<tau>, Fin \<omega>\<^sub>0') \<in> chp_sem I (Receive ch h x)" by auto
    from run have fin: "\<omega>\<^sub>0 = rrepv \<nu> x r" using receive_var_change by (meson obspref_alt reachedstate.discI reachedstate.inject obs)
    moreover from run' have fin': "\<omega>\<^sub>0' = rrepv \<nu>' x r" using receive_var_change by (meson obspref_alt otherObs reachedstate.distinct(1) reachedstate.inject)
    ultimately have "Vagree \<omega>\<^sub>0 \<omega>\<^sub>0' X" using Receive.prems(3) Vagree_def by fastforce
    hence "Vagreebot (Fin \<omega>\<^sub>0) (Fin \<omega>\<^sub>0') X" by (simp add: Vagreebot_def)
    moreover have "Vagreebot (Fin \<omega>\<^sub>0) (Fin \<omega>\<^sub>0') (MBV (Receive ch h x))" unfolding Vagreebot_def MBV.simps(11) using Vagree_def fin fin' by auto
    ultimately show ?thesis unfolding Vagreebot_def using Fin Vagree_union run' by blast   
  next
    case NonFin
    thus ?thesis using timeEq Receive.prems(4) by (auto simp add: obspref_alt)
  qed 
next
  case (Par \<alpha> \<beta>)
  hence overapprox: "\<And>\<alpha>. BVP\<^sub>\<L> \<L>\<^sub>C \<alpha> \<supseteq> BVP (\<pi>\<^sub>I I) \<alpha>" using BVP_overapprox by simp
  moreover have disjoint: "BVP\<^sub>\<L> \<L>\<^sub>C \<alpha> \<inter> BVP\<^sub>\<L> \<L>\<^sub>C \<beta> \<subseteq> \<V>\<^sub>\<mu> \<union> \<iota>\<^sub>T \<V>\<^sub>T" using Par by auto
  ultimately have "(\<nu>, \<tau>, \<omega>) \<in> chp_alt_sem_par \<L>\<^sub>C I \<alpha> \<beta>" using Par by (metis chp_sem_eq_alt_sem) 

  then obtain \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta>                                                                       
    where "(\<nu>, \<tau> \<down> CN (\<pi>\<^sub>I I) \<alpha>, \<omega>\<^sub>\<alpha>) \<in> chp_sem I \<alpha>"
      and "(\<nu>, \<tau> \<down> CN (\<pi>\<^sub>I I) \<beta>, \<omega>\<^sub>\<beta>) \<in> chp_sem I \<beta>"
      and gtime: "Vagreebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> \<V>\<^sub>\<mu>"
      and merge_BV: "\<omega> = lmergebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> (BV \<alpha>)"
      and nojunk: "\<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha> \<union> CN (\<pi>\<^sub>I I) \<beta>) = \<tau>" 
    using chp_alt_sem_par_def by auto

  (* Subruns for the other initial state \<nu>' exist by IH *)
  then obtain \<omega>\<^sub>\<alpha>' \<omega>\<^sub>\<beta>' where
    alpha': "(\<nu>', \<tau> \<down> CN (\<pi>\<^sub>I I) \<alpha>, \<omega>\<^sub>\<alpha>') \<in> chp_sem I \<alpha>" and 
    agree_alpha: "Vagreebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<alpha>' (X \<union> MBV \<alpha>)" and
    beta': "(\<nu>', \<tau> \<down> CN (\<pi>\<^sub>I I) \<beta>, \<omega>\<^sub>\<beta>') \<in> chp_sem I \<beta>" and 
    agree_beta: "Vagreebot \<omega>\<^sub>\<beta> \<omega>\<^sub>\<beta>' (X \<union> MBV \<beta>)"
    by (metis FV\<^sub>P.simps(11) Par.IH Par.prems(1) Par.prems(2) Par.prems(3) le_sup_iff wf_chp.simps(11))  

  let ?\<omega>' = "lmergebot \<omega>\<^sub>\<alpha>' \<omega>\<^sub>\<beta>' (BV \<alpha>)"

  (* The subruns can be combined to a run of \<alpha> || \<beta> starting from \<nu>' *)
  have "\<V>\<^sub>\<mu> \<subseteq> X" using Par.prems(2) by simp
  hence gtime_alpha: "Vagreebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<alpha>' \<V>\<^sub>\<mu>" and gtime_beta: "Vagreebot \<omega>\<^sub>\<beta> \<omega>\<^sub>\<beta>' \<V>\<^sub>\<mu>" 
    using agree_alpha agree_beta unfolding Vagreebot_def by (metis Vagree_and Vagree_antimon)+
  hence "Vagreebot \<omega>\<^sub>\<alpha>' \<omega>\<^sub>\<alpha> \<V>\<^sub>\<mu>" unfolding Vagreebot_def using Vagree_sym by blast
  hence gtime': "Vagreebot \<omega>\<^sub>\<alpha>' \<omega>\<^sub>\<beta>' \<V>\<^sub>\<mu>" using gtime gtime_beta Vagreebot_trans by (metis Int_absorb)
  hence "(\<nu>', \<tau>, ?\<omega>') \<in> chp_alt_sem_par \<L>\<^sub>C I \<alpha> \<beta>" 
    using nojunk alpha' beta' chp_alt_sem_par_def by auto 
  hence "(\<nu>', \<tau>, ?\<omega>') \<in> chp_sem I (\<alpha> par \<beta>)" 
    using chp_sem_eq_alt_sem disjoint overapprox BVP_overapprox by metis

  (* The alternative final state ?\<omega>' coincides with the original final state \<omega> on X \<union> MBV (\<alpha> par \<beta>) *)
  moreover have "Vagreebot \<omega> ?\<omega>' (X \<union> MBV (\<alpha> par \<beta>))" using agree_alpha agree_beta
  proof (cases \<omega>)
    case (Fin \<omega>\<^sub>0)
    hence lmerge: "\<omega>\<^sub>0 = lmerge (gets \<omega>\<^sub>\<alpha>) (gets \<omega>\<^sub>\<beta>) (BV \<alpha>)"
      using merge_BV lmergebot_Exists_Fin by fastforce

    let ?\<omega>'' = "lmerge (gets \<omega>\<^sub>\<alpha>') (gets \<omega>\<^sub>\<beta>') (BV \<alpha>)"
    have fin': "?\<omega>' = Fin ?\<omega>''"  
      by (metis Fin Vagreebot_def gtime_alpha agree_beta lmergebot.elims lmergebot.simps(1) merge_BV reachedstate.collapse reachedstate.discI)
    hence lmerge': "Fin ?\<omega>'' = lmergebot \<omega>\<^sub>\<alpha>' \<omega>\<^sub>\<beta>' (BV \<alpha>)" by auto

    (* Coincidence on MBV \<alpha> *)
    have "Vagree \<omega>\<^sub>0 (gets \<omega>\<^sub>\<alpha>) (BV \<alpha>)" using lmerge lmerge_vagree by blast
    hence origin_alpha: "Vagree \<omega>\<^sub>0 (gets \<omega>\<^sub>\<alpha>) (MBV \<alpha>)" by (meson MBV_subset_BV Vagree_antimon)
    have "Vagree ?\<omega>'' (gets \<omega>\<^sub>\<alpha>') (BV \<alpha>)" using lmerge' lmerge_vagree by blast
    hence target_alpha: "Vagree ?\<omega>'' (gets \<omega>\<^sub>\<alpha>') (MBV \<alpha>)" by (meson MBV_subset_BV Vagree_antimon)     
    have "Vagree (gets \<omega>\<^sub>\<alpha>) (gets \<omega>\<^sub>\<alpha>') (MBV \<alpha>)" using agree_alpha Vagreebot_def by auto
    hence "Vagree \<omega>\<^sub>0 ?\<omega>'' (MBV \<alpha>)" using origin_alpha target_alpha by (meson Vagree_sym Vagree_only_trans)
      
    (* Coincidence on MBV \<beta> *)
    moreover have "Vagree \<omega>\<^sub>0 ?\<omega>'' (MBV \<beta>)" 
    proof -
      have "MBV \<beta> \<subseteq> (-BV \<alpha>) \<union> \<V>\<^sub>\<mu> \<union> \<iota>\<^sub>T \<V>\<^sub>T" using disjoint MBV_subset_BV by auto
      hence mbv: "(MBV \<beta>) \<subseteq> (-BV \<alpha>) \<union> \<V>\<^sub>\<mu>" using MBV_only_rvars time_is_real tvars_compl by blast

      (* Vagree \<omega>\<^sub>0 (gets \<omega>\<^sub>\<beta>) (-(BV \<alpha>) \<union> (\<V>\<^sub>\<mu>)) *)
      have "Vagree \<omega>\<^sub>0 (gets \<omega>\<^sub>\<beta>) (-(BV \<alpha>))" using lmerge lmerge_vagree Vagree_antimon by simp
      moreover have "Vagree \<omega>\<^sub>0 (gets \<omega>\<^sub>\<beta>) (\<V>\<^sub>\<mu>)"
        unfolding Vagree_def using lmerge Vagree_def Vagreebot_def gtime by auto
      ultimately have agree_compl_orig: "Vagree \<omega>\<^sub>0 (gets \<omega>\<^sub>\<beta>) (MBV \<beta>)"
        using lmerge Vagree_def Vagree_union Vagree_antimon mbv by metis   

      (* Vagree ?\<omega>'' (gets \<omega>\<^sub>\<beta>') (-(BV \<alpha>) \<union> (\<V>\<^sub>\<mu>)) *)
      have "Vagree ?\<omega>'' (gets \<omega>\<^sub>\<beta>') (-(BV \<alpha>))" using lmerge lmerge_vagree Vagree_antimon by blast
      moreover have "Vagree ?\<omega>'' (gets \<omega>\<^sub>\<beta>') (\<V>\<^sub>\<mu>)" 
        unfolding Vagree_def lmerge using gtime' Vagree_def Vagreebot_def by auto
      ultimately have agree_compl_targ: "Vagree ?\<omega>'' (gets \<omega>\<^sub>\<beta>') (MBV \<beta>)" 
        using lmerge Vagree_def Vagree_union Vagree_antimon mbv by blast

      (* Vagree \<omega>\<^sub>0 ?\<omega>'' (MBV \<beta>) *)
      have "Vagree (gets \<omega>\<^sub>\<beta>) (gets \<omega>\<^sub>\<beta>') (MBV \<beta>)" using agree_beta Vagreebot_def by auto      
      thus "Vagree \<omega>\<^sub>0 ?\<omega>'' (MBV \<beta>)" 
        using agree_compl_orig agree_compl_targ by (meson Vagree_sym_rel Vagree_only_trans)  
    qed  

    (* Coincide on X *)
    moreover have "Vagree \<omega>\<^sub>0 ?\<omega>'' X" unfolding Vagree_def lmerge using agree_alpha agree_beta UnCI Vagree_def Vagreebot_def lmerge_access reachedstate.sel by auto    
    
    ultimately have "Vagree \<omega>\<^sub>0 ?\<omega>'' (X \<union> MBV (\<alpha> par \<beta>))" using Vagree_union by simp
    hence "\<exists>\<omega>'. ?\<omega>' = Fin \<omega>' \<and> lmergebot \<omega>\<^sub>\<alpha>' \<omega>\<^sub>\<beta>' (BV \<alpha>) = Fin \<omega>' \<and> Vagree \<omega>\<^sub>0 \<omega>' (X \<union> MBV (\<alpha> par \<beta>))" 
      using fin' lmerge' by blast
    thus ?thesis unfolding Vagreebot_def using Fin by blast
  next
    case NonFin
    hence "?\<omega>' = NonFin" by (metis MBV.simps(4) Vagreebot_def gtime_alpha gtime_beta merge_BV lmergebot.elims lmergebot.simps(2) reachedstate.distinct(1))
    thus ?thesis unfolding Vagreebot_def using NonFin by blast 
  qed 
  ultimately show ?case by blast
qed



subsection \<open>Soundness of the Computable Static Semantics\<close>

lemma computable_stat_sem_sound: "wf_fml \<L>\<^sub>C \<phi> \<Longrightarrow> CN\<^sub>F \<phi> \<supseteq> CNE J \<phi> \<and> FV\<^sub>F \<phi> \<supseteq> FVE J \<phi>"
proof -
  assume "wf_fml \<L>\<^sub>C \<phi>"
  hence "\<And>I \<nu> \<nu>'. Vagree (sfilter \<nu> (CN\<^sub>F \<phi>)) (sfilter \<nu>' (CN\<^sub>F \<phi>)) (FV\<^sub>F \<phi>) 
    \<Longrightarrow> (\<nu> \<in> (fml_sem I \<phi>) \<Longrightarrow> \<nu>' \<in> (fml_sem I \<phi>))" using computable_coincidence_fml by simp
  hence "\<And>I \<nu> \<nu>'. Vagree (sfilter \<nu> (CN\<^sub>F \<phi>)) (sfilter \<nu>' (CN\<^sub>F \<phi>)) (FV\<^sub>F \<phi>) 
    \<Longrightarrow> expr_sem I \<phi> \<nu> = expr_sem I \<phi> \<nu>'" using Vagree_sym expr_sem_fml_def by auto
  thus "CN\<^sub>F \<phi> \<supseteq> CNE J \<phi> \<and> FV\<^sub>F \<phi> \<supseteq> FVE J \<phi>" using FVE_CNE_least_sat_coincidence by blast
qed

  

end
