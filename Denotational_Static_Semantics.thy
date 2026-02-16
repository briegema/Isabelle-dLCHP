theory "Denotational_Static_Semantics" 
imports
  "Syntax"
  "Denotational_Semantics"
  "HOL.Finite_Set"
begin

section \<open>Denotational Static Semantics\<close>

subsection \<open>Partition of the Denotational Static Semantics\<close>

text \<open>The denotational static semantics in Section \<open>Denotational_Semantics\<close> unifies and generalizes 
notions of free variables and accessed channels. The following definitions provide the original 
notions and their relation with the denotational static semantics is proven.\<close>

text \<open>Free variables of the evaluation function \<open>E\<close>\<close>
definition FVF :: "(state \<Rightarrow> 'a) \<Rightarrow> variable set"
  where "FVF E = {x. \<exists>\<nu>.\<exists>\<omega>. Vagree \<nu> \<omega> (-{x}) \<and> \<not>(E \<nu> = E \<omega>)}"

text \<open>Channels accessed by the evaluation function \<open>E\<close>\<close>
definition CNF :: "(state \<Rightarrow> 'a) \<Rightarrow> comtar set"
  where "CNF E = {(h, ch). \<exists>\<nu>.\<exists>\<omega>. sfilter \<nu> (-{(h, ch)}) = sfilter \<omega> (-{(h, ch)}) \<and> \<not>(E \<nu> = E \<omega>)}"

text \<open>Variables bound by the denotation \<open>D\<close> from the initial to the final world\<close>
definition BVD :: "chp_domain set \<Rightarrow> variable set"
  where "BVD D = {z. \<exists>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> D \<and> ((\<omega> \<squnion> \<nu>) @@ \<tau>) $$ z \<noteq> \<nu> $$ z}"

text \<open>Channels bound per recorder (trace) variable by the denotation \<open>D\<close>\<close>
definition CND :: "chp_domain set \<Rightarrow> comtar set"
  where "CND D = {(h, ch). \<exists>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> D \<and> byrec \<tau> h \<down> {ch} \<noteq> []}"

lemma FNF_partition_per_name: "(b \<in> FNF E) = (b \<in> \<iota>\<^sub>V (FVF E) \<union> \<iota>\<^sub>C (CNF E))"
  unfolding FNF_def FVF_def CNF_def VCagree_def
  apply (cases b)
  using allcomtar_def sfilter_all by simp_all

lemma FNF_partition: "FNF E = \<iota>\<^sub>V (FVF E) \<union> \<iota>\<^sub>C (CNF E)"
  using FNF_partition_per_name by auto

lemma BND_subseteq_BVD_Bv: "Bv z \<in> BND D \<Longrightarrow> Bv z \<in> \<iota>\<^sub>V (BVD D)"
  unfolding BND_def BVD_def VCagree_def Vagree_def
  apply (cases z)
   apply (simp_all add: tsfilter_def)
   apply metis
  by (fastforce simp add: tsfilter_def pi_vars_def)
  
lemma BVD_subseteq_BND_Tv: "DiffD D \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R \<Longrightarrow> Bv (Tv h) \<in> \<iota>\<^sub>V (BVD D) \<Longrightarrow> Bv (Tv h) \<in> BND D"
  unfolding BVD_def BND_def VCagree_def Vagree_def
  apply (simp add: tsfilter_def pi_vars_def pi_comtar_def)
  by metis
  
lemma BVD_subseteq_BND_Bv: "DiffD D \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R \<Longrightarrow> Bv z \<in> \<iota>\<^sub>V (BVD D) \<Longrightarrow> Bv z \<in> BND D"
  apply (cases z)
   apply (simp add: BND_def BVD_def VCagree_def Vagree_def)
   apply metis
  using BVD_subseteq_BND_Tv by simp

lemma BND_BVD_per_Bv: "DiffD D \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R \<Longrightarrow> Bv z \<in> BND D = (Bv z \<in> \<iota>\<^sub>V (BVD D))"
  using BVD_subseteq_BND_Bv BND_subseteq_BVD_Bv by auto

lemma BND_CND_per_Bc: "DiffD D \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R \<Longrightarrow> Bc h ch \<in> BND D = (Bc h ch \<in> \<iota>\<^sub>C (CND D))"
proof -
  assume 0: "DiffD D \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R"
  hence "Bc h ch \<in> BND D \<Longrightarrow> Bc h ch \<in> \<iota>\<^sub>C (CND D)"
    unfolding BND_def CND_def VCagree_def Vagree_def
    by (fastforce simp add: stT_sttconc_dist)
  moreover have "Bc h ch \<in> \<iota>\<^sub>C (CND D) \<Longrightarrow> Bc h ch \<in> BND D"
    unfolding CND_def BND_def VCagree_def Vagree_def
    using 0 by (fastforce simp add: stT_sttconc_dist)
  ultimately show ?thesis by auto
qed

lemma BND_partition_per_binder: "DiffD D \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R \<Longrightarrow> (b \<in> BND D) = (b \<in> \<iota>\<^sub>V (BVD D) \<union> \<iota>\<^sub>C (CND D))"
  apply (cases b)
  using BND_BVD_per_Bv BND_CND_per_Bc by auto
  
lemma BND_partition: "DiffD D \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R \<Longrightarrow> BND D = \<iota>\<^sub>V (BVD D) \<union> \<iota>\<^sub>C (CND D)"
  using BND_partition_per_binder by blast



subsection \<open>Coincidence for Evaluations\<close>

abbreviation traceinterpol:: "trace \<Rightarrow> chan set \<Rightarrow> trace set"
  where "traceinterpol \<tau> Y \<equiv> { \<tau>' | \<tau>'. \<tau>' \<down> Y = \<tau> \<down> Y }"

text \<open>Lemma 23 in \<open>https://arxiv.org/abs/2303.17333\<close>\<close>
lemma trace_interpolation:
  assumes "Y\<^sub>0 = Y \<union> { ch } \<and> ch \<notin> Y" (* union must be disjoint! *)
  shows "\<tau>' \<in> traceinterpol \<tau> Y \<Longrightarrow> \<exists>\<tau>''. \<tau>'' \<in> traceinterpol \<tau> Y\<^sub>0 \<and> \<tau>'' \<in> traceinterpol \<tau>' (-{ch})"
proof (induction \<tau>' arbitrary: \<tau>)
  case 0: Nil
  show "\<exists>\<tau>''. \<tau>'' \<in> traceinterpol \<tau> Y\<^sub>0 \<and> \<tau>'' \<in> traceinterpol [] (-{ch})"
  proof
    let ?\<tau>'' = "\<tau> \<down> { ch }"

    have "?\<tau>'' \<in> traceinterpol \<tau> Y\<^sub>0"
    proof -
      have "\<tau> \<down> Y = []" using 0 by auto
      moreover have "?\<tau>'' \<down> Y\<^sub>0 = \<tau> \<down> ({ ch } \<inter> Y\<^sub>0)" unfolding tfilter_def by simp
      ultimately have "\<tau> \<down> { ch } = \<tau> \<down> Y\<^sub>0"
        using filter_add_empty_pred assms 0 by (simp add: tfilter_def)
      thus ?thesis using tfilter_def by auto
    qed

    thus "?\<tau>'' \<in> traceinterpol \<tau> Y\<^sub>0 \<and> ?\<tau>'' \<in> traceinterpol [] (-{ch})" using tfilter_def by auto
  qed
next
  case (Cons \<rho> \<tau>\<^sub>0')
  show "\<exists>\<tau>''. \<tau>'' \<in> traceinterpol \<tau> Y\<^sub>0 \<and>  \<tau>'' \<in> traceinterpol (\<rho> # \<tau>\<^sub>0') (-{ch})"
  proof (cases "along \<rho> \<in> Y")
    case True
    hence Cons_hd_in: "\<tau> \<down> Y = \<rho> # \<tau>\<^sub>0' \<down> Y" using tfilter_def Cons by auto
    then obtain \<tau>\<^sub>1 \<tau>\<^sub>2 where tauSplit: "\<tau> = \<tau>\<^sub>1 @ [\<rho>] @ \<tau>\<^sub>2 \<and> \<tau>\<^sub>1 \<down> Y = []" 
      using filter_hd_in_middle tfilter_def by metis
    hence "\<tau> \<down> Y = \<rho> # (\<tau>\<^sub>2 \<down> Y)" using True tfilter_def by auto
    hence "\<exists>\<tau>\<^sub>0''. \<tau>\<^sub>0'' \<in> traceinterpol \<tau>\<^sub>2 Y\<^sub>0 \<and> \<tau>\<^sub>0'' \<down> -{ch} =  \<tau>\<^sub>0' \<down> -{ch}" 
      using Cons Cons_hd_in tfilter_def by auto
    then obtain \<tau>\<^sub>0'' where IH: "\<tau>\<^sub>0'' \<in> traceinterpol \<tau>\<^sub>2 Y\<^sub>0 \<and> \<tau>\<^sub>0'' \<down> -{ch} =  \<tau>\<^sub>0' \<down> -{ch}" by auto
    
    let ?\<tau>'' = "\<tau>\<^sub>1 \<down> { ch } @ [\<rho>] @ \<tau>\<^sub>0''"

    have "?\<tau>'' \<in> traceinterpol \<tau> Y\<^sub>0"
    proof -
      from tauSplit have "\<tau>\<^sub>1 \<down> { ch } = \<tau>\<^sub>1 \<down> Y\<^sub>0" 
        using filter_add_empty_pred assms by (auto simp add: tfilter_def)
      hence "?\<tau>'' \<down> Y\<^sub>0 = (\<tau>\<^sub>1 \<down> Y\<^sub>0) @ ([\<rho>] \<down> Y\<^sub>0) @ (\<tau>\<^sub>0'' \<down> Y\<^sub>0)" by (simp add: tfilter_def)
      hence "?\<tau>'' \<down> Y\<^sub>0 = (\<tau>\<^sub>1 \<down> Y\<^sub>0) @ ([\<rho>] \<down> Y\<^sub>0) @ (\<tau>\<^sub>2 \<down> Y\<^sub>0)" using IH tfilter_def by auto
      hence "?\<tau>'' \<down> Y\<^sub>0 = \<tau> \<down> Y\<^sub>0" using tauSplit by (simp add: tfilter_def)
      thus "?\<tau>'' \<in> traceinterpol \<tau> Y\<^sub>0" by simp
    qed

    moreover have "?\<tau>'' \<in> traceinterpol (\<rho> # \<tau>\<^sub>0') (-{ch})"
    proof -
      have "?\<tau>'' \<down> (-{ ch }) = (\<tau>\<^sub>1 \<down> ({ ch } \<inter> (-{ ch }))) @ ([\<rho>] \<down> (-{ ch })) @ (\<tau>\<^sub>0'' \<down> (-{ ch }))"
        by (simp add: tfilter_def)
      hence "?\<tau>'' \<down> (-{ ch }) = ([\<rho>] \<down> (-{ ch })) @ (\<tau>\<^sub>0'' \<down> (-{ ch }))" using tfilter_def by auto
      thus "?\<tau>'' \<in> traceinterpol (\<rho> # \<tau>\<^sub>0') (-{ch})" using IH by (simp add: tfilter_def)
    qed

    ultimately show "\<exists>\<tau>''. \<tau>'' \<in> traceinterpol \<tau> Y\<^sub>0 \<and> \<tau>'' \<in> traceinterpol (\<rho> # \<tau>\<^sub>0') (-{ch})" by blast
  next
    case False
    hence "\<tau>\<^sub>0' \<in> traceinterpol \<tau> Y" using Cons by auto
    then obtain \<tau>\<^sub>0'' where IH: "\<tau>\<^sub>0'' \<in> traceinterpol \<tau> Y\<^sub>0 \<and> \<tau>\<^sub>0'' \<in> traceinterpol \<tau>\<^sub>0' (-{ch})" 
      using Cons by blast

    let ?\<tau>'' = "[\<rho>] \<down> (-{ch}) @ \<tau>\<^sub>0''"    
    
    have "?\<tau>'' \<in> traceinterpol \<tau> Y\<^sub>0"
    proof -
      have "?\<tau>'' \<down> Y\<^sub>0 = ([\<rho>] \<down> (-{ch} \<inter> Y\<^sub>0)) @ (\<tau>\<^sub>0'' \<down> Y\<^sub>0)" using tfilter_def by auto
      hence "?\<tau>'' \<down> Y\<^sub>0 = ([\<rho>] \<down> Y) @ (\<tau>\<^sub>0'' \<down> Y\<^sub>0)" using assms by (simp add: tfilter_def)
      hence "?\<tau>'' \<down> Y\<^sub>0 = (\<tau>\<^sub>0'' \<down> Y\<^sub>0)" using False tfilter_def by auto
      thus "?\<tau>'' \<in> traceinterpol \<tau> Y\<^sub>0" using IH tfilter_def by auto
    qed

    moreover have "?\<tau>'' \<in> traceinterpol (\<rho> # \<tau>\<^sub>0') (-{ch})"
    proof -
      have "?\<tau>'' \<down> (-{ ch }) = ([\<rho>] \<down> (-{ ch })) @ (\<tau>\<^sub>0'' \<down> (-{ ch }))" using tfilter_def by auto
      hence "?\<tau>'' \<down> (-{ ch }) = ([\<rho>] \<down> (-{ ch })) @ (\<tau>\<^sub>0' \<down> (-{ ch }))" using IH tfilter_def by force 
      thus "?\<tau>'' \<in> traceinterpol (\<rho> # \<tau>\<^sub>0') (-{ch})" by (simp add: tfilter_def)
    qed

    ultimately show "\<exists>\<tau>''. \<tau>'' \<in> traceinterpol \<tau> Y\<^sub>0 \<and> \<tau>'' \<in> traceinterpol (\<rho> # \<tau>\<^sub>0') (-{ch})" by blast
  qed
qed

definition tmerge :: "trace \<Rightarrow> trace \<Rightarrow> chan set \<Rightarrow> chan \<Rightarrow> trace"
  where "tmerge \<rho> \<tau> Y ch = (SOME \<tau>'. \<tau>' \<in> traceinterpol \<rho> (Y \<union> {ch}) \<and> \<tau>' \<in> traceinterpol \<tau> (-{ch}))"

lemma tmerge_traceinterpol_step: "\<tau> \<in> traceinterpol \<rho> Y \<Longrightarrow> ch \<notin> Y 
  \<Longrightarrow> tmerge \<rho> \<tau> Y ch \<in> traceinterpol \<rho> (Y \<union> {ch}) \<and> tmerge \<rho> \<tau> Y ch \<in> traceinterpol \<tau> (-{ch})"
proof -
  assume "\<tau> \<in> traceinterpol \<rho> Y"
  moreover assume "ch \<notin> Y"
  ultimately obtain \<tau>' where "\<tau>' \<in> traceinterpol \<rho> (Y \<union> {ch}) \<and> \<tau>' \<in> traceinterpol \<tau> (-{ch})"
    using trace_interpolation by fastforce
  thus ?thesis unfolding tmerge_def by (metis (no_types, lifting) someI_ex)
qed

lemma tfilter_cong_trans: "\<tau>\<^sub>1 \<down> C = \<tau>\<^sub>2 \<down> C \<Longrightarrow> \<tau>\<^sub>2 \<down> Y = \<tau>\<^sub>3 \<down> Y \<Longrightarrow> \<tau>\<^sub>1 \<down> (C\<inter>Y) = \<tau>\<^sub>3 \<down> (C\<inter>Y)"
  by (metis Int_ac(3) tfilter_trans)
                        
lemma tfilter_cong_trans_compl: "\<tau>\<^sub>1 \<down> (-C) = \<tau>\<^sub>2 \<down> (-C) \<Longrightarrow> \<tau>\<^sub>2 \<down> (-Y) = \<tau>\<^sub>3 \<down> (-Y) \<Longrightarrow> \<tau>\<^sub>1 \<down> (-(C\<union>Y)) = \<tau>\<^sub>3 \<down> (-(C\<union>Y))"
  using tfilter_cong_trans by fastforce

lemma tfilter_singleton_cong_trans_compl: "\<tau>\<^sub>1 \<down> (-{ch}) = \<tau>\<^sub>2 \<down> (-{ch}) \<Longrightarrow> \<tau>\<^sub>2 \<down> (-{dh}) = \<tau>\<^sub>3 \<down> (-{dh}) \<Longrightarrow> \<tau>\<^sub>1 \<down> (-{ch,dh}) = \<tau>\<^sub>3 \<down> (-{ch,dh})"
  using tfilter_cong_trans_compl[where \<tau>\<^sub>1=\<tau>\<^sub>1 and \<tau>\<^sub>2=\<tau>\<^sub>2 and \<tau>\<^sub>3=\<tau>\<^sub>3 and C="{ch}" and Y="{dh}"]
  by (simp add: insert_commute)

lemma tinterpol_singleton_trans: "\<tau>\<^sub>2 \<in> traceinterpol \<tau>\<^sub>1 (-{ch}) \<Longrightarrow> \<tau>\<^sub>3 \<in> traceinterpol \<tau>\<^sub>2 (-{dh}) \<Longrightarrow> \<tau>\<^sub>1 \<in> traceinterpol \<tau>\<^sub>3 (-{ch, dh})"
proof -
  have "\<tau>\<^sub>1 \<in> traceinterpol \<tau>\<^sub>2 (-{ch}) \<Longrightarrow> \<tau>\<^sub>2 \<in> traceinterpol \<tau>\<^sub>3 (-{dh}) \<Longrightarrow> \<tau>\<^sub>1 \<in> traceinterpol \<tau>\<^sub>3 (-{ch, dh})"
    using tfilter_singleton_cong_trans_compl by blast
  thus "\<tau>\<^sub>2 \<in> traceinterpol \<tau>\<^sub>1 (-{ch}) \<Longrightarrow> \<tau>\<^sub>3 \<in> traceinterpol \<tau>\<^sub>2 (-{dh}) \<Longrightarrow> \<tau>\<^sub>1 \<in> traceinterpol \<tau>\<^sub>3 (-{ch, dh})" by simp
qed

lemma tinterpol_trans: "\<tau>\<^sub>2 \<in> traceinterpol \<tau>\<^sub>1 (-C) \<Longrightarrow> \<tau>\<^sub>3 \<in> traceinterpol \<tau>\<^sub>2 (-{ch}) \<Longrightarrow> \<tau>\<^sub>1 \<in> traceinterpol \<tau>\<^sub>3 (-(C\<union>{ch}))"
proof - 
  have "\<tau>\<^sub>1 \<in> traceinterpol \<tau>\<^sub>2 (-C) \<Longrightarrow> \<tau>\<^sub>2 \<in> traceinterpol \<tau>\<^sub>3 (-{ch}) \<Longrightarrow> \<tau>\<^sub>1 \<in> traceinterpol \<tau>\<^sub>3 (-(C\<union>{ch}))"
    using tfilter_cong_trans_compl by blast
  thus "\<tau>\<^sub>2 \<in> traceinterpol \<tau>\<^sub>1 (-C) \<Longrightarrow> \<tau>\<^sub>3 \<in> traceinterpol \<tau>\<^sub>2 (-{ch}) \<Longrightarrow> \<tau>\<^sub>1 \<in> traceinterpol \<tau>\<^sub>3 (-(C\<union>{ch}))" by simp
qed


lemma tmerge_traceinterpol_two: "\<tau> \<in> traceinterpol \<rho> Y \<Longrightarrow> ch \<notin> Y \<Longrightarrow> dh \<notin> Y \<Longrightarrow> ch \<noteq> dh 
  \<Longrightarrow> tmerge \<rho> (tmerge \<rho> \<tau> Y ch) (Y \<union> {ch}) dh \<in> traceinterpol \<rho> (Y \<union> {ch, dh}) 
      \<and> tmerge \<rho> (tmerge \<rho> \<tau> Y ch) (Y \<union> {ch}) dh \<in> traceinterpol \<tau> (-{ch, dh})"
proof -
  assume "\<tau> \<in> traceinterpol \<rho> Y" "ch \<notin> Y" "dh \<notin> Y" "ch \<noteq> dh"
  hence "(tmerge \<rho> \<tau> Y ch) \<in> traceinterpol \<rho> (Y \<union> {ch})" and 0: "tmerge \<rho> \<tau> Y ch \<in> traceinterpol \<tau> (-{ch})"
    using tmerge_traceinterpol_step by auto
  moreover have "dh \<notin> Y \<union> {ch}" using \<open>dh \<notin> Y\<close> \<open>ch \<noteq> dh\<close> by simp
  ultimately have 1: "tmerge \<rho> (tmerge \<rho> \<tau> Y ch) (Y \<union> {ch}) dh \<in> traceinterpol \<rho> ((Y \<union> {ch}) \<union> {dh}) 
    \<and> tmerge \<rho> (tmerge \<rho> \<tau> Y ch) (Y \<union> {ch}) dh \<in> traceinterpol (tmerge \<rho> \<tau> Y ch) (-{dh})"
    using tmerge_traceinterpol_step by auto
  hence "tmerge \<rho> (tmerge \<rho> \<tau> Y ch) (Y \<union> {ch}) dh \<in> traceinterpol \<tau> (-{ch, dh})"
    using 0 tinterpol_singleton_trans[where \<tau>\<^sub>1="\<tau>" and \<tau>\<^sub>2="tmerge \<rho> \<tau> Y ch"] by fastforce
  moreover have "tmerge \<rho> (tmerge \<rho> \<tau> Y ch) (Y \<union> {ch}) dh \<in> traceinterpol \<rho> (Y \<union> {ch, dh})"
    using 1 by (metis (no_types, lifting) ext Un_commute Un_insert_left insert_is_Un)
  ultimately show ?thesis by simp
qed

fun tmerge_many :: "trace \<Rightarrow> trace \<Rightarrow> chan set \<Rightarrow> chan list \<Rightarrow> trace" 
  where
  "tmerge_many \<rho> \<tau> Y [] = \<tau>"
| "tmerge_many \<rho> \<tau> Y (ch # C) = tmerge \<rho> (tmerge_many \<rho> \<tau> Y C) (Y \<union> set C) ch"

(* lemma tmerge_traceinterpol_step: "\<tau> \<in> traceinterpol \<rho> Y \<Longrightarrow> ch \<notin> Y 
  \<Longrightarrow> tmerge \<rho> \<tau> Y ch \<in> traceinterpol \<rho> (Y \<union> {ch}) \<and> tmerge \<rho> \<tau> Y ch \<in> traceinterpol \<tau> (-{ch})" *)

lemma tmerge_traceinterpol: "\<tau> \<in> traceinterpol \<rho> Y \<Longrightarrow> Y \<inter> set C = {} \<Longrightarrow> distinct C
  \<Longrightarrow> tmerge_many \<rho> \<tau> Y C \<in> traceinterpol \<rho> (Y \<union> set C) \<and> tmerge_many \<rho> \<tau> Y C \<in> traceinterpol \<tau> (-set C)"
proof (induction C)
  case Nil
  then show ?case by simp
next
  case (Cons ch C)
  hence "Y \<inter> set C = {}" by auto
  hence "tmerge_many \<rho> \<tau> Y C \<in> traceinterpol \<rho> (Y \<union> set C)" 
    and 0: "tmerge_many \<rho> \<tau> Y C \<in> traceinterpol \<tau> (-set C)"
    using Cons by auto
  moreover have "ch \<notin> Y \<union> set C" using local.Cons(3,4) by auto
  ultimately have 1: "tmerge \<rho> (tmerge_many \<rho> \<tau> Y C) (Y \<union> set C) ch \<in> traceinterpol \<rho> ((Y \<union> set C) \<union> {ch}) 
    \<and> tmerge \<rho> (tmerge_many \<rho> \<tau> Y C) (Y \<union> set C) ch \<in> traceinterpol (tmerge_many \<rho> \<tau> Y C) (-{ch})"
    using tmerge_traceinterpol_step by simp
  hence "tmerge \<rho> (tmerge_many \<rho> \<tau> Y C) (Y \<union> set C) ch \<in> traceinterpol \<tau> (-(set C \<union> {ch}))"
    using 0 tinterpol_trans[where \<tau>\<^sub>1="\<tau>" and \<tau>\<^sub>2="tmerge_many \<rho> \<tau> Y C"] by fastforce
  thus ?case using 1 by simp
qed

definition smerge :: "state \<Rightarrow> comtar set \<Rightarrow> state"
  where "smerge \<nu> W = \<nu> \<lparr> stT := tsfilter (stT \<nu>) W \<rparr>"

definition set_to_list :: "'a set \<Rightarrow> 'a list"
  where "set_to_list s = (SOME l. set l = s \<and> distinct l)"

lemma set_set_to_list:
   "finite s \<Longrightarrow> set (set_to_list s) = s"
  unfolding set_to_list_def
  by (metis (mono_tags) finite_distinct_list some_eq_ex)

lemma set_chan_set_to_list [simp]: "set (set_to_list (C::chan set)) = C"
  apply (rule set_set_to_list) using finite_chans by simp

lemma distinct_set_chan_to_list [simp]: "distinct (set_to_list (C::chan set))"
  unfolding set_to_list_def 
  by (metis (mono_tags) finite_chans finite_distinct_list some_eq_ex)

lemma tmerge_traceinterpol0: "\<tau> \<in> traceinterpol \<rho> Y \<Longrightarrow> Y \<inter> C = {}
  \<Longrightarrow> tmerge_many \<rho> \<tau> Y (set_to_list C) \<in> traceinterpol \<rho> (Y \<union> C) \<and> tmerge_many \<rho> \<tau> Y (set_to_list C) \<in> traceinterpol \<tau> (-C)"
  using tmerge_traceinterpol[where C="set_to_list C"] by simp

lemma dingelidi:
  "\<tau> \<down> Y = \<rho> \<down> Y \<Longrightarrow> Y \<inter> C = {} \<Longrightarrow> \<tau> \<down> (Y\<union>C) = tmerge_many \<tau> \<rho> Y (set_to_list C) \<down> (Y\<union>C)"
  using tmerge_traceinterpol0 by simp




text \<open>The state set \<open>VCstateinterpol \<nu> \<omega> S\<close> interpolates between \<open>\<nu>\<close> and \<open>\<omega>\<close> according to the names
(variables and recorder-channel-pairs) in \<open>S\<close>. A state \<open>\<nu>' \<in> VCstateinterpol \<nu> \<omega> S\<close> agrees with \<open>\<nu>\<close> 
on the names in \<open>S\<close> and with \<open>\<omega>\<close> on the names not in \<open>S\<close>. In particular, for trace variable, the 
trace is interpolated according to the corresponding channel names in \<open>S\<close>, c.f. lemma \<open>trace_interpolation\<close>.\<close>

definition VCstateinterpol :: "state \<Rightarrow> state \<Rightarrow> bindr set \<Rightarrow> state set"
  where "VCstateinterpol \<nu> \<omega> S \<equiv> { \<nu>' | \<nu>'. VCagree \<nu>' \<nu> S \<and> VCagree \<nu>' \<omega> (-S) }"
                                                
lemma VCstateinterpol_empty [simp]: "VCstateinterpol \<nu> \<omega> {} = { \<omega> }"
  using VCstateinterpol_def nobinders_compl VCagree_univ by simp

definition tinterpol :: "trace \<Rightarrow> trace \<Rightarrow> chan set \<Rightarrow> chan \<Rightarrow> trace"
  where "tinterpol \<tau> \<tau>' Y ch \<equiv> SOME \<tau>''. \<tau>'' \<in> traceinterpol \<tau> Y \<and> \<tau>'' \<in> traceinterpol \<tau>' (-{ch})"

text \<open>Generalization of Lemma 11 in \<open>https://link.springer.com/chapter/10.1007/978-3-031-38499-8_6\<close>
and of Lemma 13 in \<open>https://arxiv.org/abs/2408.05012\<close>\<close>
theorem coincidence_evaluation: 
  assumes "VCagree \<omega> \<omega>' (FNF E)"
  shows "E \<omega> = E \<omega>'"
proof -                  
  have gen: "S \<subseteq> -FNF E \<Longrightarrow> (\<And>\<nu>'. \<nu>' \<in> (VCstateinterpol \<omega> \<omega>' S) \<Longrightarrow> E \<omega>' = E \<nu>')" 
    if "finite S" for S
  using that proof (induction S)
    case empty
    thus ?case by simp 
  next            
    case step: (insert x S\<^sub>0)
    hence xnew: "x \<notin> S\<^sub>0" by auto

    let ?S = "insert x S\<^sub>0"
    let ?X = "\<pi>\<^sub>V ?S" let ?Y = "\<pi>\<^sub>C ?S"
    let ?X\<^sub>0 = "\<pi>\<^sub>V S\<^sub>0" let ?Y\<^sub>0 = "\<pi>\<^sub>C S\<^sub>0" 

    fix \<nu>'
    assume stinterpol: "\<nu>' \<in> VCstateinterpol \<omega> \<omega>' ?S"     
    show "E \<omega>' = E \<nu>'"
    proof (cases x)
      case (Bv z)
  
      let ?\<nu>'' = "upds \<nu>' z (\<omega>' $$ z)"

      have origin: "VCagree ?\<nu>'' \<omega> S\<^sub>0"
      proof -
        have "VCagree \<nu>' \<omega> ?S" using stinterpol VCstateinterpol_def by auto
        hence 0: "VCagree \<nu>' \<omega> S\<^sub>0" using VCagree_antimon by blast
        have "S\<^sub>0 \<subseteq> -(\<iota>\<^sub>V {z})" using xnew Bv by simp
        hence "VCagree ?\<nu>'' \<nu>' S\<^sub>0" 
          using VCagree_antimon VCagree_sym_rel VCagree_upds sorteq_self_val by meson
        from this and 0 show "VCagree ?\<nu>'' \<omega> S\<^sub>0" by (metis VCagree_trans)
      qed

      have target: "VCagree ?\<nu>'' \<omega>' (-S\<^sub>0)"
      proof -
        have "VCagree ?\<nu>'' \<nu>' (-\<iota>\<^sub>V {z})" using VCagree_sym VCagree_upds sorteq_self_val by metis
        hence "VCagree ?\<nu>'' \<nu>' (-?S)" using Bv by auto (* -?S \<subseteq> - \<iota>\<^sub>V {z} *)
        moreover have "VCagree \<nu>' \<omega>' (-?S)" using stinterpol VCstateinterpol_def by auto
        ultimately have "VCagree ?\<nu>'' \<omega>' (-?S)" by (metis VCagree_trans)
        moreover have "-S\<^sub>0 = -?S \<union> (\<iota>\<^sub>V {z})" using xnew Bv by auto
        ultimately show "VCagree ?\<nu>'' \<omega>' (-S\<^sub>0)" using VCagree_add_var by simp
      qed
          
      have "?\<nu>'' \<in> VCstateinterpol \<omega> \<omega>' S\<^sub>0" using origin target by (simp add: VCstateinterpol_def)
      hence IH: "E ?\<nu>'' = E \<omega>'" using step by (metis insert_subset) 

      moreover have "E \<nu>' = E ?\<nu>''"
      proof -
        have "Vagree ?\<nu>'' \<nu>' (-{z})" using Vagree_sym Vagree_upds sorteq_self_val by blast
        moreover have "z \<notin> FVF E" using step.prems Bv FNF_partition by fastforce
        ultimately show ?thesis unfolding FVF_def mem_Collect_eq by simp
      qed

      ultimately show "E \<omega>' = E \<nu>'" by auto
    next
      case (Bc h ch)
      hence varsEq: "?X = ?X\<^sub>0" by auto
      have "-S\<^sub>0 = -?S \<union> {x}" using xnew by blast
      hence YzeroCompl: "-?Y\<^sub>0 = {(h, ch)} \<union> -?Y  \<and> (h, ch) \<notin> -?Y" using Bc xnew
        by (simp) (metis pi_insert(2) \<pi>\<^sub>C_compl insert_is_Un)
       
      let ?\<nu>'' = "trepv \<nu>' h (if (Tv h) \<in> -?X\<^sub>0 then 
        tinterpol ((stT \<omega>') h) ((stT \<nu>') h) ((-?Y\<^sub>0) ``{h}) ch else stT \<nu>' h)"

      have origin: "VCagree ?\<nu>'' \<omega> S\<^sub>0"
      proof -
        have "VCagree \<nu>' \<omega> ?S" using stinterpol VCstateinterpol_def by auto
        hence "VCagree \<nu>' \<omega> S\<^sub>0" using VCagree_antimon by blast
        moreover have "VCagree ?\<nu>'' \<nu>' S\<^sub>0"                                
          unfolding VCagree_def apply (rule Vagree_by_sortI) by (simp_all add: eqon_def tsfilter_def)
        ultimately show ?thesis using VCagree_trans by blast
      qed

      let ?tipol = "tinterpol (stT \<omega>' h) (stT \<nu>' h) ((-?Y\<^sub>0)``{h}) ch"
      have interpol_trace: "Tv h \<notin> ?X\<^sub>0 \<Longrightarrow> ?tipol \<in> traceinterpol (stT \<omega>' h) ((-?Y\<^sub>0)``{h}) 
        \<and> ?tipol \<in> traceinterpol (stT \<nu>' h) (-{ch})"
      proof -
        assume h: "Tv h \<notin> (\<pi>\<^sub>V S\<^sub>0)"
        
        have "VCagree \<nu>' \<omega>' (-?S)" using stinterpol VCstateinterpol_def by auto
        hence "eqon (tsfilter (stT \<nu>') (-?Y)) (tsfilter (stT \<omega>') (-?Y)) (\<pi>\<^sub>T (-?X))"
          using stinterpol by (metis VCagree_stT_E \<pi>\<^sub>C_compl \<pi>\<^sub>V_compl)
        hence "(stT \<nu>') h \<in> traceinterpol ((stT \<omega>') h) ((-?Y)``{h})" 
          by (simp add: eqon_def h varsEq tsfilter_def)
        
        moreover have "(-?Y\<^sub>0)``{h} = {ch} \<union> (-?Y)``{h} \<and> ch \<notin> (-?Y)``{h}" using YzeroCompl by auto
        ultimately have "\<exists>\<tau>''. \<tau>'' \<in> traceinterpol (stT \<omega>' h) ((-(\<pi>\<^sub>C S\<^sub>0))``{h}) 
          \<and> \<tau>'' \<in> traceinterpol (stT \<nu>' h) (-{ch})" 
          using trace_interpolation YzeroCompl by auto
        thus "?tipol \<in> traceinterpol (stT \<omega>' h) ((-?Y\<^sub>0)``{h}) 
          \<and> ?tipol \<in> traceinterpol (stT \<nu>' h) (-{ch})" 
          unfolding tinterpol_def by (metis (no_types, lifting) someI)
      qed

      have target: "VCagree ?\<nu>'' \<omega>' (-S\<^sub>0)"
      unfolding VCagree_def proof (rule Vagree_by_sortI, goal_cases stR stT)
        case stR
        have "eqon (stR \<nu>') (stR \<omega>') (\<pi>\<^sub>R (-?X))" 
          using stinterpol unfolding VCstateinterpol_def using VCagree_stR_E by fastforce
        then show ?case unfolding eqon_def using varsEq stR_sfilter by simp
      next
        case stT
        have "eqon (tsfilter (stT \<nu>') (-?Y)) (tsfilter (stT \<omega>') (-?Y)) (\<pi>\<^sub>T (-?X))" 
          using stinterpol unfolding VCstateinterpol_def using VCagree_stT_E by fastforce
        hence "eqon (tsfilter (stT \<nu>') (-?Y)) (tsfilter (stT \<omega>') (-?Y)) (\<pi>\<^sub>T (-?X\<^sub>0))" 
          using varsEq by simp
        hence "eqon (tsfilter (stT ?\<nu>'') (-?Y\<^sub>0)) (tsfilter (stT \<omega>') (-?Y\<^sub>0)) (\<pi>\<^sub>T (-?X\<^sub>0) \<inter> -{h})"
          unfolding eqon_def using YzeroCompl tsfilter_access tsfilter_insert_access_other by auto
        moreover have "eqon (tsfilter (stT ?\<nu>'') (-?Y\<^sub>0)) (tsfilter (stT \<omega>') (-?Y\<^sub>0)) (\<pi>\<^sub>T (-?X\<^sub>0) \<inter> {h})"
          apply (simp add: eqon_def tsfilter_def) using interpol_trace by auto
        ultimately show ?case unfolding eqon_def by auto
      qed

      have "?\<nu>'' \<in> VCstateinterpol \<omega> \<omega>' S\<^sub>0" using VCstateinterpol_def origin target by blast
      hence IH: "E ?\<nu>'' = E \<omega>'" 
        by (metis (no_types, lifting) step.IH step.prems(1) insert_subset)

      moreover have "E \<nu>' = E ?\<nu>''"
      proof -
        have "(h, ch) \<notin> CNF E" using step.prems Bc FNF_partition by fastforce 
        hence 0: "\<not>(sfilter ?\<nu>'' (-{(h, ch)}) = sfilter \<nu>' (-{(h, ch)}) 
          \<and> \<not>(E ?\<nu>'' = E \<nu>'))" using CNF_def by blast

        have 1: "\<And>ha. (- {(ha, ch)}) `` {ha} = -{ch}" by auto
        have "stT (sfilter \<nu>' (-{(h, ch)})) = stT (sfilter ?\<nu>'' (-{(h, ch)}))"
          apply (rule stT_sfilterI)
          apply (simp add: tsfilter_def 1)
          using interpol_trace by force
          
        hence "sfilter \<nu>' (-{(h, ch)}) = sfilter ?\<nu>'' (-{(h, ch)})" by simp

        thus ?thesis using 0 by presburger
      qed

      ultimately show "E \<omega>' = E \<nu>'" by auto
    qed
  qed

  have "\<omega> \<in> VCstateinterpol \<omega> \<omega>' (-FNF E)" using assms VCagree_def VCstateinterpol_def by simp
  moreover have "finite (-FNF E)" using finite_bindables by simp
  ultimately show ?thesis by (metis gen order_refl) 
qed

theorem FVF_CNF_least_sat_coincidence:
  assumes "\<And>\<omega> \<omega>'. Vagree (sfilter \<omega> Y) (sfilter \<omega>' Y) X \<Longrightarrow> E \<omega> = E \<omega>'"
  shows "Y \<supseteq> CNF E \<and> X \<supseteq> FVF E"
proof (rule ccontr)
  assume "\<not> (Y \<supseteq> CNF E \<and> X \<supseteq> FVF E)"                               
  then obtain h ch z where 0: "(h, ch) \<notin> Y \<and> (h, ch) \<in> CNF E \<or> z \<notin> X \<and> z \<in> FVF E" by auto
  thus False
  proof (cases "(h, ch) \<notin> Y \<and> (h, ch) \<in> CNF E")
    case True
    then obtain \<nu> \<omega> where 0: "sfilter \<nu> (-{(h, ch)}) = sfilter \<omega> (-{(h, ch)}) \<and> \<not>(E \<nu> = E \<omega>)"
      using CNF_def by blast
    hence "Vagree (sfilter \<nu> Y) (sfilter \<omega> Y) X"
      by (metis True Vagree_refl sfilter_antimon subset_Compl_singleton)
    then show ?thesis using assms 0 by simp
  next
    case False
    hence fve: "z \<notin> X \<and> z \<in> FVF E" using 0 by auto
    then obtain \<nu> \<omega> where 0: "Vagree \<nu> \<omega> (-{z}) \<and> \<not>(E \<nu> = E \<omega>)"
      using FVF_def by blast
    hence "Vagree (sfilter \<nu> Y) (sfilter \<omega> Y) X"
      by (meson Vagree_antimon Vagree_sfilter_cong fve subset_Compl_singleton)
    then show ?thesis using assms 0 by simp
  qed
qed



subsection \<open>Coincidence for Denotations\<close>

text \<open>The state \<open>Vstateinterpol \<nu> \<omega> S\<close> interpolates between \<open>\<nu>\<close> and \<open>\<omega>\<close> that is, \<open>\<nu>\<close> on \<open>S\<close> and \<open>\<omega>\<close> 
elsewhere. Note that \<open>Vstateinterpol \<nu> \<omega> S\<close> is always a singleton but defining it as a set via
Vagree suffices and aligns better with the assumption of theorem \<open>coincidence_chp\<close>.\<close>

fun Vstateinterpol:: "state \<Rightarrow> state \<Rightarrow> variable set \<Rightarrow> state set"
  where "Vstateinterpol \<nu> \<omega> S = { \<nu>' | \<nu>'. Vagree \<nu>' \<nu> (-S) \<and> Vagree \<nu>' \<omega> S }"

text \<open>Lemma 12 in \<open>https://link.springer.com/chapter/10.1007/978-3-031-38499-8_6\<close>\<close>
theorem coincidence_denotation: "X \<supseteq> FVD D \<Longrightarrow> Vagree \<nu> \<nu>' X \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> D 
    \<Longrightarrow> \<exists>\<omega>'. (\<nu>', \<tau>, \<omega>') \<in> D \<and> Vagreebot \<omega> \<omega>' X"
proof -
  assume b: "X \<supseteq> FVD D"
  assume a: "Vagree \<nu> \<nu>' X"
  assume c: "(\<nu>, \<tau>, \<omega>) \<in> D"
  have gen: "S \<subseteq> (-FVD D) \<Longrightarrow> (\<And>\<nu>\<^sub>S. \<nu>\<^sub>S \<in> (Vstateinterpol \<nu> \<nu>' S)
    \<Longrightarrow> (\<exists>\<omega>\<^sub>S. (\<nu>\<^sub>S, \<tau>, \<omega>\<^sub>S) \<in> D \<and> Vagreebot \<omega> \<omega>\<^sub>S (-S)))" if "finite S" for S
    using that 
  proof (induction S)
    case empty
    fix \<nu>\<^sub>S
    assume "\<nu>\<^sub>S \<in> Vstateinterpol \<nu> \<nu>' {}"
    hence "\<nu>\<^sub>S = \<nu>" using Vagree_univ by auto
    hence "(\<nu>\<^sub>S, \<tau>, \<omega>) \<in> D \<and> Vagreebot \<omega> \<omega> (-X) \<and> \<tau> = \<tau>" 
      by (metis Vagree_refl Vagreebot_def c reachedstate.exhaust)
    thus "\<exists>\<omega>\<^sub>S. (\<nu>\<^sub>S, \<tau>, \<omega>\<^sub>S) \<in> D \<and> Vagreebot \<omega> \<omega>\<^sub>S (-{})" 
      using \<open>\<nu>\<^sub>S = \<nu>\<close> Vagree_univ Vagreebot_def by auto
  next
    case step: (insert z S\<^sub>0)

    fix \<nu>\<^sub>S
    assume 0: "\<nu>\<^sub>S \<in> Vstateinterpol \<nu> \<nu>' (insert z S\<^sub>0)"

    let ?\<nu>'' = "upds \<nu>\<^sub>S z (\<nu> $$ z)"

    have "Vagree ?\<nu>'' \<nu>' S\<^sub>0"
    proof -
      have "Vagree \<nu>\<^sub>S \<nu>' (insert z S\<^sub>0)" using 0 by auto
      hence "Vagree \<nu>\<^sub>S \<nu>' S\<^sub>0" using 0 Vagree_antimon by blast
      thus ?thesis by (simp add: Vagree_def step.hyps(2))
    qed

    moreover have "Vagree ?\<nu>'' \<nu> (-S\<^sub>0)"
    proof -
      have "Vagree \<nu>\<^sub>S \<nu> (-(insert z S\<^sub>0))" using 0 by auto
      hence "Vagree ?\<nu>'' \<nu> (-(insert z S\<^sub>0))" by (simp add: Vagree_def)
      moreover have "Vagree ?\<nu>'' \<nu> {z}" by (simp add: Vagree_def)
      ultimately show ?thesis using Vagree_def by fastforce
    qed

    ultimately have "?\<nu>'' \<in> Vstateinterpol \<nu> \<nu>' S\<^sub>0" by auto
    moreover have "S\<^sub>0 \<subseteq> -FVD D" using step.prems(1) by auto
    ultimately have "\<exists>\<omega>''. (?\<nu>'', \<tau>, \<omega>'') \<in> D \<and> Vagreebot \<omega> \<omega>'' (-S\<^sub>0)" 
      using step.IH by presburger
    then obtain \<omega>'' where IH: "(?\<nu>'', \<tau>, \<omega>'') \<in> D \<and> Vagreebot \<omega> \<omega>'' (-S\<^sub>0)" by auto

    moreover have "Vagree ?\<nu>'' \<nu>\<^sub>S (-{z})" using Vagree_sym Vagree_upds sorteq_self_val by blast
    moreover have "\<forall>\<nu>\<^sub>1 \<nu>\<^sub>2 \<omega>\<^sub>1. \<not>((Vagree \<nu>\<^sub>1 \<nu>\<^sub>2 (-{z})) \<and> (\<nu>\<^sub>1, \<tau>, \<omega>\<^sub>1) \<in> D) \<or>
        (\<exists>\<omega>\<^sub>2. (\<nu>\<^sub>2, \<tau>, \<omega>\<^sub>2) \<in> D \<and> (Vagreebot \<omega>\<^sub>1 \<omega>\<^sub>2 (-{z})))" 
      using FVD_def step.prems(1) by auto
    ultimately have "(\<exists>\<omega>\<^sub>2. (\<nu>\<^sub>S, \<tau>, \<omega>\<^sub>2) \<in> D \<and> (Vagreebot \<omega>'' \<omega>\<^sub>2 (-{z})))" by blast
    then obtain \<omega>\<^sub>S where thisstep: "(\<nu>\<^sub>S, \<tau>, \<omega>\<^sub>S) \<in> D \<and> (Vagreebot \<omega>'' \<omega>\<^sub>S (-{z}))" by auto

    hence "Vagreebot \<omega> \<omega>\<^sub>S (-S\<^sub>0 \<inter> -{z})" using IH Vagreebot_trans by blast
    hence "Vagreebot \<omega> \<omega>\<^sub>S (-insert z S\<^sub>0)" by (metis Compl_Un inf_sup_aci(1) insert_is_Un)  
    hence "(\<nu>\<^sub>S, \<tau>, \<omega>\<^sub>S) \<in> D \<and> (Vagreebot \<omega> \<omega>\<^sub>S (-(insert z S\<^sub>0)))" using IH thisstep by meson
    thus "\<exists>\<omega>\<^sub>S. (\<nu>\<^sub>S, \<tau>, \<omega>\<^sub>S) \<in> D \<and> Vagreebot \<omega> \<omega>\<^sub>S (-(insert z S\<^sub>0))" by auto
  qed

  let ?S = "-FVD D"
  
  have "-X \<subseteq> -FVD D" using b by auto
  moreover have isX: "\<nu>' \<in> Vstateinterpol \<nu> \<nu>' (-X)" using a by (auto simp add: Vagree_sym)
  moreover have fin: "finite (-X)" using allvars_finite rev_finite_subset by fastforce
  ultimately show "\<exists>\<omega>\<^sub>S. (\<nu>', \<tau>, \<omega>\<^sub>S) \<in> D \<and> Vagreebot \<omega> \<omega>\<^sub>S X"
    by (metis double_complement gen)
qed

theorem FVD_least_sat_coincidence:
  assumes "\<And>X I \<nu> \<nu>' \<tau> \<omega> \<omega>'. X \<supseteq> X\<^sub>0 \<Longrightarrow> Vagree \<nu> \<nu>' X \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> D
    \<Longrightarrow> \<exists>\<omega>'. (\<nu>', \<tau>, \<omega>') \<in> D \<and> Vagreebot \<omega> \<omega>' X"
  shows "X\<^sub>0 \<supseteq> FVD D"
proof (rule ccontr)
  assume "\<not> X\<^sub>0 \<supseteq> FVD D"                               
  then obtain z where 0: "z \<notin> X\<^sub>0 \<and> z \<in> FVD D" by auto
  then obtain \<nu>\<^sub>1 \<nu>\<^sub>2 \<tau>\<^sub>1 \<omega>\<^sub>1 where 1: "Vagree \<nu>\<^sub>1 \<nu>\<^sub>2 (-{z}) \<and> (\<nu>\<^sub>1, \<tau>\<^sub>1, \<omega>\<^sub>1) \<in> D 
    \<and> \<not>(\<exists>\<tau>\<^sub>2 \<omega>\<^sub>2. (\<nu>\<^sub>2, \<tau>\<^sub>2, \<omega>\<^sub>2) \<in> D \<and> \<tau>\<^sub>1 = \<tau>\<^sub>2 \<and> (Vagreebot \<omega>\<^sub>1 \<omega>\<^sub>2 (-{z})))"
    unfolding FVD_def by blast
  hence "-{z} \<supseteq> X\<^sub>0" using 0 by blast
  thus False using 1 assms by blast
qed



    
section \<open>Least Static Semantics\<close>

subsection \<open>Definition of the Least Static Semantics\<close>

text \<open>The least static semantics is computed relative to an interpretation J of the spaces occurring
in the respective expression, because otherwise the static semantics of a program symbol restricted
to a space would be \<close>

text \<open>Channel names denoted by the space \<open>Y\<close>\<close>
definition CNC :: "binterp \<Rightarrow> cspace \<Rightarrow> chan set"
  where "CNC J Y = cspace_sem J Y"

text \<open>Variables denoted by the space \<open>Z\<close>\<close>
definition FVV :: "binterp \<Rightarrow> vspace \<Rightarrow> variable set"
  where "FVV J Z = vspace_sem J Z"

definition CNV :: "binterp \<Rightarrow> vspace \<Rightarrow> comtar set"
  where "CNV J Z = \<pi>\<^sub>T (vspace_sem J Z) \<times> \<Omega>"

definition FNV :: "binterp \<Rightarrow> vspace \<Rightarrow> bindr set"
  where "FNV J Z = \<iota>\<^sub>V (FVV J Z) \<union> \<iota>\<^sub>C (CNV J Z)"

text \<open>Free names of the expression \<open>e\<close>\<close>
definition FNE :: "binterp \<Rightarrow> ('a::expr) \<Rightarrow> bindr set"
  where "FNE J e = {x. \<exists>I. J = \<pi>\<^sub>I I \<and> (\<exists>\<nu>.\<exists>\<omega>. VCagree \<nu> \<omega> (-{x}) 
    \<and> \<not>(expr_sem I e \<nu> = expr_sem I e \<omega>))}"

text \<open>Free variables of the program \<open>\<alpha>\<close>\<close>
definition FVP :: "binterp \<Rightarrow> chp \<Rightarrow> variable set"
  where "FVP J \<alpha> = {z. \<exists>I. J = \<pi>\<^sub>I I \<and> (\<exists>\<nu>\<^sub>1 \<nu>\<^sub>2 \<tau>\<^sub>1 \<omega>\<^sub>1. (Vagree \<nu>\<^sub>1 \<nu>\<^sub>2 (-{z})) \<and> (\<nu>\<^sub>1, \<tau>\<^sub>1, \<omega>\<^sub>1) \<in> chp_sem I \<alpha> 
    \<and> \<not>(\<exists>\<tau>\<^sub>2 \<omega>\<^sub>2. (\<nu>\<^sub>2, \<tau>\<^sub>2, \<omega>\<^sub>2) \<in> chp_sem I \<alpha> \<and> \<tau>\<^sub>1 = \<tau>\<^sub>2 \<and> (Vagreebot \<omega>\<^sub>1 \<omega>\<^sub>2 (-{z}))))}"

text \<open>Names bound by the program \<open>\<alpha>\<close> from the initial to some reachable world\<close>
definition BNP :: "binterp \<Rightarrow> chp \<Rightarrow> bindr set"
  where "BNP J \<alpha> = {b. \<exists>I. J = \<pi>\<^sub>I I \<and> (\<exists>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> 
    \<and> \<not>(VCagree \<nu> ((\<omega> \<squnion> \<nu>) @@ \<tau>) (bclose b)))}"



paragraph \<open>Subsets of the Least Static Semantics\<close>


text \<open>The following aspects of the static semantics are covered by the least static semantics above.
They are included for reference and because they are sometimes useful in proofs.\<close>

text \<open>Free variables of the expression \<open>e\<close>\<close>
definition FVE :: "binterp \<Rightarrow> ('a::expr) \<Rightarrow> variable set"
  where "FVE J e = {x. \<exists>I. J = \<pi>\<^sub>I I \<and> (\<exists>\<nu>.\<exists>\<omega>. Vagree \<nu> \<omega> (-{x}) 
    \<and> \<not>(expr_sem I e \<nu> = expr_sem I e \<omega>))}"

text \<open>Channels accessed per trace variable by the expression \<open>e\<close>\<close>
definition CNE :: "binterp \<Rightarrow> ('a::expr) \<Rightarrow> comtar set"
  where "CNE J e = { (h, ch). \<exists>I. J = \<pi>\<^sub>I I \<and> (\<exists>\<nu>.\<exists>\<omega>. sfilter \<nu> (-{(h, ch)}) = sfilter \<omega> (-{(h, ch)}) 
    \<and> \<not>(expr_sem I e \<nu> = expr_sem I e \<omega>))}"

text \<open>Variables bound by the program \<open>\<alpha>\<close> from the initial to the final world\<close>
definition BVP :: "binterp \<Rightarrow> chp \<Rightarrow> variable set"
  where "BVP J \<alpha> = {z. \<exists>I. J = \<pi>\<^sub>I I \<and> (\<exists>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<and> ((\<omega> \<squnion> \<nu>) @@ \<tau>) $$ z \<noteq> \<nu> $$ z)}"

text \<open>Channels bound per recorder (trace) variable by the program \<open>\<alpha>\<close>\<close>
definition CNP :: "binterp \<Rightarrow> chp \<Rightarrow> comtar set"
  where "CNP J \<alpha> = {(h, ch). \<exists>I. J = \<pi>\<^sub>I I \<and> (\<exists>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<and> byrec \<tau> h \<down> {ch} \<noteq> [])}"

text \<open>Variables bound by the program \<open>\<alpha>\<close> from the initial to the final state\<close>
definition DiffP :: "binterp \<Rightarrow> chp \<Rightarrow> variable set"
  where "DiffP J \<alpha> = {z. \<exists>I. J = \<pi>\<^sub>I I \<and> (\<exists>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha> \<and> \<omega> $$ z \<noteq> \<nu> $$ z)}"

text \<open>Recorder variables bound by the program \<open>\<alpha>\<close>\<close>
definition RecP :: "binterp \<Rightarrow> chp \<Rightarrow> tvar set"
  where "RecP J \<alpha> = {h. \<exists>I. J = \<pi>\<^sub>I I \<and> (\<exists>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<and> byrec \<tau> h \<noteq> [])}"



paragraph \<open>Free Names of Argument Lists\<close>

text \<open>Free names of the expression list \<open>\<Theta>\<close>\<close>
definition FNArgs :: "binterp \<Rightarrow> ('a::expr) list \<Rightarrow> bindr set"
  where "FNArgs J \<Theta> = (\<Union> { FNE J e | e. e \<in> set \<Theta>})"

definition FVArgs :: "binterp \<Rightarrow> ('a::expr) list \<Rightarrow> variable set"
  where "FVArgs J \<Theta> = (\<Union> { FVE J e | e. e \<in> set \<Theta>})"

definition CNArgs :: "binterp \<Rightarrow> ('a::expr) list \<Rightarrow> comtar set"
  where "CNArgs J \<Theta> = (\<Union> { CNE J e | e. e \<in> set \<Theta>})"

text \<open>The set of bound variables as defined in previous work. This set does not cover recorder
variables that do only change in runs from an initial state to an intermediate world.\<close>

definition BVP_old :: "binterp \<Rightarrow> chp \<Rightarrow> variable set"
  where "BVP_old J \<alpha> = {z. \<exists>I. J = \<pi>\<^sub>I I \<and> (\<exists>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha> \<and> (\<omega> @@ \<tau>) $$ z \<noteq> \<nu> $$ z)}"

lemma FNArgs_empty [simp]: "FNArgs J [] = {}" by (simp add: FNArgs_def)
lemma FVArgs_empty [simp]: "FVArgs J [] = {}" by (simp add: FVArgs_def)
lemma CNArgs_empty [simp]: "CNArgs J [] = {}" by (simp add: CNArgs_def)

lemma FNArgs_Cons [simp]: "FNArgs J (e # \<Theta>) = FNE J e \<union> FNArgs J \<Theta>"
  unfolding FNArgs_def by auto

lemma FVArgs_Cons [simp]: "FVArgs J (e # \<Theta>) = FVE J e \<union> FVArgs J \<Theta>"
  unfolding FVArgs_def by auto

lemma CNArgs_Cons [simp]: "CNArgs J (e # \<Theta>) = CNE J e \<union> CNArgs J \<Theta>"
  unfolding CNArgs_def by auto



paragraph \<open>Embedding into the Denotational Static Semantics\<close>

lemma FNE_FNF: "FNE J e = \<Union> { FNF (expr_sem I e) | I. J = \<pi>\<^sub>I I}"
  unfolding FNE_def FNF_def by blast

lemma FVE_FVF: "FVE J e = \<Union> { FVF (expr_sem I e) | I. J = \<pi>\<^sub>I I}"
  unfolding FVE_def FVF_def by blast

lemma CNE_CNF: "CNE J e = \<Union> { CNF (expr_sem I e) | I. J = \<pi>\<^sub>I I}"
  unfolding CNE_def CNF_def by blast

lemma FNE_partition: "FNE J e = \<iota>\<^sub>V (FVE J e) \<union> \<iota>\<^sub>C (CNE J e)"
  apply (simp add: FNE_FNF FVE_FVF CNE_CNF)
  using FNF_partition by blast

lemma FNArgs_partition: "FNArgs J \<Theta> = \<iota>\<^sub>V (FVArgs J \<Theta>) \<union> \<iota>\<^sub>C (CNArgs J \<Theta>)"
  apply (induction \<Theta>)
   apply (simp add: FNArgs_def FVArgs_def CNArgs_def)
  apply (simp add: FNE_partition) by blast

lemma FVP_FVD: "FVP J \<alpha> = \<Union> { FVD (chp_sem I \<alpha>) | I. J = \<pi>\<^sub>I I}"
  unfolding FVP_def FVD_def by blast

lemma BNP_BND: "BNP J \<alpha> = \<Union> { BND (chp_sem I \<alpha>) | I. J = \<pi>\<^sub>I I }"
  unfolding BNP_def BND_def by blast

lemma BVP_BVD: "BVP J \<alpha> = \<Union> { BVD (chp_sem I \<alpha>) | I. J = \<pi>\<^sub>I I }"
  unfolding BVP_def BVD_def by blast

lemma CNP_CND: "CNP J \<alpha> = \<Union> { CND (chp_sem I \<alpha>) | I. J = \<pi>\<^sub>I I }"
  unfolding CNP_def CND_def by blast


lemma DiffD_chp_sem [simp]: "DiffD (chp_sem I \<alpha>) \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R"
proof -
  have "\<And>x. \<exists>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha> \<and> \<omega> $$ x \<noteq> \<nu> $$ x \<Longrightarrow> x \<in> -\<iota>\<^sub>T \<V>\<^sub>T"
    using chps_do_not_bind_tvars by (force simp only: Vagree_def)
  thus ?thesis by (auto simp add: DiffD_def)
qed

lemma BNP_partition: "BNP J \<alpha> = \<iota>\<^sub>V (BVP J \<alpha>) \<union> \<iota>\<^sub>C (CNP J \<alpha>)"
  apply (simp add: BNP_BND BVP_BVD CNP_CND)
  using BND_partition by auto

lemma DiffP_DiffD: "DiffP J \<alpha> = \<Union> { DiffD (chp_sem I \<alpha>) | I. J = \<pi>\<^sub>I I }"
  unfolding DiffP_def DiffD_def by blast



paragraph \<open>Misc Observations\<close>

lemma reach_stT [simp]: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> stT (\<omega> \<squnion> \<nu>) = stT \<nu>"
  using DiffD_reach_stT DiffD_chp_sem by blast

lemma RecP_Domain_CNP: "RecP J \<alpha> = Domain (CNP J \<alpha>)"
  unfolding RecP_def CNP_def
  apply (rule; rule)
   apply simp_all
   apply (metis tfilter_allchans tfilter_emptyI)
  by fastforce

lemma RecP_in_BVP: "RecP J \<alpha> = \<pi>\<^sub>T (BVP J \<alpha>)"
  by (fastforce simp add: RecP_def BVP_def pi_tvars_def stT_sttconc_dist_access)

lemma Range_CNP: "Range (CNP J \<alpha>) = {ch. \<exists>I. J = \<pi>\<^sub>I I \<and> (\<exists>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<and> \<tau> \<down> {ch} \<noteq> [])}"
  unfolding CNP_def
  apply (rule; rule)
   apply simp_all
  using byrec_in_empty_filter_empty apply blast
  by (metis byrec_hd_in byrec_tfilter_commute neq_Nil_conv)

definition RecP_trecs :: "binterp \<Rightarrow> chp \<Rightarrow> tvar set" 
  where "RecP_trecs J \<alpha> = {h | h. \<exists>I. J = \<pi>\<^sub>I I \<and> (\<exists>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<and> h \<in> trecs \<tau>)}"


lemma RecP_trecs: "Domain (CNP J \<alpha>) = RecP_trecs J \<alpha>"
  using RecP_Domain_CNP by (simp add: RecP_trecs_def trecs_equiv_byrec RecP_def)

lemma RecP_trecs_RecP: "RecP_trecs J \<alpha> = RecP J \<alpha>" using RecP_trecs RecP_Domain_CNP by simp

lemma nochans_empty_trace0: "Range (CND D) \<subseteq> {} \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> D \<Longrightarrow> \<tau> \<down> \<Omega> = []"
  apply (rule tfilter_emptyI)
  unfolding CND_def apply simp
  by (metis byrec_dist_cons byrec_tfilter_commute neq_Nil_conv)

lemma CND_empty_no_com: "Range (CND D) \<subseteq> {} \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> D \<Longrightarrow> \<tau> = []"
  using nochans_empty_trace0 by simp

lemma CNP_empty_no_com: "CNP (\<pi>\<^sub>I I) \<alpha> \<subseteq> {} \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> (chp_sem I \<alpha>) \<Longrightarrow> \<tau> = []"
  using CND_empty_no_com CNP_CND by blast

lemma CNF_recorders_subseteq_FVF: "\<iota>\<^sub>T (Domain (CNF E)) \<subseteq> FVF E"
  unfolding iota_tvars_def CNF_def FVF_def
  using sfilter_singleton_compl_Vagree by blast

lemma VCagree_FNArgs_Cons: "VCagree \<nu> \<omega> (FNArgs J (e # \<Theta>)) \<Longrightarrow> (VCagree \<nu> \<omega> (FNE J e) \<and> VCagree \<nu> \<omega> (FNArgs J \<Theta>))"
  unfolding FNArgs_Cons using VCagree_union_rev by blast



paragraph \<open>Simple Observations\<close>

(* The fact that this is a simp lemma makes BVP_pre disappear in proofs *) 
lemma BVP_pre_BVP [simp]: "BVP_pre J \<alpha> = BVP J \<alpha>"
  unfolding BVP_def by (simp add: BVP_pre.simps)

lemma chp_sem_par_BVP_D [dest]: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I (\<alpha> par \<beta>) \<Longrightarrow> (\<exists>\<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta>. 
    (\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha>), \<omega>\<^sub>\<alpha>) \<in> chp_sem I \<alpha> \<and> (\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<beta>), \<omega>\<^sub>\<beta>) \<in> chp_sem I \<beta> \<and>
    (Vagreebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> \<V>\<^sub>\<mu>) \<and> (\<omega> = lmergebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> (BVP (\<pi>\<^sub>I I) \<alpha>)) \<and> \<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha> \<union> CN (\<pi>\<^sub>I I) \<beta>) = \<tau>)"
  using BVP_pre_BVP by auto

lemma chp_sem_par_BVP_I [intro]: "(\<exists>\<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta>. 
    (\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha>), \<omega>\<^sub>\<alpha>) \<in> chp_sem I \<alpha> \<and> (\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<beta>), \<omega>\<^sub>\<beta>) \<in> chp_sem I \<beta> \<and>
    (Vagreebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> \<V>\<^sub>\<mu>) \<and> (\<omega> = lmergebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> (BVP (\<pi>\<^sub>I I) \<alpha>)) \<and> \<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha> \<union> CN (\<pi>\<^sub>I I) \<beta>) = \<tau>)
    \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> chp_sem I (\<alpha> par \<beta>)"
  using BVP_pre_BVP by auto

lemma chp_sem_par_fin [dest]: "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I (\<alpha> par \<beta>) \<Longrightarrow> (\<exists>\<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta>. 
    (\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha>), Fin \<omega>\<^sub>\<alpha>) \<in> chp_sem I \<alpha> \<and> (\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<beta>), Fin \<omega>\<^sub>\<beta>) \<in> chp_sem I \<beta> \<and>
    (Vagree \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> \<V>\<^sub>\<mu>) \<and> (\<omega> = lmerge \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> (BVP (\<pi>\<^sub>I I) \<alpha>)) \<and> \<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha> \<union> CN (\<pi>\<^sub>I I) \<beta>) = \<tau>)"
  apply simp
  using Vagreebot_only_Fin[where X=\<open>\<V>\<^sub>\<mu>\<close>] lmergebot_fin lmergebot_Exists_Fin by blast

lemma BVP_elem:"(z\<in>BVP J \<alpha>) = (\<exists>I \<nu> \<tau> \<omega>. J = \<pi>\<^sub>I I \<and> (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<and> ((\<omega> \<squnion> \<nu>) @@ \<tau>) $$ z \<noteq> \<nu> $$ z)"
  unfolding BVP_def by simp


lemma FNE_RArg [simp]: "FNE J (RArg \<theta>) = FNE J \<theta>" by (simp add: FNE_def)
lemma FNE_TArg [simp]: "FNE J (TArg te) = FNE J te" by (simp add: FNE_def)











subsection \<open>Coincidence Properties\<close>

paragraph \<open>Coincidence for Expressions\<close>

theorem coincidence_expr: 
  assumes "VCagree \<omega> \<omega>' (FNE (\<pi>\<^sub>I I) e)"
  shows "expr_sem I e \<omega> = expr_sem I e \<omega>'"
proof -
  have "FNF (expr_sem I e) \<subseteq> (FNE (\<pi>\<^sub>I I) e)" using FNE_FNF by blast
  thus ?thesis using coincidence_evaluation assms VCagree_antimon by metis
qed

theorem FVE_CNE_least_sat_coincidence:
  assumes "\<And>I \<omega> \<omega>'. Vagree (sfilter \<omega> Y) (sfilter \<omega>' Y) X \<Longrightarrow> expr_sem I e \<omega> = expr_sem I e \<omega>'"
  shows "Y \<supseteq> CNE J e \<and> X \<supseteq> FVE J e"
proof -
  have "\<And>I. Y \<supseteq> CNF (expr_sem I e) \<and> X \<supseteq> FVF (expr_sem I e)"
    using assms FVF_CNF_least_sat_coincidence by blast
  thus "Y \<supseteq> CNE J e \<and> X \<supseteq> FVE J e" unfolding FVE_FVF CNE_CNF by blast
qed

corollary coincidence_rtrm: "VCagree \<nu> \<omega> (FNE (\<pi>\<^sub>I I) \<theta>) \<Longrightarrow> rtrm_sem I \<theta> \<nu> = rtrm_sem I \<theta> \<omega>"
  by (metis coincidence_expr evals.inject(1) expr_sem_rtrm_def)

corollary coincidence_rtrm_FVE: "Vagree \<nu> \<omega> (FVE (\<pi>\<^sub>I I) \<theta>) \<Longrightarrow> rtrm_sem I \<theta> \<nu> = rtrm_sem I \<theta> \<omega>"
  using coincidence_rtrm by (simp add: VCagree_def FNE_partition Vagree_sfilter_cong)

corollary coincidence_ttrm: "VCagree \<nu> \<omega> (FNE (\<pi>\<^sub>I I) te) \<Longrightarrow> ttrm_sem I te \<nu> = ttrm_sem I te \<omega>"
  by (metis coincidence_expr evals.inject(2) expr_sem_ttrm_def)

corollary coincidence_ttrm_FVE: "Vagree \<nu> \<omega> (FVE (\<pi>\<^sub>I I) te) \<Longrightarrow> ttrm_sem I te \<nu> = ttrm_sem I te \<omega>"
  using coincidence_ttrm by (simp add: VCagree_def FNE_partition Vagree_sfilter_cong)

corollary coincidence_arg: "VCagree \<nu> \<omega> (FNE (\<pi>\<^sub>I I) e) \<Longrightarrow> arg_sem I e \<nu> = arg_sem I e \<omega>"
  apply (cases e)
  using coincidence_rtrm coincidence_ttrm by simp_all
                                  
corollary coincidence_args: "VCagree \<nu> \<omega> (FNArgs (\<pi>\<^sub>I I) \<Theta>) \<Longrightarrow> args_sem I \<Theta> \<nu> = args_sem I \<Theta> \<omega>"
  apply (induction \<Theta>)
  by (simp_all add: args_sem_def coincidence_arg) 

corollary coincidence_args_FVArgs: "Vagree \<nu> \<omega> (FVArgs (\<pi>\<^sub>I I) \<Theta>) \<Longrightarrow> args_sem I \<Theta> \<nu> = args_sem I \<Theta> \<omega>"
  using coincidence_args by (simp add: VCagree_def FNArgs_partition Vagree_sfilter_cong) 

corollary coincidence_fml: "VCagree \<nu> \<omega> (FNE (\<pi>\<^sub>I I) \<phi>) \<Longrightarrow> (\<nu> \<in> fml_sem I \<phi>) = (\<omega> \<in> fml_sem I \<phi>)"
  by (metis coincidence_expr evals.inject(3) expr_sem_fml_def)

corollary coincidence_fml_FVE: "Vagree \<nu> \<omega> (FVE (\<pi>\<^sub>I I) \<phi>) \<Longrightarrow> (\<nu> \<in> fml_sem I \<phi>) = (\<omega> \<in> fml_sem I \<phi>)"
  using coincidence_fml by (simp add: VCagree_def FNE_partition Vagree_sfilter_cong) 



paragraph \<open>Alternative Characterization of Interpretations\<close>

corollary is_pinterp_alt: "is_pinterp I = (\<forall>\<nu> \<omega> Z. Vagree \<nu> \<omega> Z \<longrightarrow> I Z \<nu> = I Z \<omega>)"
proof -
  have "\<And>Z \<nu> \<omega>. Vagree \<nu> \<omega> (FVF (I Z)) \<Longrightarrow> VCagree \<nu> \<omega> (FNF (I Z))"
    unfolding VCagree_def FNF_partition using Vagree_sfilter_cong by simp
  hence "\<And>Z \<nu> \<omega>. FVF (I Z) \<subseteq> Z \<Longrightarrow> Vagree \<nu> \<omega> Z \<Longrightarrow> I Z \<nu> = I Z \<omega>"
    using Vagree_antimon coincidence_evaluation by metis
  moreover have "\<And>Z. (\<forall>Z \<nu> \<omega>. Vagree \<nu> \<omega> Z \<longrightarrow> I Z \<nu> = I Z \<omega>) \<Longrightarrow> FVF (I Z) \<subseteq> Z"
    unfolding FVF_def using Vagree_antimon by blast
  ultimately have "(\<forall>Z. FVF (I Z) \<subseteq> Z) = (\<forall>\<nu> \<omega> Z. Vagree \<nu> \<omega> Z \<longrightarrow> I Z \<nu> = I Z \<omega>)" by blast
  moreover have "(\<forall>Z. FNF (I (\<pi>\<^sub>V Z)) \<inter> \<iota>\<^sub>V \<V> \<subseteq> Z) = (\<forall>Z. FVF (I Z) \<subseteq> Z)"
    apply (simp add: FNF_partition only_vars_intersect iota_pi_vars_alternate) using pi_vars_injective by metis 
  ultimately show ?thesis unfolding is_pinterp_def by blast
qed


lemma PInterp_VBot_state_idependent: "PInterp I {} \<omega> = PInterp I {} \<nu>"
  using PInterp_correct is_pinterp_alt Vagree_empty by blast

(* okay as simplifier rule as Pred is not defined using PInterp but uses the underlying type directly *)
lemma PInterp_VBot_SOME_state [simp]: "PInterp I {} \<omega> = Pred I"
  unfolding Pred_def using PInterp_VBot_state_idependent by auto


lemma pi_tvars_empty [simp]: "\<pi>\<^sub>T {} = {}" by (simp add: pi_tvars_def)

lemma rtrm_sem_QRFunc [simp]: "rtrm_sem I (QRFunc f \<Theta>) = (\<lambda>\<omega>. (QRFuncs I f)(rargs_sem I \<Theta> \<omega>))" 
  apply (simp add: QRFunc_def QRFuncs_def QRPred_def)
  by (simp add: comp_def args_sem_def)

lemma fml_sem_QRGPsymb [simp]: "fml_sem I (QRGPsymb p \<Theta>) = {\<omega>. (QRPsymbs I p)(rargs_sem I \<Theta> \<omega>) }" 
  apply (simp add: QRGPsymb_def QRPsymbs_def QRPred_def)
  by (simp add: comp_def args_sem_def)


lemma pure_rtrm_com_independent:
  assumes "isQRpolynom \<theta>"
  shows "rtrm_sem I \<theta> (sfilter \<nu> Y) = rtrm_sem I \<theta> \<nu>"
proof (induction arbitrary: \<nu> rule: QRpolynom_induct)
  case (RVar x)
  then show ?case by (simp add: sfilter_def)
next
  case (QRConst f n)
  then show ?case by simp
next
  case (QRFunc f \<Theta>)
  then show ?case by (metis rargs_semI rtrm_sem_QRFunc)
qed (auto simp add: assms)






paragraph \<open>Coincidence for Programs\<close>

theorem coincidence_chp: "X \<supseteq> FVP (\<pi>\<^sub>I I) \<alpha> \<Longrightarrow> Vagree \<nu> \<nu>' X \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> 
    \<Longrightarrow> \<exists>\<omega>'. (\<nu>', \<tau>, \<omega>') \<in> chp_sem I \<alpha> \<and> Vagreebot \<omega> \<omega>' X"
proof -
  have "FVD (chp_sem I \<alpha>) \<subseteq> FVP (\<pi>\<^sub>I I) \<alpha>" unfolding FVD_def FVP_def by blast
  thus "X \<supseteq> FVP (\<pi>\<^sub>I I) \<alpha> \<Longrightarrow> Vagree \<nu> \<nu>' X \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> 
    \<Longrightarrow> \<exists>\<omega>'. (\<nu>', \<tau>, \<omega>') \<in> chp_sem I \<alpha> \<and> Vagreebot \<omega> \<omega>' X" using coincidence_denotation Vagree_antimon by auto
qed

theorem FVP_least_satisfying_coincidence:
  assumes "\<And>X I \<nu> \<nu>' \<tau> \<omega> \<omega>'. X \<supseteq> X\<^sub>0 \<Longrightarrow> Vagree \<nu> \<nu>' X \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> 
    \<Longrightarrow> \<exists>\<omega>'. (\<nu>', \<tau>, \<omega>') \<in> chp_sem I \<alpha> \<and> Vagreebot \<omega> \<omega>' X"
  shows "X\<^sub>0 \<supseteq> FVP (\<pi>\<^sub>I I) \<alpha>"
proof -
  have "\<And>I. X\<^sub>0 \<supseteq> FVD (chp_sem I \<alpha>)" using assms FVD_least_sat_coincidence by auto
  thus "X\<^sub>0 \<supseteq> FVP (\<pi>\<^sub>I I) \<alpha>" unfolding FVP_FVD by blast
qed

theorem coincidence_chp_fin: "X \<supseteq> FVP (\<pi>\<^sub>I I) \<alpha> \<Longrightarrow> Vagree \<nu> \<nu>' X \<Longrightarrow> (\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha> 
    \<Longrightarrow> \<exists>\<omega>'. (\<nu>', \<tau>, Fin \<omega>') \<in> chp_sem I \<alpha> \<and> Vagree \<omega> \<omega>' X"
proof -
  assume "X \<supseteq> FVP (\<pi>\<^sub>I I) \<alpha>" and "Vagree \<nu> \<nu>' X" and "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha>"
  hence "\<exists>\<omega>'. (\<nu>', \<tau>, \<omega>') \<in> chp_sem I \<alpha> \<and> Vagreebot (Fin \<omega>) \<omega>' X" 
    using coincidence_chp by blast
  thus ?thesis using Vagreebot_def by auto
qed



subsection \<open>Bound Effect Property\<close>


lemma bound_effect_classical: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> Vagree \<nu> ((\<omega> \<squnion> \<nu>) @@ \<tau>) (-BVP (\<pi>\<^sub>I I) \<alpha>)"
  unfolding BVP_def Vagree_def by auto

text \<open>Part of Lemma 10 in \<open>https://link.springer.com/chapter/10.1007/978-3-031-38499-8_6\<close>\<close>
theorem bound_effect_on_state:
  assumes "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha>"
  shows "Vagree \<nu> (\<omega> @@ \<tau>) (-BVP (\<pi>\<^sub>I I) \<alpha>)"
    and "Vagree \<nu> \<omega> (\<iota>\<^sub>T \<V>\<^sub>T)"
  using bound_effect_classical assms apply force
  using chps_do_not_bind_tvars assms by simp

theorem bound_effect_on_state_NonFin: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> Vagree \<nu> (\<omega> \<squnion> \<nu>) (\<iota>\<^sub>T \<V>\<^sub>T)"
  apply (cases \<omega>)
  using bound_effect_on_state by simp_all


theorem BVD_least_sat_coincidence:
  assumes "\<And>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> D \<Longrightarrow> Vagree \<nu> ((\<omega> \<squnion> \<nu>) @@ \<tau>) (-X)"
  shows "X \<supseteq> BVD D"
proof (rule ccontr)
  assume "\<not> (BVD D \<subseteq> X)"
  then obtain z \<nu> \<tau> \<omega> where "(\<nu>, \<tau>, \<omega>) \<in> D \<and> ((\<omega> \<squnion> \<nu>) @@ \<tau>) $$ z \<noteq> \<nu> $$ z \<and> z \<notin> X" using BVD_def by auto
  thus False using assms unfolding Vagree_def by auto
qed

theorem CND_least_sat_coincidence:
  assumes "\<And>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> D \<Longrightarrow> \<forall>h. byrec \<tau> h \<down> (-Y) `` {h} = []"
  shows "Y \<supseteq> CND D"
proof (rule ccontr)
  assume "\<not> (CND D \<subseteq> Y)"
  then obtain h ch \<nu> \<tau> \<omega> where "(\<nu>, \<tau>, \<omega>) \<in> D \<and> byrec \<tau> h \<down> {ch} \<noteq> [] \<and> (h, ch) \<notin> Y" using CND_def by fastforce
  thus False using assms
    by (metis Compl_iff Image_singleton_iff empty_subsetI insert_subset tfilter_empty_antimon)
qed


(* theorem bound_effect_on_com: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> rec_tfilter (byrec \<tau> h) (-CNP (\<pi>\<^sub>I I) \<alpha>) = []"
  by (rule rec_tfilter_emptyI) (auto simp add: CNP_def) *)


theorem bound_effect_on_com2: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> byrec \<tau> h \<down> (-CNP (\<pi>\<^sub>I I) \<alpha>) `` {h} = []"
  by (rule tfilter_emptyI) (auto simp add: CNP_def) 

corollary bound_effect_property_short:
  assumes "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha>"
  shows "Vagree \<nu> \<omega> (-BVP (\<pi>\<^sub>I I) \<alpha>)"
proof -
  have "Vagree (\<omega> @@ \<tau>) \<omega> (-\<iota>\<^sub>T \<V>\<^sub>T)" using Vagree_self_sttconc_on_rvars tvars_compl Vagree_sym_rel by presburger
  hence "Vagree \<nu> \<omega> ((-BVP (\<pi>\<^sub>I I) \<alpha>) \<inter> (-\<iota>\<^sub>T \<V>\<^sub>T))" by (meson Vagree_trans assms bound_effect_on_state)
  moreover have "Vagree \<nu> \<omega> (\<iota>\<^sub>T \<V>\<^sub>T)" using assms bound_effect_on_state by blast
  ultimately show ?thesis apply (rule Vagree_union_antimon) by blast
qed


corollary all_recorders_bound: (* contraposition explains lemma name *) 
  assumes "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha>"
  shows "\<And>h. h \<in> \<pi>\<^sub>T (-BVP (\<pi>\<^sub>I I) \<alpha>) \<Longrightarrow> byrec \<tau> h = []"
proof -
  fix h
  assume "h \<in> \<pi>\<^sub>T (-BVP (\<pi>\<^sub>I I) \<alpha>)"
  hence "\<And>I\<^sub>0 \<nu> \<tau> \<omega>. \<pi>\<^sub>I I = \<pi>\<^sub>I I\<^sub>0 \<Longrightarrow> (\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I\<^sub>0 \<alpha> \<Longrightarrow> (\<omega> @@ \<tau>) $$ (Tv h) = \<nu> $$ (Tv h)" 
    unfolding BVP_def by fastforce
  hence "(\<omega> @@ \<tau>) $$ (Tv h) = \<nu> $$ (Tv h)" using assms by blast
  hence "(\<nu> @@ \<tau>) $$ (Tv h) = \<nu> $$ (Tv h)" by (metis Vagree_alltvars assms byvar.simps(2) bound_effect_on_state(2) stT_sttconc_dist_access) 
  thus "byrec \<tau> h = []" using sttconc_def by simp
qed



subsection \<open>Bounds for the Least Static Semantics\<close>

paragraph \<open>General Bounds for the Static Semantics of (First-order) Real-arithmetic\<close>

lemma FVE_QRpolynom_subseteq_rvars:
  assumes "isQRpolynom \<theta>"
  shows "FVE J \<theta> \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R"
proof (rule, induction rule: QRpolynom_induct)
  case IsQRPoly
  thus ?case using assms by simp
next
  case (RVar x)
  thus ?case unfolding expr_sem_rtrm_def FVE_def Vagree_def iota_rvars_def by fastforce
next
  case (QRConst c n)
  thus ?case unfolding expr_sem_rtrm_def FVE_def QRConst_def by fastforce
next
  case (QRFunc f \<Theta>)
  then obtain I \<nu> \<omega> where agree: "J = \<pi>\<^sub>I I \<and> Vagree \<nu> \<omega> (-{x})" 
    and "expr_sem I (QRFunc f \<Theta>) \<nu> \<noteq> expr_sem I (QRFunc f \<Theta>) \<omega>" unfolding FVE_def by blast
  hence "rargs_sem I \<Theta> \<nu> \<noteq> rargs_sem I \<Theta> \<omega>" unfolding expr_sem_rtrm_def using rtrm_sem_QRFunc by force
  then obtain \<theta> where "\<theta> \<in> set \<Theta>" and "rtrm_sem I \<theta> \<nu> \<noteq> rtrm_sem I \<theta> \<omega>" using rargs_semI by blast
  hence "x \<in> FVE J \<theta>" unfolding expr_sem_rtrm_def FVE_def expr_sem.simps using agree by blast
  thus ?case using QRFunc \<open>\<theta> \<in> set \<Theta>\<close> nth_mem by auto
next
  case (Number l)
  thus ?case unfolding expr_sem_rtrm_def FVE_def Vagree_def by simp
next
  case (Plus \<theta>\<^sub>1 \<theta>\<^sub>2)
  then obtain I \<nu> \<omega> where 0: "J = \<pi>\<^sub>I I \<and> Vagree \<nu> \<omega> (-{x})" 
    and "expr_sem I (Plus \<theta>\<^sub>1 \<theta>\<^sub>2) \<nu> \<noteq> expr_sem I (Plus \<theta>\<^sub>1 \<theta>\<^sub>2) \<omega>" unfolding FVE_def by blast
  hence "rtrm_sem I \<theta>\<^sub>1 \<nu> \<noteq> rtrm_sem I \<theta>\<^sub>1 \<omega> \<or> rtrm_sem I \<theta>\<^sub>2 \<nu> \<noteq> rtrm_sem I \<theta>\<^sub>2 \<omega>" 
    by (simp add: expr_sem_rtrm_def)
  hence "x \<in> FVE J \<theta>\<^sub>1 \<or> x \<in> FVE J \<theta>\<^sub>2" using 0 unfolding expr_sem_rtrm_def FVE_def by blast
  thus ?case using Plus by blast
next
  case (Times \<theta>\<^sub>1 \<theta>\<^sub>2)
  then obtain I \<nu> \<omega> where 0: "J = \<pi>\<^sub>I I \<and> Vagree \<nu> \<omega> (-{x})" 
    and "expr_sem I (Times \<theta>\<^sub>1 \<theta>\<^sub>2) \<nu> \<noteq> expr_sem I (Times \<theta>\<^sub>1 \<theta>\<^sub>2) \<omega>" unfolding FVE_def by blast
  hence "rtrm_sem I \<theta>\<^sub>1 \<nu> \<noteq> rtrm_sem I \<theta>\<^sub>1 \<omega> \<or> rtrm_sem I \<theta>\<^sub>2 \<nu> \<noteq> rtrm_sem I \<theta>\<^sub>2 \<omega>" 
    unfolding expr_sem_rtrm_def by auto
  hence "x \<in> FVE J  \<theta>\<^sub>1 \<or> x \<in> FVE J  \<theta>\<^sub>2" using 0 unfolding expr_sem_rtrm_def FVE_def by blast
  thus ?case using Times by blast
qed

lemma FVE_FOL\<^sub>R_subseteq_rvars:
  assumes "isFOL\<^sub>R \<phi>"
  shows "FVE J \<phi> \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R"
proof (rule, induction rule: FOL\<^sub>R_induct)
  case IsFOL\<^sub>R
  thus ?case using assms by blast
next
  case (QRGPsymb p \<Theta>)
  then obtain I \<nu> \<omega> where agree: "J = \<pi>\<^sub>I I \<and> Vagree \<nu> \<omega> (-{x})" 
    and "expr_sem I (QRGPsymb p \<Theta>) \<nu> \<noteq> expr_sem I (QRGPsymb p \<Theta>) \<omega>" unfolding FVE_def by blast
  hence "rargs_sem I \<Theta> \<nu> \<noteq> rargs_sem I \<Theta> \<omega>" unfolding expr_sem_fml_def using fml_sem_QRGPsymb by force
  then obtain \<theta> where "\<theta> \<in> set \<Theta>" and "rtrm_sem I \<theta> \<nu> \<noteq> rtrm_sem I \<theta> \<omega>" by auto
  hence "x \<in> FVE J \<theta>" using agree unfolding expr_sem_rtrm_def FVE_def expr_sem.simps by blast
  thus ?case using QRGPsymb \<open>\<theta> \<in> set \<Theta>\<close> FVE_QRpolynom_subseteq_rvars by blast
next
  case (Geq \<theta> \<eta>)
  then obtain I \<nu> \<omega> where 0: "Vagree \<nu> \<omega> (-{x})" 
    and "expr_sem I (Geq \<theta> \<eta>) \<nu> \<noteq> expr_sem I (Geq \<theta> \<eta>) \<omega>" unfolding FVE_def by blast
  hence "(rtrm_sem I \<eta> \<nu> \<le> rtrm_sem I \<theta> \<nu>) \<noteq> (rtrm_sem I \<eta> \<omega> \<le> rtrm_sem I \<theta> \<omega>)" 
    by (simp add: expr_sem_fml_def)
  hence "x \<in> FVE (\<pi>\<^sub>I I) \<eta> \<or> x \<in> FVE (\<pi>\<^sub>I I) \<theta>" 
    using 0 Vagree_antimon coincidence_rtrm_FVE subset_Compl_singleton by metis
  thus ?case using FVE_QRpolynom_subseteq_rvars Geq by blast
next
  case (Not \<phi>)
  thus ?case unfolding expr_sem_fml_def FVE_def Vagree_def by simp
next
  case (And \<phi> \<psi>)
  then obtain I \<nu> \<omega> where 0: "Vagree \<nu> \<omega> (-{x}) \<and> J = \<pi>\<^sub>I I" 
    and "expr_sem I (\<phi> && \<psi>) \<nu> \<noteq> expr_sem I (\<phi> && \<psi>) \<omega>" unfolding FVE_def by blast
  hence "(\<nu> \<in> fml_sem I \<phi>) \<noteq> (\<omega> \<in> fml_sem I \<phi>) \<or> (\<nu> \<in> fml_sem I \<psi>) \<noteq> (\<omega> \<in> fml_sem I \<psi>)"
    by (auto simp add: expr_sem_fml_def)
  hence "x \<in> FVE (\<pi>\<^sub>I I) \<phi> \<or> x \<in> FVE (\<pi>\<^sub>I I) \<psi>" 
    using 0 Vagree_antimon coincidence_fml_FVE subset_Compl_singleton by meson
  thus ?case using And 0 by metis
next
  case (Exists z \<phi>)
  then obtain I \<nu> \<omega> where 0: "Vagree \<nu> \<omega> (-{x}) \<and> J = \<pi>\<^sub>I I" 
    and "expr_sem I (Exists (Rv z) \<phi>) \<nu> \<noteq> expr_sem I (Exists (Rv z) \<phi>) \<omega>" unfolding FVE_def by blast
  then obtain d where 1: "sorteq (Rv z) (Rp d)" 
    and "(upds \<nu> (Rv z) (Rp d) \<in> fml_sem I \<phi>) \<noteq> (upds \<omega> (Rv z) (Rp d) \<in> fml_sem I \<phi>)" 
    unfolding expr_sem_fml_def expr_sem.simps fml_sem.simps sorteq_def by blast
  hence "\<exists>z'. z' \<in> FVE (\<pi>\<^sub>I I) \<phi> \<and> ((upds \<omega> (Rv z) (Rp d)) $$ z' \<noteq> (upds \<nu> (Rv z) (Rp d)) $$ z')" 
    using coincidence_fml_FVE unfolding Vagree_def by blast
  hence "x \<in> FVE (\<pi>\<^sub>I I) \<phi>" using 0 1 upds_access ComplI empty_iff insert_iff unfolding Vagree_def by metis
  thus ?case using Exists 0 by metis
qed



paragraph \<open>General Bounds for the Static Semantics of Programs\<close>


lemma Vagree_trepv_cong [simp, intro]: "Vagree \<nu> \<omega> X \<Longrightarrow> Vagree (trepv \<nu> h \<rho>) (trepv \<omega> h \<rho>) X" 
  by (simp add: Vagree_def)

lemma Vagree_rrepv_cong [simp, intro]: "Vagree \<nu> \<omega> X \<Longrightarrow> Vagree (rrepv \<nu> x d) (rrepv \<omega> x d) X" 
  by (simp add: Vagree_def)

text \<open>Part of Corollary 15 of \<open>https://arxiv.org/abs/2408.05012\<close>\<close>

lemma history_independence: 
  assumes wf: "wf_chp \<L> \<alpha>"
  assumes run: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha>"
  shows "(trepv \<nu> h \<rho>, \<tau>, trepvbot \<omega> h \<rho>) \<in> chp_sem I \<alpha>"
using assms proof (induction arbitrary: \<nu> \<tau> \<omega> rule: chp_induct)
  case (Chp a Z Y)
  hence FVD_DiffD: "FVD (chp_sem I (Chp a Z Y)) \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R \<and> DiffD (chp_sem I (Chp a Z Y)) \<subseteq> -(\<iota>\<^sub>T \<V>\<^sub>T)" 
    using Chps_correct(3) is_denotation_def by auto
  hence "Tv h \<notin> FVD (chp_sem I (Chp a Z Y))" by auto
  moreover have "Vagree \<nu> (trepv \<nu> h \<rho>) (-{Tv h})" using Vagree_trepv by simp
  ultimately obtain \<omega>\<^sub>2 
    where run: "(trepv \<nu> h \<rho>, \<tau>, \<omega>\<^sub>2) \<in> (chp_sem I (Chp a Z Y)) \<and> (Vagreebot \<omega> \<omega>\<^sub>2 (-{Tv h}))"
    using FVD_def Chp by blast
  thus ?case
  proof (cases \<omega>)
    case (Fin \<omega>')
    then obtain \<omega>\<^sub>2' where "\<omega>\<^sub>2 = Fin \<omega>\<^sub>2'" using run unfolding Vagreebot_def by blast
    hence run: "(trepv \<nu> h \<rho>, \<tau>, Fin \<omega>\<^sub>2') \<in> (chp_sem I (Chp a Z Y)) \<and> Vagree \<omega>' \<omega>\<^sub>2' (-{Tv h})" 
      using run Fin Vagreebot_only_Fin by blast
    moreover have "Tv h \<notin> DiffD (chp_sem I (Chp a Z Y))" using FVD_DiffD by auto
    ultimately have "(trepv \<nu> h \<rho>) $$ (Tv h) = \<omega>\<^sub>2' $$ (Tv h)" using run FVD_DiffD DiffD_def by auto
    hence "Vagree (trepv \<nu> h \<rho>) \<omega>\<^sub>2' {Tv h}" unfolding Vagree_def by blast
    hence "Vagree (trepv \<omega>' h \<rho>) \<omega>\<^sub>2' {Tv h}" unfolding Vagree_def by auto
    moreover have "Vagree (trepv \<omega>' h \<rho>) \<omega>\<^sub>2' (-{Tv h})" using run unfolding Vagree_def by simp 
    ultimately have "Vagree (trepv \<omega>' h \<rho>) \<omega>\<^sub>2' ({Tv h}\<union>-{Tv h})" using Vagree_and by blast
    then show ?thesis using run Fin by simp
  next
    case NonFin
    then show ?thesis using Chp run unfolding Vagreebot_def by auto
  qed
next
  case (Assign x \<theta>) 
  moreover have "\<omega> \<noteq> NonFin \<Longrightarrow> trepv (gets \<omega>) h \<rho> = rrepv (trepv \<nu> h \<rho>) x (rtrm_sem I \<theta> (trepv \<nu> h \<rho>))"
  proof - 
    have free: "FVE (\<pi>\<^sub>I I) \<theta> \<subseteq> -{Tv h}" using Assign FVE_QRpolynom_subseteq_rvars by fastforce
    assume "\<omega> \<noteq> NonFin"
    hence "gets \<omega> = rrepv \<nu> x (rtrm_sem I \<theta> \<nu>)" using Assign by auto
    moreover have "rtrm_sem I \<theta> \<nu> = rtrm_sem I \<theta> (trepv \<nu> h \<rho>)" 
      by (meson Vagree_antimon Vagree_trepv coincidence_rtrm_FVE free)
    ultimately show ?thesis by (simp add: rrepv_trepv_commute)
  qed
  ultimately show ?case using Assign.prems(2) by force
next
  case (Nondet x)
  moreover have "\<omega> \<noteq> NonFin \<Longrightarrow> \<exists>r. trepv (gets \<omega>) h \<rho> = rrepv (trepv \<nu> h \<rho>) x r"
  proof -
    assume "\<omega> \<noteq> NonFin"
    hence "\<exists>r. gets \<omega> = rrepv \<nu> x r" using Nondet by auto
    thus ?thesis using rrepv_trepv_commute by auto
  qed
  ultimately show ?case by auto
next
  case (Evolution x \<theta> \<phi>)
  then show ?case 
  proof (cases \<omega>)
    case (Fin \<omega>)
    then obtain F T where 0: "\<tau> = [] \<and> Vagree \<nu> (F(0)) (-{Rv (DVarName x)}) 
      \<and> F(T) = \<omega> \<and> solves_ODE I F x \<theta> \<and> (\<forall>\<zeta>. F(\<zeta>) \<in> fml_sem I \<phi>)"
      using Evolution by auto

    have freeTheta: "FVE (\<pi>\<^sub>I I) \<theta> \<subseteq> -{Tv h}" using Evolution FVE_QRpolynom_subseteq_rvars by fastforce
    have freeDomain: "FVE (\<pi>\<^sub>I I) \<phi> \<subseteq> -{Tv h}" using Evolution FVE_FOL\<^sub>R_subseteq_rvars by fastforce

    let ?sol = "trepv_sol F h \<rho>"
    have "Vagree (trepv \<nu> h \<rho>) (?sol(0)) (-{Rv (DVarName x)}) \<and> ?sol(T) = trepv \<omega> h \<rho>"
      using 0 by (simp add: trepv_sol_def)
    moreover have "solves_ODE I ?sol x \<theta>"
      using 0 apply (simp add: solves_ODE_def trepv_sol_def)
      by (metis Vagree_antimon Vagree_trepv coincidence_rtrm_FVE freeTheta)
    moreover have "\<forall>\<zeta>. ?sol(\<zeta>) \<in> fml_sem I \<phi>"
      using 0 apply (simp add: solves_ODE_def trepv_sol_def)
      by (metis Vagree_antimon Vagree_trepv coincidence_fml_FVE freeDomain)
    ultimately have "\<tau> = [] \<and> Vagree (trepv \<nu> h \<rho>) (?sol(0)) (-{Rv (DVarName x)}) 
      \<and> ?sol(T) = (trepv \<omega> h \<rho>) \<and> solves_ODE I ?sol x \<theta> \<and> (\<forall>\<zeta>. ?sol(\<zeta>) \<in> fml_sem I \<phi>)"
      using 0 by blast
    then show ?thesis using Fin by auto 
  next
    case NonFin
    then show ?thesis using Evolution.prems(2) by force
  qed
next
  case (Test \<phi>)
  moreover have "\<omega> \<noteq> NonFin \<Longrightarrow> trepv \<nu> h \<rho> \<in> fml_sem I \<phi>"
  proof -
    assume "\<omega> \<noteq> NonFin"
    hence "\<nu> \<in> fml_sem I \<phi>" using Test by simp
    moreover have "FVE (\<pi>\<^sub>I I) \<phi> \<subseteq> -{Tv h}" using FVE_FOL\<^sub>R_subseteq_rvars Test by fastforce 
    ultimately show ?thesis by (meson Vagree_antimon Vagree_trepv coincidence_fml_FVE)
  qed
  ultimately show ?case by auto
next
  case (Choice \<alpha> \<beta>)
  thus ?case by auto
next
  case (Compose \<alpha> \<beta>)
  show ?case
  proof (cases "(\<nu>, \<tau>, \<omega>) \<in> botop (chp_sem I \<alpha>)")
    case True
    then obtain \<omega>' where "(\<nu>, \<tau>, \<omega>') \<in> chp_sem I \<alpha>" and 4: "\<omega> = NonFin" by auto
    hence "(trepv \<nu> h \<rho>, \<tau>, trepvbot \<omega>' h \<rho>) \<in> chp_sem I \<alpha>" using Compose by simp
    thus ?thesis using 4 by (simp, blast)
  next
    case False
    hence "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<triangleright> chp_sem I \<beta>" using Compose.prems(2) by auto
    then obtain \<tau>\<^sub>1 \<kappa> \<tau>\<^sub>2 where "(\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> chp_sem I \<alpha>" and "(\<kappa>, \<tau>\<^sub>2, \<omega>) \<in> chp_sem I \<beta>" 
      and "\<tau> = \<tau>\<^sub>1 @ \<tau>\<^sub>2" unfolding continue.simps by blast
    hence "(trepv \<nu> h \<rho>, \<tau>\<^sub>1, trepvbot (Fin \<kappa>) h \<rho>) \<in> chp_sem I \<alpha> 
      \<and> (trepv \<kappa> h \<rho>, \<tau>\<^sub>2, trepvbot \<omega> h \<rho>) \<in> chp_sem I \<beta> \<and> \<tau> = \<tau>\<^sub>1 @ \<tau>\<^sub>2" 
      using Compose unfolding wf_chp.simps by blast
    thus ?thesis by (simp, blast)
  qed
next
  case (Loop \<alpha>)
  then obtain n where "(\<nu>, \<tau>, \<omega>) \<in> iterate_linhis n (chp_sem I \<alpha>)" 
    unfolding chp_sem.simps linhis_rtcl_eq_iteration by auto
  thus ?case unfolding chp_sem.simps linhis_rtcl_eq_iteration
  proof (induction n arbitrary: \<nu> \<tau> \<omega>)
    case 0
    hence "(trepv \<nu> h \<rho>, \<tau>, trepvbot \<omega> h \<rho>) \<in> iterate_linhis 0 (chp_sem I \<alpha>)" 
      unfolding iterate_linhis.simps by fastforce
    thus ?case by blast
  next
    case (Suc n)
    thus ?case
    proof (induction n arbitrary: \<nu> \<tau> \<omega>)
      case 0
      hence "(trepv \<nu> h \<rho>, \<tau>, trepvbot \<omega> h \<rho>) \<in> iterate_linhis (Suc 0) (chp_sem I \<alpha>)" 
        using Loop chp_sem_total_and_pc neutComp_is_neut 
        unfolding wf_chp.simps iterate_linhis.simps compose.simps by fast
      thus ?case by blast
    next
      case (Suc n)
      thus ?case
      proof (cases "(\<nu>, \<tau>, \<omega>) \<in> botop (chp_sem I \<alpha>)")
        case True
        thus ?thesis using Suc(2) unfolding iterate_linhis.simps by blast
      next
        case False
        then obtain \<tau>\<^sub>1 \<kappa> \<tau>\<^sub>2 where 4: "(\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> (chp_sem I \<alpha>) 
          \<and> (\<kappa>, \<tau>\<^sub>2, \<omega>) \<in> (botop (chp_sem I \<alpha>) \<union> chp_sem I \<alpha> \<triangleright> iterate_linhis n (chp_sem I \<alpha>))" 
          and 5: "\<tau> = \<tau>\<^sub>1 @ \<tau>\<^sub>2" using Suc(3) unfolding iterate_linhis.simps continue.simps by blast
        hence "(trepv \<nu> h \<rho>, \<tau>\<^sub>1, Fin (trepv \<kappa> h \<rho>)) \<in> (chp_sem I \<alpha>)" 
          using Loop by (simp, fastforce)
        moreover have "(trepv \<kappa> h \<rho>, \<tau>\<^sub>2, trepvbot \<omega> h \<rho>) \<in> (\<Union>n. iterate_linhis n (chp_sem I \<alpha>))" 
          using Suc(2) 4 unfolding iterate_linhis.simps by blast
        ultimately show ?thesis using 5 linhis_rtcl_eq_iteration rtcl_linhis.rtcl_linhis_continue by fastforce
      qed
    qed
  qed
next
  case (Send ch h\<^sub>0 \<theta>)
  hence free: "FVE (\<pi>\<^sub>I I) \<theta> \<subseteq> -{Tv h}" using FVE_QRpolynom_subseteq_rvars by fastforce
  
  let ?\<tau> = "\<lambda>\<nu>. [mkrecevent h\<^sub>0 ch (rtrm_sem I \<theta> \<nu>) ((stR \<nu>)(\<mu>))]"
  have "(\<tau>, \<omega>) \<sqsubseteq> (?\<tau> \<nu>, Fin \<nu>)" using Send by simp
  moreover have "rtrm_sem I \<theta> \<nu> = rtrm_sem I \<theta> (trepv \<nu> h \<rho>)" 
    using free Vagree_antimon Vagree_trepv coincidence_rtrm_FVE by meson
  ultimately have "(\<tau>, trepvbot \<omega> h \<rho>) \<sqsubseteq> (?\<tau> (trepv \<nu> h \<rho>), Fin (trepv \<nu> h \<rho>))" 
    unfolding obspref_def by fastforce
  thus ?case by auto
next
  case (Receive ch h\<^sub>0 x)
  let ?\<tau> = "\<lambda>r. [mkrecevent h\<^sub>0 ch r ((stR \<nu>)(\<mu>))]"

  obtain r where obs: "(\<tau>, \<omega>) \<sqsubseteq> (?\<tau> r, Fin (rrepv \<nu> x r))" using Receive by fastforce
  have "(\<tau>, trepvbot \<omega> h \<rho>) \<sqsubseteq> (?\<tau> r, Fin (rrepv (trepv \<nu> h \<rho>) x r))" 
  proof (cases \<omega>)
    case (Fin \<omega>\<^sub>0)
    hence "\<omega>\<^sub>0 = rrepv \<nu> x r" using obs by (simp add: obspref_def)
    hence "trepv \<omega>\<^sub>0 h \<rho> = rrepv (trepv \<nu> h \<rho>) x r" using obs by (simp add: rrepv_trepv_commute)
    thus ?thesis using obs Fin by (simp add: obspref_def)
  next
    case NonFin
    then show ?thesis using obs by (simp add: obspref_def)
  qed
  thus ?case by auto
next
  case (Par \<alpha> \<beta>)
  then obtain \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> where alpha: "(\<nu>, \<tau> \<down> CN (\<pi>\<^sub>I I) \<alpha>, \<omega>\<^sub>\<alpha>) \<in> chp_sem I \<alpha>"
    and beta: "(\<nu>, \<tau> \<down> CN (\<pi>\<^sub>I I) \<beta>, \<omega>\<^sub>\<beta>) \<in> chp_sem I \<beta>"
    and gtime: "Vagreebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> \<V>\<^sub>\<mu>"
    and merge: "\<omega> = lmergebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> (BVP (\<pi>\<^sub>I I) \<alpha>)" 
    and nojunk: "\<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha> \<union> CN (\<pi>\<^sub>I I) \<beta>) = \<tau>" by auto
  hence "(trepv \<nu> h \<rho>, \<tau> \<down> CN (\<pi>\<^sub>I I) \<alpha>, trepvbot \<omega>\<^sub>\<alpha> h \<rho>) \<in> chp_sem I \<alpha>"
    and "(trepv \<nu> h \<rho>, \<tau> \<down> CN (\<pi>\<^sub>I I) \<beta>, trepvbot \<omega>\<^sub>\<beta> h \<rho>) \<in> chp_sem I \<beta>" 
    using Par.IH Par.prems(1) by auto

  moreover have "Vagreebot (trepvbot \<omega>\<^sub>\<alpha> h \<rho>) (trepvbot \<omega>\<^sub>\<beta> h \<rho>) \<V>\<^sub>\<mu> 
    \<and> (trepvbot \<omega> h \<rho>) = lmergebot (trepvbot \<omega>\<^sub>\<alpha> h \<rho>) (trepvbot \<omega>\<^sub>\<beta> h \<rho>) (BVP (\<pi>\<^sub>I I) \<alpha>)"
  proof (cases "\<omega>\<^sub>\<alpha> = NonFin \<or> \<omega>\<^sub>\<beta> = NonFin")
    case True
    thus ?thesis using gtime merge unfolding Vagreebot_def by auto
  next
    case False
    then obtain \<omega>' \<omega>\<^sub>\<alpha>' \<omega>\<^sub>\<beta>' where fin: "\<omega> = Fin \<omega>' \<and> \<omega>\<^sub>\<alpha> = Fin \<omega>\<^sub>\<alpha>' \<and> \<omega>\<^sub>\<beta> = Fin \<omega>\<^sub>\<beta>'" 
      using merge by (metis lmergebot.elims)
    hence agree: "Vagree \<omega>\<^sub>\<alpha>' \<omega>\<^sub>\<beta>' \<V>\<^sub>\<mu>" and merge: "\<omega>' = lmerge \<omega>\<^sub>\<alpha>' \<omega>\<^sub>\<beta>' (BVP (\<pi>\<^sub>I I) \<alpha>)" 
      using Vagreebot_only_Fin gtime fin merge by auto
    hence "trepvbot \<omega> h \<rho> = Fin (trepv \<omega>' h \<rho>) \<and> trepvbot \<omega>\<^sub>\<alpha> h \<rho> = Fin (trepv \<omega>\<^sub>\<alpha>' h \<rho>) 
      \<and> trepvbot \<omega>\<^sub>\<beta> h \<rho> = Fin (trepv \<omega>\<^sub>\<beta>' h \<rho>)" using fin by simp
    moreover have  agree: "Vagree (trepv \<omega>\<^sub>\<alpha>' h \<rho>) (trepv \<omega>\<^sub>\<beta>' h \<rho>) \<V>\<^sub>\<mu>" 
      using Vagree_def agree trepv_access by presburger
    moreover have "(trepv \<omega>' h \<rho>) = lmerge (trepv \<omega>\<^sub>\<alpha>' h \<rho>) (trepv \<omega>\<^sub>\<beta>' h \<rho>) (BVP (\<pi>\<^sub>I I) \<alpha>)"
      apply (rule state_eqI)
      using lmerge_access merge trepv_access by presburger  
    ultimately show ?thesis using Vagreebot_only_Fin lmergebot_fin by presburger
  qed
  ultimately show ?case using nojunk by auto
qed

lemma FVP_bound_rvars: 
  assumes "wf_chp \<L> \<alpha>"
  shows "FVP (\<pi>\<^sub>I I) \<alpha> \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R"
proof
  fix z                  
  have "z \<notin> \<iota>\<^sub>R \<V>\<^sub>R \<Longrightarrow> z \<notin> FVP (\<pi>\<^sub>I I) \<alpha>"
  proof -
    assume "z \<notin> \<iota>\<^sub>R \<V>\<^sub>R"
    then obtain h where "z = Tv h" using tvars_compl iota_tvars_def by auto
    have "\<And>I \<nu>\<^sub>1 \<nu>\<^sub>2 \<tau>\<^sub>1 \<omega>\<^sub>1. (Vagree \<nu>\<^sub>1 \<nu>\<^sub>2 (-{Tv h})) \<and> (\<nu>\<^sub>1, \<tau>\<^sub>1, \<omega>\<^sub>1) \<in> chp_sem I \<alpha> 
            \<longrightarrow> (\<exists>\<tau>\<^sub>2 \<omega>\<^sub>2. (\<nu>\<^sub>2, \<tau>\<^sub>1, \<omega>\<^sub>2) \<in> chp_sem I \<alpha> \<and> Vagreebot \<omega>\<^sub>1 \<omega>\<^sub>2 (-{Tv h}))"
    proof
      fix I \<nu>\<^sub>1 \<nu>\<^sub>2 \<tau>\<^sub>1 \<omega>\<^sub>1
      assume "Vagree \<nu>\<^sub>1 \<nu>\<^sub>2 (-{Tv h}) \<and> (\<nu>\<^sub>1, \<tau>\<^sub>1, \<omega>\<^sub>1) \<in> chp_sem I \<alpha>"
      hence "trepv \<nu>\<^sub>1 h (stT \<nu>\<^sub>2 h) = \<nu>\<^sub>2 \<and> (\<nu>\<^sub>1, \<tau>\<^sub>1, \<omega>\<^sub>1) \<in> chp_sem I \<alpha>"
        using Vagree_single_upds by simp
      hence "(\<nu>\<^sub>2, \<tau>\<^sub>1, trepvbot \<omega>\<^sub>1 h (stT \<nu>\<^sub>2 h)) \<in> chp_sem I \<alpha>" 
        using history_independence assms by metis
      moreover have "Vagreebot \<omega>\<^sub>1 \<omega>\<^sub>1 (-{Tv h})" 
        unfolding Vagreebot_def using Vagree_refl reachedstate.collapse by metis
      ultimately show "\<exists>\<tau>\<^sub>2 \<omega>\<^sub>2. (\<nu>\<^sub>2, \<tau>\<^sub>1, \<omega>\<^sub>2) \<in> chp_sem I \<alpha> \<and> Vagreebot \<omega>\<^sub>1 \<omega>\<^sub>2 (-{Tv h})" 
        unfolding Vagreebot_def using Vagree_trepv by fastforce
    qed
    thus "z \<notin> FVP (\<pi>\<^sub>I I) \<alpha>" using FVP_def \<open>z = Tv h\<close> by simp
  qed
  thus "z \<in> FVP (\<pi>\<^sub>I I) \<alpha> \<Longrightarrow> z \<in> \<iota>\<^sub>R \<V>\<^sub>R" by auto
qed

corollary FVP_no_tvars: "wf_chp \<L> \<alpha> \<Longrightarrow> FVP (\<pi>\<^sub>I I) \<alpha> \<subseteq> -(\<iota>\<^sub>T \<V>\<^sub>T)" 
  using FVP_bound_rvars by auto


lemma nocom_no_chans: "(\<And>I. nocom_denotation (chp_sem I \<alpha>)) \<Longrightarrow> CNP J \<alpha> = {}"
  unfolding CNP_def by fastforce



(* lemma BVP_diff_vars: "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> diff_vars \<nu> (\<omega> @@ \<tau>) \<subseteq> BVP (\<pi>\<^sub>I I) \<alpha>"
  unfolding BVP_def diff_vars_def by fastforce

lemma RecP_diff_vars: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> diff_vars \<nu> (\<nu> @@ \<tau>) \<subseteq> RecP (\<pi>\<^sub>I I) \<alpha>"
  unfolding RecP_def diff_vars_def by fastforce *)


lemma in_tchans_proj_non_empty1: "ch \<in> tchans \<tau> \<Longrightarrow> (\<exists>h. ch \<in> tchans (byrec \<tau> h))"
   apply (induction \<tau>)
  apply simp
  by (simp add: byrec_def tflat_def) (blast)

lemma CNP_tchans0: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> tchans (byrec \<tau> h) \<subseteq> CNP (\<pi>\<^sub>I I) \<alpha> `` UNIV"
  using CNP_def in_tchans_proj_non_empty by fast

lemma CNP_tchans: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> tchans \<tau> \<subseteq> CNP (\<pi>\<^sub>I I) \<alpha> `` UNIV"
  using CNP_tchans0 in_tchans_proj_non_empty1 by fastforce






lemma tvar_diff_states_exist: "\<exists>\<nu> \<omega>. Vagree \<nu> \<omega> (-{Tv h}) \<and> stT \<nu> h \<noteq> stT \<omega> h"
  by (metis (full_types) Vagree_trepv list.simps(3) trepv_stT_access)


lemma by_rec_conv_some_ch: "byrec \<tau> h \<noteq> [] \<Longrightarrow> \<exists>ch. byrec \<tau> h \<down> {ch} \<noteq> []"
proof -
  have "\<forall>ch. byrec \<tau> h \<down> {ch} = [] \<Longrightarrow> byrec \<tau> h \<down> \<Omega> = []"
    by (rule tfilter_emptyI) (simp)
  thus "byrec \<tau> h \<noteq> [] \<Longrightarrow> \<exists>ch. byrec \<tau> h \<down> {ch} \<noteq> []" by auto
qed



paragraph \<open>Concrete Bounds on Free Variables\<close>

lemma FVE_Empty [simp]: "FVE J Empty = {}"
  by (simp add: FVE_def expr_sem_ttrm_def)

lemma FVE_TVar [simp]: "FVE J (TVar h) = {Tv h}"
  apply (simp add: FVE_def expr_sem_ttrm_def)
  apply (rule, clarify)
    apply (metis Vagree_single_upds sorteq_self_val stT_upds_other)
  using binterp_has_interp tvar_diff_states_exist by blast

lemma FVE_Proj [simp, intro]: "FVE J (Proj te Y) \<subseteq> FVE J te"
  by (fastforce simp add: FVE_def expr_sem_ttrm_def)

lemma CNE_Proj [simp, intro]: "CNE J (Proj te Y) \<subseteq> CNE J te"
  by (fastforce simp add: CNE_def expr_sem_ttrm_def)

lemma CNE_Proj_rec: "CNE J (Proj (TVar rec) Y) \<subseteq> ({rec} \<times> CNC J Y)"
proof
  fix tch
  have 0: "\<And>\<tau>\<^sub>1 \<tau>\<^sub>2 ch Y. \<tau>\<^sub>1 \<down> (-{ch}) = \<tau>\<^sub>2 \<down> (-{ch}) \<Longrightarrow> \<tau>\<^sub>1 \<down> Y \<noteq> \<tau>\<^sub>2 \<down> Y \<Longrightarrow> ch \<in> Y"
    by (meson subset_Compl_singleton tfilter_cong_antimon)
  assume "tch \<in> CNE J (Proj (TVar rec) Y)"
  then obtain h ch I \<nu> \<omega> where 1: "tch = (h, ch) \<and> J = \<pi>\<^sub>I I \<and> sfilter \<nu> (-{(h, ch)}) = sfilter \<omega> (-{(h, ch)})
    \<and> \<not>(expr_sem I (Proj (TVar rec) Y) \<nu> = expr_sem I (Proj (TVar rec) Y) \<omega>)" using CNE_def by blast
  hence 2: "stT \<nu> rec \<down> (cspace_sem (\<pi>\<^sub>I I) Y) \<noteq> stT \<omega> rec \<down> (cspace_sem (\<pi>\<^sub>I I) Y)" 
    unfolding expr_sem_ttrm_def by simp
  moreover have "\<And>h0. h0\<noteq>h \<Longrightarrow> stT \<nu> h0 = stT \<omega> h0" 
    using 1 by (metis Vagree_single_upds sfilter_singleton_compl_Vagree sorteq_self_val stT_upds_other variable.inject(2))
  ultimately have hrec: "h = rec" using 1 by metis
  hence "stT \<nu> rec \<down> (-{ch}) = stT \<omega> rec \<down> (-{ch})" 
    using 1 by (metis sfilter_eq_stT_E singleton_compl_image_same)
  moreover have "stT \<nu> rec \<down> (cspace_sem (\<pi>\<^sub>I I) Y) \<noteq> stT \<omega> rec \<down> (cspace_sem (\<pi>\<^sub>I I) Y)"
    using 2 unfolding expr_sem_ttrm_def by simp 
  ultimately have "ch \<in> cspace_sem (\<pi>\<^sub>I I) Y" using 0 1 by auto
  thus "tch \<in> {rec} \<times> CNC J Y" using hrec 1 unfolding CNC_def by auto
qed

lemma FVE_Concat: "FVE J (te\<^sub>1 \<circ>\<^sub>T te\<^sub>2) \<subseteq> FVE J te\<^sub>1 \<union> FVE J te\<^sub>2"
  apply (simp add: FVE_def expr_sem_ttrm_def) 
  apply clarify by auto


lemma FVE_Concat_TVars: "FVE (\<pi>\<^sub>I I) ((TVar h0) \<circ>\<^sub>T (TVar h)) \<subseteq> {Tv h0, Tv h}"
  using FVE_Concat FVE_TVar by blast

lemma sfilter_UNIV [simp]: "sfilter \<nu> UNIV = \<nu>" using sfilter_all by (simp add: allcomtar_def)

lemma VCagree_Bc_compl_Vagree: "VCagree \<nu> \<omega> (-{Bc h ch}) \<Longrightarrow> Vagree \<nu> \<omega> (-{Tv h})"
  unfolding VCagree_def by (simp add: sfilter_singleton_compl_Vagree)

lemma VCagree_singleton_compl_not_Vagree: "VCagree \<nu> \<omega> (-{b}) \<Longrightarrow> \<not> Vagree \<nu> \<omega> X \<Longrightarrow> b \<in> \<iota>\<^sub>V X \<union> \<iota>\<^sub>C (\<pi>\<^sub>T X \<times> \<Omega>)"
  apply (cases b)
   apply (simp add: VCagree_def) using FNV_def Vagree_antimon in_iota(1) apply blast
  apply simp                               
  apply (drule VCagree_Bc_compl_Vagree)
  using Vagree_antimon in_iota(1) by blast
  
lemma FNE_Psymb: "FNE J (Psymb i Z \<Theta>) \<subseteq> FNV J Z \<union> FNArgs J \<Theta>"
proof
  fix z
  assume "z \<in> FNE J (Psymb i Z \<Theta>)"
  then obtain I \<nu> \<omega> where 0: "J = \<pi>\<^sub>I I \<and> VCagree \<nu> \<omega> (-{z}) 
    \<and> \<not>(expr_sem I (Psymb i Z \<Theta>) \<nu> = expr_sem I (Psymb i Z \<Theta>) \<omega>)"
    unfolding FNE_def by auto
  hence "\<not> Vagree \<nu> \<omega> (vspace_sem (\<pi>\<^sub>I I) Z) \<or> args_sem I \<Theta> \<nu> \<noteq> args_sem I \<Theta> \<omega>" 
    apply (simp add: Psymb_def expr_sem_fml_def)
    by (metis (full_types) PInterp_correct is_pinterp_alt)
  hence "z \<in> FNV J Z \<or> z \<in> FNArgs J \<Theta>"
    using 0 VCagree_singleton_compl_not_Vagree 
    unfolding FNV_def FVV_def CNV_def
    by (meson VCagree_antimon coincidence_args subset_Compl_singleton)
  thus "z \<in> FNV J Z \<union> FNArgs J \<Theta>" by simp
qed


lemma pi_vars_subseteqI: "\<iota>\<^sub>V Y \<subseteq> Z \<Longrightarrow> Y \<subseteq> \<pi>\<^sub>V Z" by (auto simp add: iota_vars_def pi_vars_def)
lemma pi_comtar_subseteqI: "\<iota>\<^sub>C Y \<subseteq> Z \<Longrightarrow> Y \<subseteq> \<pi>\<^sub>C Z" by (auto simp add: iota_comtar_def pi_comtar_def)

lemma FVE_Psymb0: "\<pi>\<^sub>V (FNE J (Psymb i Z \<Theta>)) \<subseteq> FVV J Z \<union> \<pi>\<^sub>V (FNArgs J \<Theta>)"
  using FNE_Psymb unfolding FNV_def FVV_def using \<pi>\<^sub>V_inverse \<pi>\<^sub>V_dist_union pi_vars_mono
  by (metis (no_types, lifting) ext \<pi>\<^sub>V_anychans sup_bot.right_neutral)
                                                            
lemma FVE_Psymb: "FVE J (Psymb i Z \<Theta>) \<subseteq> FVV J Z \<union> FVArgs J \<Theta>"
  using FVE_Psymb0 by (simp add: FNE_partition FNArgs_partition)

lemma CNE_Psymb0: "\<pi>\<^sub>C (FNE J (Psymb i Z \<Theta>)) \<subseteq> \<pi>\<^sub>C (FNV J Z) \<union> \<pi>\<^sub>C (FNArgs J \<Theta>)"
  using FNE_Psymb \<pi>\<^sub>C_dist_union pi_comtar_mono by metis


lemma pi_comtar_FNV_CNV [simp]: "\<pi>\<^sub>C (FNV J Z) = CNV J Z" by (simp add: FNV_def CNV_def)

lemma CNE_Psymb: "CNE J (Psymb i Z \<Theta>) \<subseteq> CNV J Z \<union> CNArgs J \<Theta>"
  using CNE_Psymb0 by (simp add: FNE_partition FNArgs_partition)



lemma FVE_RArg [simp]: "FVE J (RArg \<theta>) = FVE J \<theta>" by (simp add: FVE_def)
lemma FVE_TArg [simp]: "FVE J (TArg te) = FVE J te" by (simp add: FVE_def)
lemma CNE_RArg [simp]: "CNE J (RArg \<theta>) = CNE J \<theta>" by (simp add: CNE_def)
lemma CNE_TArg [simp]: "CNE J (TArg te) = CNE J te" by (simp add: CNE_def)


lemma FNE_Psymb_TArg: "FNE J (Psymb i X [TArg te]) \<subseteq> FNV J X \<union> (FNE J te)"
  using FNE_Psymb by fastforce

lemma FVP_Chp: "FVP J (Chp a Z Y) \<subseteq> vspace_sem J Z \<inter> (\<iota>\<^sub>R \<V>\<^sub>R)"
proof - 
  have "\<And>I. FVD (Chps I a (vspace_sem (\<pi>\<^sub>I I) Z) (cspace_sem (\<pi>\<^sub>I I) Y)) \<subseteq> vspace_sem (\<pi>\<^sub>I I) Z \<inter> \<iota>\<^sub>R \<V>\<^sub>R"
    using Chps_correct is_denotation_def by simp
  thus ?thesis unfolding FVP_FVD using Chps_correct(3) by fastforce
qed

lemma FRvP_Chp: "\<pi>\<^sub>R (FVP J (Chp a Z Y)) \<subseteq> rvspace_sem J Z"
  using FVP_Chp unfolding pi_rvars_def by blast



paragraph \<open>Concrete Bounds on Bound Names\<close>

abbreviation chpspace_sem where "chpspace_sem J Z Y \<equiv> \<iota>\<^sub>V (vspace_sem J Z) \<union> (\<iota>\<^sub>C (\<pi>\<^sub>T (vspace_sem J Z) \<times> (cspace_sem J Y)))"

lemma BNP_Chp: "BNP J (Chp a Z Y) \<subseteq> chpspace_sem J Z Y"
  apply (simp add: BNP_BND)           
  using bound_effect_def by blast

lemma BVP_Chp: "BVP J (Chp a Z Y) \<subseteq> vspace_sem J Z"
  using BNP_Chp BNP_partition
  by (metis \<pi>\<^sub>V_anychans \<pi>\<^sub>V_dist_union \<pi>\<^sub>V_inverse pi_vars_mono sup_bot.right_neutral)
  
lemma BRvP_Chp: "\<pi>\<^sub>R (BVP J (Chp a Z Y)) \<subseteq> rvspace_sem J Z"
  using BVP_Chp pi_rvars_def by blast

lemma CNP_Chp: "CNP J (Chp a Z Y) \<subseteq> \<pi>\<^sub>T (vspace_sem J Z) \<times> (cspace_sem J Y)"
  using BNP_Chp BNP_partition
  by (metis \<pi>\<^sub>C_anyvars \<pi>\<^sub>C_dist_union \<pi>\<^sub>C_inverse pi_comtar_mono sup_bot_left)
  

lemma BRecD_BVD_overapprox: "DiffD D \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R \<Longrightarrow> Domain (CND D) \<subseteq> \<pi>\<^sub>T (BVD D)"
  unfolding CND_def BVD_def
  by (fastforce simp add: stT_sttconc_dist)




lemma stT_ini_eq_fin: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> \<omega> \<noteq> NonFin \<Longrightarrow> (stT \<nu>) = (stT (gets \<omega>))"
  using Vagree_alltvars bound_effect_on_state(2) by auto

lemma ini_eq_fin: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> \<omega> \<noteq> NonFin \<Longrightarrow> \<nu> $$ (Tv h) = (gets \<omega>) $$ (Tv h)"
  using stT_ini_eq_fin by simp

lemma ini_neq_fin_conv: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> \<omega> \<noteq> NonFin \<Longrightarrow> \<nu> $$ z \<noteq> (gets \<omega>) $$ z \<Longrightarrow> \<not>isTv z"
  using ini_eq_fin by blast

lemma variable_dichotomy: "isRv z \<longleftrightarrow> \<not>isTv z" by (metis variable.collapse(1,2) variable.simps(4))
                                                                                                
lemma RecP_subseteq_BVP: "\<iota>\<^sub>T (RecP J \<alpha>) \<subseteq> BVP J \<alpha>"
  unfolding RecP_def BVP_def iota_tvars_def
  by (fastforce simp add: stT_sttconc_dist stT_ini_eq_fin)



lemma RecP_Chp_overapprox: "RecP J (Chp a Z Y) \<subseteq> \<pi>\<^sub>T (vspace_sem J Z)"
  using RecP_subseteq_BVP BVP_Chp by fastforce


lemma BVP_assign_other: "Rv x \<noteq> y \<Longrightarrow> y \<notin> BVP J (x := \<theta>)"
  unfolding BVP_def by auto

lemma BVP_assign_meta: "(\<And>I \<omega>. rtrm_sem I \<theta> \<omega> = stR \<omega> x) \<Longrightarrow> BVP J (x := \<theta>) = {}"
  and "rtrm_sem I \<theta> \<omega> \<noteq> stR \<omega> x \<Longrightarrow> BVP (\<pi>\<^sub>I I) (x := \<theta>) = {Rv x}"
  unfolding BVP_def apply rule
  apply auto
   apply argo 
  by fastforce


lemma state_join_concat_neq: "\<tau> = [] \<Longrightarrow> (\<omega> \<squnion> \<nu>) @@ \<tau> $$ z \<noteq> \<nu> $$ z \<Longrightarrow> \<omega> \<noteq> NonFin" by auto

lemma state_join_neq: "\<omega> $$ z \<noteq> \<nu> $$ z \<Longrightarrow> ((Fin \<omega>) \<squnion> \<nu>) $$ z \<noteq> \<nu> $$ z" by auto

lemma BVP_BVP_old: "BVP_old J \<alpha> \<subseteq> BVP J \<alpha>"
  unfolding BVP_old_def BVP_def by fastforce

lemma state_join_neq_conv: "(stR (\<omega> \<squnion> \<nu>) x \<noteq> stR \<nu> x) \<Longrightarrow> (stR (gets \<omega>) x \<noteq> stR \<nu> x)"
  apply (cases \<omega>)
  by auto

lemma BVP_assign: "BVP J (x := \<theta>) = (if (\<forall>I \<omega>. \<pi>\<^sub>I I = J \<longrightarrow> rtrm_sem I \<theta> \<omega> = stR \<omega> x) then {} else {Rv x})"
proof -
  have "\<exists>I \<omega>. \<pi>\<^sub>I I = J \<and> rtrm_sem I \<theta> \<omega> \<noteq> stR \<omega> x \<Longrightarrow> Rv x \<in> BVP_old J (x := \<theta>)"
    using rrepv_def BVP_old_def by auto
  hence "\<exists>I \<omega>. \<pi>\<^sub>I I = J \<and> rtrm_sem I \<theta> \<omega> \<noteq> stR \<omega> x \<Longrightarrow> Rv x \<in> BVP J (x := \<theta>)"
    using BVP_BVP_old by blast
  moreover have "BVP J (x := \<theta>) \<subseteq> {Rv x}" unfolding BVP_def using state_join_concat_neq by fastforce
  moreover have "\<forall>I \<omega>. \<pi>\<^sub>I I = J \<longrightarrow> rtrm_sem I \<theta> \<omega> = stR \<omega> x \<Longrightarrow> BVP J (x := \<theta>) = {}" 
    by (auto simp add: BVP_def rrepv_def state_join_concat_neq)
  ultimately show ?thesis by auto
qed

lemma BVP_nondet_other: "Rv x \<noteq> y \<Longrightarrow> y \<notin> BVP J (x := *)"
  unfolding BVP_def by auto

lemma BVP_nondet: "BVP J (x := *) = {Rv x}"
proof -
  fix \<nu>
  have 0: "BVP J (x := *) \<subseteq> {Rv x}" using BVP_nondet_other by (metis singletonI subsetI)
  let ?\<omega> = "rrepv \<nu> x (stR \<nu> x + 1)"
  obtain I where "J = \<pi>\<^sub>I I \<and> (\<nu>, [], Fin ?\<omega>) \<in> chp_sem I (x := *)"
    using binterp_has_interp by fastforce
  moreover have "?\<omega> $$ Rv x \<noteq> \<nu> $$ Rv x" by auto
  ultimately have 1: "Rv x \<in> BVP J (x := *)" using BVP_elem sttconc_empty state_join_neq by metis
  from 0 1 show ?thesis by auto
qed

lemma BVP_test: "BVP J (Test \<phi>) = {}"
  unfolding BVP_def by auto

lemma BVP_Evolution: "BVP J (Evolution x \<theta> \<phi>) \<subseteq> bvrident x"
proof
  fix z
  assume "z \<in> BVP J (Evolution x \<theta> \<phi>)"
  then obtain I \<nu> \<tau> \<omega> where 0: "J = \<pi>\<^sub>I I \<and> (\<nu>, \<tau>, \<omega>) \<in> chp_sem I (Evolution x \<theta> \<phi>) \<and> ((\<omega> \<squnion> \<nu>) @@ \<tau>) $$ z \<noteq> \<nu> $$ z"
    using BVP_def by blast
  then obtain \<omega>\<^sub>0 where neq: "\<omega> = Fin \<omega>\<^sub>0" "\<omega>\<^sub>0 $$ z \<noteq> \<nu> $$ z" by auto
  then obtain F T where sol: "Vagree \<nu> (F(0)) (-{Rv (DVarName x)}) \<and> F(T) = \<omega>\<^sub>0 \<and> solves_ODE I F x \<theta>"
    using 0 by auto
  hence "Vagree \<nu> (F(0)) (-(bvrident x))" by auto
  moreover have "Vagree (F(T)) \<omega>\<^sub>0 (-(bvrident x))" using sol by blast
  moreover have "Vagree (F(0)) (F(T)) (-(bvrident x))" 
    using sol unfolding solves_ODE_def by blast
  ultimately have "Vagree \<nu> \<omega>\<^sub>0 (-(bvrident x))" using Vagree_only_trans by blast
  thus "z \<in> bvrident x" using neq Vagree_def by auto
qed
  
lemma BVP_choice_bound: "BVP J (\<alpha> \<union>\<union> \<beta>) \<subseteq> BVP J \<alpha> \<union> BVP J \<beta>"
  using BVP_def by auto

lemma BVP_compose_bound: "BVP J (\<alpha> ;; \<beta>) \<subseteq> BVP J \<alpha> \<union> BVP J \<beta>"
proof
  fix z
  assume "z \<in> BVP J (\<alpha> ;; \<beta>)"
  then obtain I \<nu> \<tau> \<omega> where eqJ: "\<pi>\<^sub>I I = J"
    and run: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I (\<alpha> ;; \<beta>)"
    and neq: "(\<omega> \<squnion> \<nu>) @@ \<tau> $$ z \<noteq> \<nu> $$ z" unfolding BVP_def by blast
  then obtain \<kappa> \<tau>\<^sub>1 \<tau>\<^sub>2 where subruns: "(\<nu>, \<tau>, \<omega>) \<in> botop (chp_sem I \<alpha>) 
      \<or> (\<tau> = \<tau>\<^sub>1 @ \<tau>\<^sub>2 \<and> (\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> chp_sem I \<alpha> \<and> (\<kappa>, \<tau>\<^sub>2, \<omega>) \<in> chp_sem I \<beta>)"
    by auto

  thus "z \<in> BVP J \<alpha> \<union> BVP J \<beta>"
  proof (cases "(\<nu>, \<tau>, \<omega>) \<in> botop (chp_sem I \<alpha>)")
    case True
    hence "\<nu> @@ \<tau> $$ z \<noteq> \<nu> $$ z" using neq by simp
    moreover obtain \<omega>\<^sub>0 where "(\<nu>, \<tau>, \<omega>\<^sub>0) \<in> chp_sem I \<alpha>" using True by auto
    ultimately show ?thesis by (metis BVP_elem eqJ lower_run state_join.simps(2) unfold_simps(1))
  next
    case False
    hence com: "\<tau> = \<tau>\<^sub>1 @ \<tau>\<^sub>2" 
        and alpha: "(\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> chp_sem I \<alpha>" 
        and beta: "(\<kappa>, \<tau>\<^sub>2, \<omega>) \<in> chp_sem I \<beta>" 
      using subruns by auto
    hence "((Fin \<kappa> \<squnion> \<nu>) @@ \<tau>\<^sub>1) $$ z \<noteq> \<nu> $$ z \<or> ((\<omega> \<squnion> \<kappa>) @@ \<tau>\<^sub>2) $$ z \<noteq> \<kappa> $$ z" 
    proof (cases z)
      case (Rv x)
      hence "(\<omega> \<squnion> \<nu>) $$ z \<noteq> \<nu> $$ z" using neq
        by (metis Vagree_allrvars Vagree_self_sttconc_on_rvars byvar.simps(1))
      hence "(\<omega> \<squnion> \<kappa>) $$ z \<noteq> \<kappa> $$ z \<or> (Fin \<kappa> \<squnion> \<nu>) $$ z \<noteq> \<nu> $$ z" 
        by (metis state_join.elims state_join_neq)
      thus ?thesis by (metis Rv Vagree_allrvars Vagree_self_sttconc_on_rvars byvar.simps(1))
    next
      case (Tv h)
      hence coin: "stT (\<omega> \<squnion> \<nu>) h = stT \<nu> h"
        by (metis Vagree_alltvars bound_effect_on_state(2) run state_join.elims)
      hence "byrec \<tau>\<^sub>1 h \<noteq> [] \<or> byrec \<tau>\<^sub>2 h \<noteq> []"
        using Tv neq stT_sttconc_dist_access com by force
      hence "stT \<kappa> h @ byrec \<tau>\<^sub>1 h \<noteq> stT \<nu> h \<or> stT (\<omega> \<squnion> \<kappa>) h @ byrec \<tau>\<^sub>2 h \<noteq> stT \<kappa> h"
        by (metis Vagree_alltvars alpha append_self_conv bound_effect_on_state(2) run state_join.elims)
      thus ?thesis
        by (simp add: Tv stT_sttconc_dist_access)
    qed
    thus "z \<in> BVP J \<alpha> \<union> BVP J \<beta>" using eqJ BVP_elem alpha beta com by blast
  qed
qed

lemma BVP_Repeat_bound: "BVP J (Repeat \<alpha> n) \<subseteq> BVP J \<alpha>"
proof (induction n)
  case 0
  thus ?case by (simp add: BVP_test)
next
  case (Suc n)
  thus ?case by (metis BVP_compose_bound Repeat.elims Suc_inject nat.discI sup.orderE)
qed

lemma BVP_loop_bound: "BVP J (\<alpha>**) \<subseteq> BVP J \<alpha>"
proof
  fix z 
  assume "z \<in> BVP J (\<alpha>**)"
  then obtain I \<nu> \<tau> \<omega> n
    where eqJ: "\<pi>\<^sub>I I = J"
      and "(\<nu>, \<tau>, \<omega>) \<in> iterate_linhis n (chp_sem I \<alpha>)"
      and neq: "(\<omega> \<squnion> \<nu>) @@ \<tau> $$ z \<noteq> \<nu> $$ z"
    using BVP_elem chp_sem_Loop_by_iterate UN_E by metis
  hence "z \<in> BVP J (Repeat \<alpha> n)" using BVP_elem chp_sem_Repeat by auto
  thus "z \<in> BVP J \<alpha>" by (meson BVP_Repeat_bound subsetD)
qed

lemma BVP_send_other: "Tv h \<noteq> y \<Longrightarrow> y \<notin> BVP J (Send ch h \<theta>)"
proof (cases y)
  case (Rv x)
  thus ?thesis by (metis BVP_elem byvar.simps(1) send_no_state_change stR_sttconc state_join.elims)
next
  case (Tv h')
  assume "Tv h \<noteq> y"
  hence hneq: "h \<noteq> h'" using Tv by simp
  show ?thesis
  proof
    assume "y \<in> BVP J (Send ch h \<theta>)"
    then obtain I \<nu> \<tau> \<omega>
      where pref: "(\<tau>, \<omega>) \<sqsubseteq> ([mkrecevent h ch (rtrm_sem I \<theta> \<nu>) (stR \<nu> \<mu>)], Fin \<nu>)"
        and neq: "stT ((\<omega> \<squnion> \<nu>) @@ \<tau>) h' \<noteq> stT \<nu> h'"
      using BVP_def Tv by auto
    hence com: "\<tau> \<preceq> [mkrecevent h ch (rtrm_sem I \<theta> \<nu>) (stR \<nu> \<mu>)]" using pref unfolding obspref_def by auto
    have "byrec [mkrecevent h ch (rtrm_sem I \<theta> \<nu>) (stR \<nu> \<mu>)] h' \<noteq> []" 
    proof (cases \<omega>)
      case (Fin \<omega>\<^sub>0)
      then show ?thesis by (metis neq obspref_alt pref reachedstate.discI stT_sttconc_neq_iff_byrec state_join.simps(1))
    next
      case NonFin
      then show ?thesis by (metis byrec_mono_prefix com neq prefix_bot.extremum_uniqueI reachedstate.distinct(2) stT_sttconc_neq_iff_byrec state_join.elims)
    qed
    thus False using byrec_def hneq by auto
  qed
qed

lemma BVP_send: "BVP J (Send ch h \<theta>) = {Tv h}"
proof
  show "BVP J (Send ch h \<theta>) \<subseteq> {Tv h}"
    using BVP_send_other by (metis insertI1 subset_eq)
next
  fix \<nu> :: state
  obtain I :: interp where eqJ: "\<pi>\<^sub>I I = J" by (metis binterp_has_interp)
  let ?event = "[mkrecevent h ch (rtrm_sem I \<theta> \<nu>) (stR \<nu> \<mu>)]"
  have run: "(\<nu>, ?event, Fin \<nu>) \<in> chp_sem I (Send ch h \<theta>)" by (simp add: obspref_refl)
  have "\<nu> @@ ?event $$ Tv h \<noteq> \<nu> $$ Tv h" unfolding byrec_def  by (simp add: stT_sttconc_dist_access)
  from eqJ run this show "{Tv h} \<subseteq> BVP J (Send ch h \<theta>)" unfolding BVP_def by force
qed

lemma BVP_receive_other: "y \<notin> {Tv h, Rv x} \<Longrightarrow> y \<notin> BVP J (Receive ch h x)"
proof
  assume nin: "y \<notin> {Tv h, Rv x}" and inBVP: "y \<in> BVP J (Receive ch h x)"
  show False
  proof (cases y)
    case (Rv x')
    hence xneq: "x' \<noteq> x" and "Rv x' \<in> BVP J (Receive ch h x)" using nin inBVP by auto

    then obtain \<nu> \<tau> \<omega> r
      where pref: "(\<tau>, \<omega>) \<sqsubseteq> ([mkrecevent h ch r (stR \<nu> \<mu>)], Fin (rrepv \<nu> x r))"
        and neq: "stR ((\<omega> \<squnion> \<nu>) @@ \<tau>) x' \<noteq> stR \<nu> x'"
      unfolding BVP_def by auto
    then obtain \<omega>\<^sub>0 where rrepv: "\<omega> = Fin \<omega>\<^sub>0 \<and> \<omega>\<^sub>0 = rrepv \<nu> x r" 
      by (metis obspref_alt stR_sttconc state_join.simps(2))
    hence "stR \<omega>\<^sub>0 x' \<noteq> stR \<nu> x'" using neq unfolding sttconc_def by simp
    hence "stR (rrepv \<nu> x r) x' \<noteq> stR \<nu> x'" using rrepv by simp
    thus False unfolding rrepv_def fun_upd_def using xneq by simp
  next
    case (Tv h')
    hence hneq: "h' \<noteq> h" and "Tv h' \<in> BVP J (Receive ch h x)" using nin inBVP by auto

    then obtain \<nu> \<tau> \<omega> r
      where pref: "(\<tau>, \<omega>) \<sqsubseteq> ([mkrecevent h ch r (stR \<nu> \<mu>)], Fin (rrepv \<nu> x r))"
        and neq: "stT ((\<omega> \<squnion> \<nu>) @@ \<tau>) h' \<noteq> stT \<nu> h'"
      unfolding BVP_def by auto
    hence com: "\<tau> \<preceq> [mkrecevent h ch r (stR \<nu> \<mu>)]" using pref unfolding obspref_def by auto
    have "byrec [mkrecevent h ch r (stR \<nu> \<mu>)] h' \<noteq> []" 
    proof (cases \<omega>)
      case (Fin \<omega>\<^sub>0)
      hence "stT (\<omega>\<^sub>0 @@ \<tau>) h' \<noteq> stT \<nu> h'" using neq by auto
      moreover have "stT \<omega>\<^sub>0 = stT \<nu>" using pref Fin by (simp add: obspref_alt)
      ultimately show ?thesis using Fin pref by (simp add: stT_sttconc_dist_access obspref_alt)
    next
      case NonFin
      hence "stT (\<nu> @@ \<tau>) h' \<noteq> stT \<nu> h'" using neq by auto
      then show ?thesis using NonFin pref apply (simp add: stT_sttconc_dist_access obspref_alt)
        by (metis byrec_mono_prefix prefix_bot.extremum_unique)
    qed
    thus False using byrec_def hneq by auto
  qed
qed

lemma BVP_receive: "BVP J (Receive ch h x) = {Tv h, Rv x}"
proof
  show "BVP J (Receive ch h x) \<subseteq> {Tv h, Rv x}" using BVP_receive_other by blast
next
  from binterp_has_interp obtain I :: interp where eqJ: "\<pi>\<^sub>I I = J" by metis
  fix \<nu> :: state
  let ?r = "stR \<nu> x + 1"
  let ?\<tau> = "[mkrecevent h ch ?r (stR \<nu> \<mu>)]"
  let ?\<omega> = "rrepv \<nu> x ?r"
  have run: "(\<nu>, ?\<tau>, Fin ?\<omega>) \<in> chp_sem I (Receive ch h x)" using obspref_refl by auto
  moreover have "?\<omega> @@ ?\<tau> $$ Rv x \<noteq> \<nu> $$ Rv x" unfolding sttconc_def by simp
  ultimately have x_in_BVP: "Rv x \<in> BVP J (Receive ch h x)" using eqJ BVP_def by fastforce

  hence "?\<omega> @@ ?\<tau> $$ Tv h \<noteq> \<nu> $$ Tv h" unfolding sttconc_def  rrepv_def by simp
  hence h_in_BVP: "Tv h \<in> BVP J (Receive ch h x)" using run eqJ BVP_def by fastforce

  from h_in_BVP x_in_BVP show "{Tv h, Rv x} \<subseteq> BVP J (Receive ch h x)" by simp
qed

lemma ini_fin_Rv_rm_join: "((\<omega> \<squnion> \<nu>) @@ \<tau>) $$ z \<noteq> \<nu> $$ z \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> isRv z \<Longrightarrow> ((gets \<omega>) @@ \<tau>) $$ z \<noteq> \<nu> $$ z"
  apply (cases z)
  using ini_neq_fin_conv state_join_neq_conv by auto

lemma lmergebot_conv: "\<omega> = lmergebot \<omega>\<^sub>1 \<omega>\<^sub>2 X \<Longrightarrow> \<omega> \<noteq> NonFin \<Longrightarrow> gets \<omega> = lmerge (gets \<omega>\<^sub>1) (gets \<omega>\<^sub>2) X"
  apply (cases "\<omega>\<^sub>1 = NonFin \<or> \<omega>\<^sub>2 = NonFin")
  apply auto
  by (metis lmergebot_fin reachedstate.exhaust_sel)




lemma BVP_par_bound: "BVP J (\<alpha> par \<beta>) \<subseteq> BVP J \<alpha> \<union> BVP J \<beta>"
proof
  fix z
  assume "z \<in> BVP J (\<alpha> par \<beta>)"
  then obtain I \<nu> \<tau> \<omega> where eqJ: "J = \<pi>\<^sub>I I" and par_run: "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I (\<alpha> par \<beta>)" 
    and neq: "((\<omega> \<squnion> \<nu>) @@ \<tau>) $$ z \<noteq> \<nu> $$ z" using BVP_elem by metis
  then obtain \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta>
    where alpha: "(\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha>), \<omega>\<^sub>\<alpha>) \<in> chp_sem I \<alpha>"
      and beta:  "(\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<beta>), \<omega>\<^sub>\<beta>) \<in> chp_sem I \<beta>"
      and merge: "\<omega> = lmergebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> (BVP (\<pi>\<^sub>I I) \<alpha>)"
      and nojunk: "\<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha> \<union> CN (\<pi>\<^sub>I I) \<beta>) = \<tau>"
    by blast

  let ?\<tau>\<^sub>\<alpha> = "\<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha>)"
  let ?\<tau>\<^sub>\<beta> = "\<tau> \<down> (CN (\<pi>\<^sub>I I) \<beta>)"

  show "z \<in> BVP J \<alpha> \<union> BVP J \<beta>"
  proof (cases z)
    case (Rv x)
    hence fin: "\<omega> \<noteq> NonFin" using neq by auto
    hence "(gets \<omega>) @@ \<tau> $$ z \<noteq> \<nu> $$ z" using neq Rv ini_fin_Rv_rm_join par_run by blast
    hence xneq: "(gets \<omega>) $$ z \<noteq> \<nu> $$ z" using Rv by auto 
    show ?thesis
    proof (cases "z \<in> BVP (\<pi>\<^sub>I I) \<alpha>")
      case True
      then show ?thesis using eqJ by force
    next
      case False
      have "Vagree (gets \<omega>) (gets \<omega>\<^sub>\<beta>) (-BVP (\<pi>\<^sub>I I) \<alpha>)"
        using merge Vagreebot_only_Fin lmerge_vagree lmergebot_conv fin by blast
      moreover have "\<omega>\<^sub>\<beta> \<noteq> NonFin" using fin merge by auto
      ultimately show ?thesis using Vagree_def False beta bound_effect_property_short eqJ xneq
        by (metis (no_types, lifting) mem_simps(5) reachedstate.exhaust_sel unfold_simps(1))
    qed
  next
    case (Tv h)
    hence "stT (\<omega> \<squnion> \<nu>) h = stT \<nu> h" using bound_effect_on_state_NonFin par_run
      by (metis (no_types, lifting) Vagree_alltvars)
    hence "byrec \<tau> h \<noteq> []" using neq Tv
      by (simp add: stT_sttconc_dist_access)
    hence "{\<rho> \<in> set \<tau>. recvar \<rho> = h} \<noteq> {}" using byrec_def by fastforce
    then obtain \<rho>
      where in_trace: "\<rho> \<in> set \<tau>"
        and var_h: "recvar \<rho> = h"
      by auto
    hence "\<rho> \<in> set ?\<tau>\<^sub>\<alpha> \<union> set ?\<tau>\<^sub>\<beta>" using nojunk events_tfilter_union by metis
    thus ?thesis
    proof
      assume "\<rho> \<in> set ?\<tau>\<^sub>\<alpha>"
      hence "byrec ?\<tau>\<^sub>\<alpha> h \<noteq> []" using var_h byrec_def
        by (metis (mono_tags, lifting) addrec_empty addrec_urec_tflat
            empty_filter_conv filter_True filter_set
            member_filter)
      hence "(\<omega>\<^sub>\<alpha> \<squnion> \<nu>) @@ ?\<tau>\<^sub>\<alpha> $$ z \<noteq> (\<omega>\<^sub>\<alpha> \<squnion> \<nu>) $$ z" using Tv by (simp add: stT_sttconc_dist_access)
      hence "(\<omega>\<^sub>\<alpha> \<squnion> \<nu>) @@ ?\<tau>\<^sub>\<alpha> $$ z \<noteq> \<nu> $$ z" using alpha Tv ini_eq_fin by simp
      hence "z \<in> BVP J \<alpha>" using alpha BVP_elem eqJ by auto
      thus "z \<in> BVP J \<alpha> \<union> BVP J \<beta>" by simp
    next
      assume "\<rho> \<in> set ?\<tau>\<^sub>\<beta>"
      hence "byrec ?\<tau>\<^sub>\<beta> h \<noteq> []" using var_h byrec_def
        by (metis (mono_tags, lifting) addrec_empty addrec_urec_tflat
            empty_filter_conv filter_True filter_set
            member_filter)
      hence "(\<omega>\<^sub>\<beta> \<squnion> \<nu>) @@ ?\<tau>\<^sub>\<beta> $$ z \<noteq> (\<omega>\<^sub>\<beta> \<squnion> \<nu>) $$ z" using Tv by (simp add: stT_sttconc_dist_access)
      hence "(\<omega>\<^sub>\<beta> \<squnion> \<nu>) @@ ?\<tau>\<^sub>\<beta> $$ z \<noteq> \<nu> $$ z" using beta Tv ini_eq_fin by simp
      hence "z \<in> BVP J \<beta>" using beta BVP_elem eqJ by auto
      thus "z \<in> BVP J \<alpha> \<union> BVP J \<beta>" by simp
    qed
  qed
qed


lemma CNP_Chp_bound: "CNP J (Chp a Z Y) \<subseteq> UNIV \<times> (cspace_sem J Y)" 
  using CNP_Chp by blast

lemma CNP_assign [simp]: "CNP J (x := \<theta>) = {}"
  apply (rule nocom_no_chans) by auto

lemma CNP_nondet [simp]: "CNP J (x := *) = {}"
  apply (rule nocom_no_chans) by auto

lemma CNP_choice_bound: "CNP J (\<alpha> \<union>\<union> \<beta>) \<subseteq> CNP J \<alpha> \<union> CNP J \<beta>"
  unfolding CNP_def by fastforce

lemma tfilter_byrec_hd_not_in [simp]: "recvar \<rho> = h \<Longrightarrow> along \<rho> \<notin> C \<Longrightarrow> byrec (\<rho> # \<tau>) h \<down> C = byrec \<tau> h \<down> C"
  by (simp add: tfilter_def tflat_def)

lemma CNP_send [simp]: "CNP J (Send ch h \<theta>) = { (h, ch) }"
proof
  show "CNP J (Send ch h \<theta>) \<subseteq> {(h, ch)}"
  proof (rule subrelI)
    fix h\<^sub>0 dh
    assume "(h\<^sub>0, dh) \<in> CNP J (Send ch h \<theta>)"  
    then obtain I \<nu> \<tau> \<omega>
    where "J = \<pi>\<^sub>I I"
      and "(\<tau>, \<omega>) \<sqsubseteq> ([mkrecevent h ch (rtrm_sem I \<theta> \<nu>) (stR \<nu> \<mu>)], Fin \<nu>)"
      and has_dh: "byrec \<tau> h\<^sub>0 \<down> {dh} \<noteq> []" using CNP_def by auto
    hence "\<tau> \<preceq> [mkrecevent h ch (rtrm_sem I \<theta> \<nu>) (stR \<nu> \<mu>)]" and "\<tau> \<noteq> []" unfolding obspref_def by auto
    hence "\<tau> = [mkrecevent h ch (rtrm_sem I \<theta> \<nu>) (stR \<nu> \<mu>)]" by (simp add: prefix_Cons)
    thus "(h\<^sub>0, dh) \<in> { (h, ch) }" using has_dh   
      apply (cases "h = h\<^sub>0")
      apply (metis along_mkevent byrec_mkevent_success singleton_iff tfilter_empty tfilter_hd_not_in)
      by simp
  qed
next
  fix \<nu> :: state
  obtain I :: interp where eqJ: "J = \<pi>\<^sub>I I" using binterp_has_interp by blast

  let ?\<tau> = "[mkrecevent h ch (rtrm_sem I \<theta> \<nu>) (stR \<nu> \<mu>)]"

  have "(\<nu>, ?\<tau>, Fin \<nu>) \<in> chp_sem I (Send ch h \<theta>)" using obspref_refl by auto
  moreover have "byrec ?\<tau> h \<down> {ch} \<noteq> []" unfolding tfilter_def by simp
  ultimately have "(h, ch) \<in> CNP J (Send ch h \<theta>)" unfolding CNP_def using eqJ by blast
  thus "{ (h, ch) } \<subseteq> CNP J (Send ch h \<theta>)" by simp
qed

lemma CNP_receive [simp]: "CNP J (Receive ch h x) = {(h, ch)}"
proof
  show "CNP J (Receive ch h x) \<subseteq> {(h, ch)}"
  proof (rule subrelI)
    fix h\<^sub>0 dh
    assume "(h\<^sub>0, dh) \<in> CNP J (Receive ch h x)"
    then obtain I \<nu> \<tau> \<omega> r
      where "J = \<pi>\<^sub>I (I :: interp)"
        and "(\<tau>, \<omega>) \<sqsubseteq> ([mkrecevent h ch r (stR \<nu> \<mu>)], Fin (rrepv \<nu> x r))"
        and has_dh: "byrec \<tau> h\<^sub>0 \<down> {dh} \<noteq> []" using CNP_def by auto
    hence "\<tau> \<preceq> [mkrecevent h ch r (stR \<nu> \<mu>)]" and "\<tau> \<noteq> []" unfolding obspref_def by auto
    hence "\<tau> = [mkrecevent h ch r (stR \<nu> \<mu>)]" by (simp add: prefix_Cons)
    thus "(h\<^sub>0, dh) \<in> {(h, ch)}" using has_dh   
      apply (cases "h = h\<^sub>0")
      apply (metis along_mkevent byrec_mkevent_success singleton_iff tfilter_empty tfilter_hd_not_in)
      by simp
  qed
next
  fix \<nu> :: state
  fix x :: rvar
  fix r :: real
  obtain I :: interp where eqJ: "J = \<pi>\<^sub>I I" using binterp_has_interp by blast

  let "(?\<tau>, ?\<omega>)" = "([mkrecevent h ch r (stR \<nu> \<mu>)], Fin (rrepv \<nu> x r))"

  have "(\<nu>, ?\<tau>, ?\<omega>) \<in> chp_sem I (Receive ch h x)" using obspref_refl by auto
  moreover have "byrec ?\<tau> h \<down> {ch} \<noteq> []" unfolding tfilter_def by simp
  ultimately have "(h, ch) \<in> CNP J (Receive ch h x)" unfolding CNP_def using eqJ by blast
  thus "{ (h, ch) } \<subseteq> CNP J (Receive ch h x)" by simp
qed

lemma CNP_compose_bound: "CNP J (\<alpha> ;; \<beta>) \<subseteq> CNP J \<alpha> \<union> CNP J \<beta>"
proof (rule subrelI)
  fix h ch
  assume "(h, ch) \<in> CNP J (\<alpha> ;; \<beta>)"
  term compose
  then obtain I \<nu> \<tau> \<omega>
    where "J = \<pi>\<^sub>I I \<and> (\<nu>, \<tau>, \<omega>) \<in> compose (chp_sem I \<alpha>) (chp_sem I \<beta>) \<and> byrec \<tau> h \<down> {ch} \<noteq> []"
    using CNP_def by fastforce
  hence eqJ: "J = \<pi>\<^sub>I I"
      and run: "(\<nu>, \<tau>, \<omega>) \<in> compose (chp_sem I \<alpha>) (chp_sem I \<beta>)"
      and has_ch: "byrec \<tau> h \<down> {ch} \<noteq> []"
    by auto

  show "(h, ch) \<in> CNP J \<alpha> \<union> CNP J \<beta>"
  proof (cases "(\<nu>, \<tau>, \<omega>) \<in> botop (chp_sem I \<alpha>)")
    case True
    then obtain \<omega>' where "(\<nu>, \<tau>, \<omega>') \<in> chp_sem I \<alpha>" by auto
    then show ?thesis using eqJ has_ch CNP_def by auto
  next
    case False
    hence "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<triangleright> chp_sem I \<beta>" using run by auto
    then obtain \<kappa> \<tau>\<^sub>1 \<tau>\<^sub>2
      where "\<tau> = \<tau>\<^sub>1 @ \<tau>\<^sub>2"
        and alpha: "(\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> chp_sem I \<alpha>"
        and beta: "(\<kappa>, \<tau>\<^sub>2, \<omega>) \<in> chp_sem I \<beta>"
      by auto
    hence "byrec \<tau>\<^sub>1 h \<down> {ch} \<noteq> [] \<or> byrec \<tau>\<^sub>2 h \<down> {ch} \<noteq> []" using has_ch by simp
    then show ?thesis using eqJ alpha beta CNP_def by blast
  qed
qed

lemma CNP_test [simp]: "CNP J (? P) = {}"
  unfolding CNP_def by auto

lemma CNP_delay [simp]: "CNP J (Evolution x \<theta> \<phi>) = {}"
  unfolding CNP_def by auto

lemma CNP_repeat_bound: "CNP J (Repeat \<alpha> n) \<subseteq> CNP J \<alpha>"
proof (induction n)
  case 0
  then show ?case unfolding CNP_def by auto
next
  case (Suc n)
  then show ?case using CNP_compose_bound by (metis Repeat.simps(2) sup.absorb_iff1)
qed

lemma CNP_loop_bound: "CNP J \<alpha>** \<subseteq> CNP J \<alpha>"
proof (rule subrelI)
  fix h ch
  assume "(h, ch) \<in> CNP J (\<alpha>**)"
  then obtain I \<nu> \<tau> \<omega> n
    where "\<pi>\<^sub>I I = J"
      and "(\<nu>, \<tau>, \<omega>) \<in> iterate_linhis n (chp_sem I \<alpha>)"
      and "byrec \<tau> h \<down> {ch} \<noteq> []"
    using CNP_def chp_sem_Loop_by_iterate UN_E by auto
  hence "(h, ch) \<in> CNP J (Repeat \<alpha> n)" using CNP_def chp_sem_Repeat by auto
  thus "(h, ch) \<in> CNP J \<alpha>" by (meson CNP_repeat_bound subsetD)
qed

lemma CNP_par_bound: "CNP J (\<alpha> par \<beta>) \<subseteq> CNP J \<alpha> \<union> CNP J \<beta>"
proof (rule subrelI)
  fix h ch
  assume "(h, ch) \<in> CNP J (\<alpha> par \<beta>)"
  then obtain I \<nu> \<tau> \<omega>
    where eqJ: "J = \<pi>\<^sub>I I"
      and "(\<nu>, \<tau>, \<omega>) \<in> chp_sem I (\<alpha> par \<beta>)" 
      and has_ch: "byrec \<tau> h \<down> {ch} \<noteq> []"
    unfolding CNP_def by fastforce
  then obtain \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta>
    where alpha: "(\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha>), \<omega>\<^sub>\<alpha>) \<in> chp_sem I \<alpha>"
      and beta:  "(\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<beta>), \<omega>\<^sub>\<beta>) \<in> chp_sem I \<beta>"
      and no_junk: "\<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha> \<union> CN (\<pi>\<^sub>I I) \<beta>) = \<tau>"
    using chp_sem_par_fin by blast

  let ?\<tau>\<^sub>\<alpha> = "\<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha>)"
  let ?\<tau>\<^sub>\<beta> = "\<tau> \<down> (CN (\<pi>\<^sub>I I) \<beta>)"

  from has_ch have "{\<rho> \<in> set (byrec \<tau> h). along \<rho> = ch} \<noteq> {}" unfolding tfilter_def by force
  then obtain \<rho> where "\<rho> \<in> set (byrec \<tau> h)" and eq_ch: "along \<rho> = ch" by auto
  hence "\<rho> \<in> set (byrec ?\<tau>\<^sub>\<alpha> h) \<union> set (byrec ?\<tau>\<^sub>\<beta> h)" 
    using no_junk by (metis byrec_tfilter_commute events_tfilter_union)
  thus "(h, ch) \<in> CNP J \<alpha> \<union> CNP J \<beta>"
  proof
    assume "\<rho> \<in> set (byrec ?\<tau>\<^sub>\<alpha> h)"
    hence "\<rho> \<in> set ((byrec ?\<tau>\<^sub>\<alpha> h) \<down> {ch})" using eq_ch by (simp add: byrec_def tfilter_def)
    hence "byrec ?\<tau>\<^sub>\<alpha> h \<down> {ch} \<noteq> []" by force
    thus ?thesis using CNP_def eqJ alpha by blast
  next
    assume "\<rho> \<in> set (byrec ?\<tau>\<^sub>\<beta> h)"
    hence "\<rho> \<in> set ((byrec ?\<tau>\<^sub>\<beta> h) \<down> {ch})" using eq_ch by (simp add: byrec_def tfilter_def)
    hence "byrec ?\<tau>\<^sub>\<beta> h \<down> {ch} \<noteq> []" by force
    thus ?thesis using CNP_def eqJ beta by blast
  qed
qed

lemma BNP_choice_bound: "z \<in> BNP J (\<alpha> \<union>\<union> \<beta>) \<Longrightarrow> z \<in> BNP J \<alpha> \<union> BNP J \<beta>"
  apply (cases z)
   apply (simp_all add: BNP_def) 
  using BVP_choice_bound CNP_choice_bound by blast+

lemma BNP_compose_bound: "z \<in> BNP J (\<alpha> ;; \<beta>) \<Longrightarrow> z \<in> BNP J \<alpha> \<union> BNP J \<beta>"
  apply (cases z)
   apply (simp_all add: BNP_partition) 
  using BVP_compose_bound CNP_compose_bound by blast+

lemma BNP_loop_bound: "z \<in> BNP J \<alpha>** \<Longrightarrow> z \<in> BNP J \<alpha>"
  apply (cases z)
   apply (simp_all add: BNP_partition) 
  using BVP_loop_bound CNP_loop_bound by blast+

lemma BNP_par_bound: "z \<in> BNP J (\<alpha> par \<beta>) \<Longrightarrow> z \<in> BNP J \<alpha> \<union> BNP J \<beta>"
  apply (cases z)
   apply (simp_all add: BNP_partition) 
  using BVP_par_bound CNP_par_bound by blast+



subsection \<open>Corollaries of the Coincidence Properties\<close>


definition communicatively_wf :: "binterp \<Rightarrow> fml \<Rightarrow> chp \<Rightarrow> bool"
  where "communicatively_wf J \<phi> \<alpha> \<longleftrightarrow> FVE J \<phi> \<inter> (BVP J \<alpha> \<union> \<V>\<^sub>\<mu>) \<subseteq> \<iota>\<^sub>T \<V>\<^sub>T"

text \<open>Corollary 16 of \<open>https://arxiv.org/abs/2408.05012\<close>\<close>
corollary communicative_coincidence: 
  assumes wf: "communicatively_wf (\<pi>\<^sub>I I) \<phi> \<alpha>"
  assumes run: "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha>"
  shows "Vagree \<nu> \<omega> (FVE (\<pi>\<^sub>I I) \<phi>)"
    and "\<nu> @@ \<tau>' \<in> fml_sem I \<phi> \<longleftrightarrow> \<omega> @@ \<tau>' \<in> fml_sem I \<phi>"
proof -
  have "Vagree \<nu> \<omega> (-BVP (\<pi>\<^sub>I I) \<alpha>)" using run bound_effect_property_short by presburger
  moreover have "Vagree \<nu> \<omega> (\<iota>\<^sub>T \<V>\<^sub>T)" using Vagree_and run bound_effect_on_state by blast
  moreover have "FVE (\<pi>\<^sub>I I) \<phi> \<subseteq> -(BVP (\<pi>\<^sub>I I) \<alpha>) \<union> \<iota>\<^sub>T \<V>\<^sub>T" using communicatively_wf_def local.wf by auto
  ultimately show "Vagree \<nu> \<omega> (FVE (\<pi>\<^sub>I I) \<phi>)" by (meson Vagree_antimon Vagree_union)
  thus "\<nu> @@ \<tau>' \<in> fml_sem I \<phi> \<longleftrightarrow> \<omega> @@ \<tau>' \<in> fml_sem I \<phi>" 
    using coincidence_fml_FVE Vagree_and Vagree_sttconc_cong by blast
qed

text \<open>Part of Corollary 15 of \<open>https://arxiv.org/abs/2408.05012\<close>\<close>
lemma add_initial_communication_fin:
  assumes wf: "wf_chp \<L> \<alpha>"
  assumes run: "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha>"
  shows "(\<nu> @@ \<tau>\<^sub>0, \<tau>, Fin (\<omega> @@ \<tau>\<^sub>0)) \<in> chp_sem I \<alpha>"
proof -
  obtain \<omega>' where newrun: "(\<nu> @@ \<tau>\<^sub>0, \<tau>, Fin \<omega>') \<in> chp_sem I \<alpha> \<and> Vagree \<omega> \<omega>' (\<iota>\<^sub>R \<V>\<^sub>R)"
    using Vagree_self_sttconc_on_rvars coincidence_chp_fin local.wf run FVP_bound_rvars by blast
  hence "stT \<omega>' = stT (\<omega> @@ \<tau>\<^sub>0)" by (metis Vagree_alltvars Vagree_sttconc_cong bound_effect_on_state(2) run)
  moreover have "stR \<omega>' = stR (\<omega> @@ \<tau>\<^sub>0)" using Vagree_allrvars Vagree_sttconc_on_rvars Vagree_sym newrun by blast
  ultimately show ?thesis using state_eq_by_sortI newrun by blast
qed

lemma add_initial_communication: 
  "wf_chp \<L> \<alpha> \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> \<exists>\<omega>'. (\<nu> @@ \<tau>\<^sub>0, \<tau>, \<omega>') \<in> chp_sem I \<alpha>"
  by (meson Vagree_self_sttconc_on_rvars coincidence_chp FVP_bound_rvars)

lemma add_initial_com_nonfin: 
  "wf_chp \<L> \<alpha> \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> (\<nu> @@ \<tau>\<^sub>0, \<tau>, NonFin) \<in> chp_sem I \<alpha>"
  by (meson add_initial_communication chp_sem_total_and_pc obspref_nonfin pc.cases)



lemma remove_initial_com_fin:
  assumes wf: "wf_chp \<L> \<alpha>" 
  assumes run: "(\<nu> @@ \<tau>\<^sub>0, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha>"
  shows "(\<nu>, \<tau>, Fin (stt_rmsuffix \<tau>\<^sub>0 \<omega>)) \<in> chp_sem I \<alpha>"
proof -
  have "Vagree (\<nu> @@ \<tau>\<^sub>0) \<nu> (\<iota>\<^sub>R \<V>\<^sub>R)" using Vagree_self_sttconc_on_rvars Vagree_sym_rel by blast
  then obtain \<omega>' where newrun: "(\<nu>, \<tau>, Fin \<omega>') \<in> chp_sem I \<alpha> \<and> Vagree \<omega> \<omega>' (\<iota>\<^sub>R \<V>\<^sub>R)"
    using coincidence_chp_fin local.wf run FVP_bound_rvars by metis
  moreover have "stt_rmsuffix \<tau>\<^sub>0 \<omega> = \<omega>'"
  proof -
    have "stT \<omega> = stT (\<nu> @@ \<tau>\<^sub>0)" by (metis Vagree_alltvars bound_effect_on_state(2) run)
    moreover have "stT \<omega>' = stT \<nu>" by (metis Vagree_alltvars newrun bound_effect_on_state(2))
    ultimately have "stT (stt_rmsuffix \<tau>\<^sub>0 \<omega>) = stT \<omega>'" using stT_stt_rmsuffix_correct stt_rmsuffix_def by force
    moreover have "stR (stt_rmsuffix \<tau>\<^sub>0 \<omega>) = stR \<omega>'" using newrun Vagree_allrvars stR_stt_rmsuffix by metis
    ultimately show ?thesis using state_eq_by_sortI by blast
  qed
  ultimately show ?thesis by force
qed

lemma remove_initial_communication:
  assumes wf: "wf_chp \<L> \<alpha>" 
  assumes run: "(\<nu> @@ \<tau>\<^sub>0, \<tau>, \<omega>) \<in> chp_sem I \<alpha>"
  shows "(\<nu>, \<tau>, botify (stt_rmsuffix \<tau>\<^sub>0) \<omega>) \<in> chp_sem I \<alpha>"
proof (cases \<omega>)
  case (Fin x1)
  then show ?thesis using local.wf remove_initial_com_fin run by force
next
  case NonFin
  have "Vagree (\<nu> @@ \<tau>\<^sub>0) \<nu> (\<iota>\<^sub>R \<V>\<^sub>R)" using Vagree_self_sttconc_on_rvars Vagree_sym_rel by blast
  then obtain \<omega>' where newrun: "(\<nu>, \<tau>, NonFin) \<in> chp_sem I \<alpha> \<and> Vagreebot \<omega> \<omega>' (\<iota>\<^sub>R \<V>\<^sub>R)"
    using coincidence_chp run local.wf FVP_bound_rvars by (metis add_initial_com_nonfin sttconc_empty)
  then show ?thesis using NonFin botify.simps(1) by presburger
qed

lemma suffix_of_initial_is_suffix_of_final: 
  assumes "(\<kappa> @@ \<tau>\<^sub>1, \<tau>\<^sub>2, Fin \<omega>) \<in> chp_sem I \<alpha>"
  shows "is_stt_suffix \<omega> \<tau>\<^sub>1"
proof -
  have 0: "Vagree (\<kappa> @@ \<tau>\<^sub>1) \<omega> (\<iota>\<^sub>T \<V>\<^sub>T)" using assms bound_effect_on_state by blast
  hence "\<And>h. (stT (\<kappa> @@ \<tau>\<^sub>1))(h) = (stT \<omega>)(h)" using Vagree_alltvars by metis
  hence "\<And>h. stT \<omega> h = (stT \<kappa>)(h) @ byrec \<tau>\<^sub>1 h" using sttconc_def by simp
  thus "is_stt_suffix \<omega> \<tau>\<^sub>1" unfolding is_stt_suffix_def by simp
qed 



subsection \<open>Sound Static Semantics\<close>

fun FNE\<^sub>0 :: "binterp \<Rightarrow> expr \<Rightarrow> bindr set"
  where
  "FNE\<^sub>0 J (Ertrm \<theta>) = FNE J \<theta>"
| "FNE\<^sub>0 J (Ettrm te) = FNE J te"
| "FNE\<^sub>0 J (Efml \<phi>) = FNE J \<phi>"
| "FNE\<^sub>0 J (Earg e) = FNE J e"


definition sem_stat_sem :: "binterp \<Rightarrow> stat_sem" ("\<L>\<^sub>0")
  where "sem_stat_sem \<equiv> \<lambda>J. \<lparr> FNE\<^sub>\<L> = FNE\<^sub>0 J, BNP\<^sub>\<L> = BNP J,
    FVP\<^sub>\<L> = FVP J, CNC\<^sub>\<L> = CNC J, UACN\<^sub>\<L> = CNC J, FVV\<^sub>\<L> = FVV J, UAV\<^sub>\<L> = FVV J \<rparr>"
                                                        
text \<open>A static semantics stays correct when it approximates the free and bound variabels, i.e. if
\<open>\<L>\<^sub>1 \<sqsubseteq>\<^sub>\<L> \<L>\<^sub>2\<close>, then \<open>\<L>\<^sub>2\<close> is a sound static semantics if \<open>\<L>\<^sub>1\<close> is.\<close>
definition stat_sem_porder :: "stat_sem \<Rightarrow> stat_sem \<Rightarrow> bool" (infixr "\<sqsubseteq>\<^sub>\<L>" 75)
  where "stat_sem_porder \<L>\<^sub>1 \<L>\<^sub>2 = ((\<forall>e. FNE\<^sub>\<L> \<L>\<^sub>1 e \<subseteq> FNE\<^sub>\<L> \<L>\<^sub>2 e) 
    \<and> (\<forall>\<alpha>. BNP\<^sub>\<L> \<L>\<^sub>1 \<alpha> \<subseteq> BNP\<^sub>\<L> \<L>\<^sub>2 \<alpha> \<and> FVP\<^sub>\<L> \<L>\<^sub>1 \<alpha> \<subseteq> FVP\<^sub>\<L> \<L>\<^sub>2 \<alpha>) 
    \<and> (\<forall>Y. UACN\<^sub>\<L> \<L>\<^sub>1 Y \<supseteq> UACN\<^sub>\<L> \<L>\<^sub>2 Y) \<and> (\<forall>Y. CNC\<^sub>\<L> \<L>\<^sub>1 Y \<subseteq> CNC\<^sub>\<L> \<L>\<^sub>2 Y) 
    \<and> (\<forall>Z. FVV\<^sub>\<L> \<L>\<^sub>1 Z \<supseteq> FVV\<^sub>\<L> \<L>\<^sub>2 Z) \<and> (\<forall>Z. UAV\<^sub>\<L> \<L>\<^sub>1 Z \<supseteq> UAV\<^sub>\<L> \<L>\<^sub>2 Z))"

text \<open>Algebraic soundness of the static semantics ensures that bound variables and written channels
are no overestimated beyond the syntactical occurrences of variables and channels. This is necessary
for soundness of the output taboo computation of uniform substitution.\<close>
definition algebraically_sound :: "stat_sem \<Rightarrow> bool"
  where "algebraically_sound \<L> = 
   ((\<forall>x \<theta>. BNP\<^sub>\<L> \<L> (x := \<theta>) \<subseteq> {Bv (Rv x)}) 
      \<and> (\<forall>x. BNP\<^sub>\<L> \<L> (x := *) \<subseteq> {Bv (Rv x)})
      \<and> (\<forall>\<phi>. BNP\<^sub>\<L> \<L> (? \<phi>) \<subseteq> {})
      \<and> (\<forall>x \<theta> \<phi>. BNP\<^sub>\<L> \<L> (Evolution x \<theta> \<phi>) \<subseteq> \<iota>\<^sub>V (bvrident x))
      \<and> (\<forall>\<alpha> \<beta>. BNP\<^sub>\<L> \<L> (\<alpha> \<union>\<union> \<beta>) \<subseteq> BNP\<^sub>\<L> \<L> \<alpha> \<union> BNP\<^sub>\<L> \<L> \<beta>)
      \<and> (\<forall>\<alpha> \<beta>. BNP\<^sub>\<L> \<L> (\<alpha> ;; \<beta>) \<subseteq> BNP\<^sub>\<L> \<L> \<alpha> \<union> BNP\<^sub>\<L> \<L> \<beta>)
      \<and> (\<forall>\<alpha>. BNP\<^sub>\<L> \<L> (Loop \<alpha>) \<subseteq> BNP\<^sub>\<L> \<L> \<alpha>)
      \<and> (\<forall>ch h \<theta>. BNP\<^sub>\<L> \<L> (Send ch h \<theta>) \<subseteq> {Bv (Tv h), Bc h ch})
      \<and> (\<forall>ch h x. BNP\<^sub>\<L> \<L> (Receive ch h x) \<subseteq> {Bv (Tv h), Bv (Rv x), Bc h ch})
      \<and> (\<forall>\<alpha> \<beta>. BNP\<^sub>\<L> \<L> (\<alpha> par \<beta>) \<subseteq> BNP\<^sub>\<L> \<L> \<alpha> \<union> BNP\<^sub>\<L> \<L> \<beta>))"

lemma BVP\<^sub>\<L>_simps: 
  assumes "algebraically_sound \<L>"
    shows "BVP\<^sub>\<L> \<L> (x := \<theta>) \<subseteq> {Rv x}"
      and "BVP\<^sub>\<L> \<L> (x := *) \<subseteq> {Rv x}"
  using assms unfolding algebraically_sound_def BVP\<^sub>\<L>_def pi_vars_def by auto

lemma static_semantics_sem_stat_sem [simp]: 
  shows "FNE\<^sub>\<L> (\<L>\<^sub>0 J) (Ertrm \<theta>) = FNE J \<theta>"
    and "FNE\<^sub>\<L> (\<L>\<^sub>0 J) (Ettrm te) = FNE J te"
    and "FNE\<^sub>\<L> (\<L>\<^sub>0 J) (Efml \<phi>) = FNE J \<phi>"
    and "BNP\<^sub>\<L> (\<L>\<^sub>0 J) \<alpha> = BNP J \<alpha>"
    and "UAV\<^sub>\<L> (\<L>\<^sub>0 J) Z = FVV J Z"  
    and "FVP\<^sub>\<L> (\<L>\<^sub>0 J) \<alpha> = FVP J \<alpha>"
  by (simp_all add: sem_stat_sem_def)

lemma BNP_sem_stat_sem [simp]: "BVP\<^sub>\<L> (\<L>\<^sub>0 J) \<alpha> = BVP J \<alpha>"
  using static_semantics_sem_stat_sem unfolding BNP_partition BVP\<^sub>\<L>_def by simp

text \<open>A static semantics is sound for uniform substitution if it over-approximates the denotational
static semantics but does not over-approximate arbitrarily.\<close> 
definition is_sound_stat_sem :: "stat_sem \<Rightarrow> bool"
  where "is_sound_stat_sem \<L> = (\<forall>I. \<L>\<^sub>0 I \<sqsubseteq>\<^sub>\<L> \<L> \<and> algebraically_sound \<L>)"

end