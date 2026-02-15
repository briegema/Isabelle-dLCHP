theory "Domain" 
imports
  "HOL-Analysis.Derivative"
  "Identifiers"
  "HOL-Library.Sublist"
  Lib
begin

section \<open>Domain of Computation\<close>

text \<open>This section defines the computational domain of a linear history semantics.
Every program denotes a set of runs (\<nu>, \<tau>, \<omega>), where \<nu> is the iniial state, \<tau> is a trace of 
communication events, and \<omega> is either a state or NonFin if the run is unfinished. 
The pair (\<tau>, \<omega>) is the called observable behavior.
An unfinished run may be continued if the program did not abort due to a failing test.
In a linear history semantics, every denotation is naturally total and prefix-closed, which reflects 
that every program can start computation in every state and that every prefix of an observable trace
is observable as well.

This section provides basic operators on the denotations and proves common properties that are 
independent of the concrete notion of states and communication events.
Therefore, it is polymorphic ('a, 'b) in the notion of state 'a and communication event 'b.\<close>

datatype 'a reachedstate = Fin (gets: 'a) | NonFin

type_synonym ('a, 'b) domain = "'a \<times> ('b list) \<times> ('a reachedstate)"

notation prefix (infix "\<preceq>" 70)
notation strict_prefix (infix "\<prec>" 70)

subsection \<open>Properties of the Domain\<close>

text \<open>Prefix relation on the observable behavior\<close>
definition obspref :: "('b list \<times> 'a reachedstate) \<Rightarrow> ('b list \<times> 'a reachedstate) \<Rightarrow> bool" (infixr "\<sqsubseteq>" 75)
  where "obs' \<sqsubseteq> obs \<longleftrightarrow> (let (\<tau>', \<omega>') = obs'; (\<tau>, \<omega>) = obs in
    (\<tau>' = \<tau> \<and> \<omega>' = \<omega>) \<or> (\<tau>' \<preceq> \<tau> \<and> \<omega>' = NonFin))"

(* substantially simplifies proof of transitivity *)
lemma obspref_alt: "(\<tau>', \<omega>') \<sqsubseteq> (\<tau>, \<omega>) \<equiv> ((\<tau>' = \<tau> \<and> \<omega>' = \<omega>) \<or> (\<tau>' \<preceq> \<tau> \<and> \<omega>' = NonFin))"
  by (simp add: obspref_def)

text \<open>\<sqsubseteq> is a partial order\<close>
lemma obspref_refl: "(\<tau>, \<omega>) \<sqsubseteq> (\<tau>, \<omega>)" by (simp add: obspref_def) 
lemma obspref_trans: "(\<tau>'', \<omega>'') \<sqsubseteq> (\<tau>', \<omega>') \<Longrightarrow> (\<tau>', \<omega>') \<sqsubseteq> (\<tau>, \<omega>) \<Longrightarrow> (\<tau>'', \<omega>'') \<sqsubseteq> (\<tau>, \<omega>)"
  by (metis (no_types, lifting) obspref_alt prefix_order.trans)
lemma obspref_antisym: "obs' \<sqsubseteq> obs \<Longrightarrow> obs \<sqsubseteq> obs' \<Longrightarrow> obs' = obs"
  by (metis (mono_tags, lifting) case_prod_unfold obspref_def prefix_order.antisym prod_eq_iff)

text \<open>([], NonFin) is the least element of \<sqsubseteq>\<close>
lemma obspref_least: "([], NonFin) \<sqsubseteq> (\<tau>, \<omega>)"
  by (simp add: obspref_def)

lemma obspref_nonfin [simp]: "(\<tau>\<^sub>2, NonFin) \<sqsubseteq> (\<tau>\<^sub>2, \<omega>)"
  by (simp add: obspref_alt)



subsection \<open>Operators on the Domain\<close>

text \<open>The least denotation \<open>\<bottom>\<^sub>\<D>\<close> is part of every denotation and reflects that every program can
start computation in every state even if it immediately aborts.\<close>
abbreviation leastComp :: "('a, 'b) domain set" ("\<bottom>\<^sub>\<D>") 
  where "leastComp \<equiv> { (\<nu>, [], NonFin) | \<nu>. True }"

text \<open>The identity denotation \<open>I\<^sub>\<S>\<close> is a neutral element for compose but not prefix-closed.\<close>
abbreviation idComp :: "('a, 'b) domain set" ("I\<^sub>\<S>") 
  where "idComp \<equiv> { (\<nu>, [], Fin \<nu>) | \<nu>. True }"

text \<open>The neutral denotation is the identity \<open>I\<^sub>\<S>\<close> plus the least denotation \<open>\<bottom>\<^sub>\<D>\<close> to ensure 
prefix-closedness.\<close>
abbreviation neutComp :: "('a, 'b) domain set" ("I\<^sub>\<D>")  
  where "neutComp \<equiv> I\<^sub>\<S> \<union> \<bottom>\<^sub>\<D>"

fun botop :: "('a, 'b) domain set \<Rightarrow> ('a, 'b) domain set"
  where "botop D = { (\<nu>, \<tau>, NonFin) | \<nu> \<tau>. \<exists>\<omega>. (\<nu>, \<tau>, \<omega>) \<in> D }"

fun continue :: "('a, 'b) domain set \<Rightarrow> ('a, 'b) domain set \<Rightarrow> ('a, 'b) domain set" (infixr "\<triangleright>" 100)
  where "continue D\<^sub>1 D\<^sub>2 = { (\<nu>, \<tau>\<^sub>1 @ \<tau>\<^sub>2, \<omega>) | \<nu> \<tau>\<^sub>1 \<tau>\<^sub>2 \<omega>. \<exists>\<kappa>. (\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> D\<^sub>1 \<and> (\<kappa>, \<tau>\<^sub>2, \<omega>) \<in> D\<^sub>2 }"

fun compose :: "('a, 'b) domain set \<Rightarrow> ('a, 'b) domain set \<Rightarrow> ('a, 'b) domain set" (infixr "\<Zsemi>" 100)
  where "compose D\<^sub>1 D\<^sub>2 = botop D\<^sub>1 \<union> (D\<^sub>1 \<triangleright> D\<^sub>2)"



subsection \<open>Reflexive-transitive Closure and Iteration\<close>

text \<open>Reflexive-transitive closure operator defined as inductively defined set, which works for the 
denotations of a linear history semantics that are sets of triples, and further respects 
prefix-closedness and totality.\<close>
inductive_set rtcl_linhis :: "('a, 'b) domain set \<Rightarrow> ('a, 'b) domain set"
  for D :: "('a, 'b) domain set"
  where
    rtcl_linhis_pc_base: "(\<nu>, [], NonFin) \<in> rtcl_linhis D"
  | rtcl_linhis_base_id: "(\<nu>, [], Fin \<nu>) \<in> rtcl_linhis D"
  | rtcl_linhis_pc_step: "(\<nu>, \<tau>, \<kappa>) \<in> D \<Longrightarrow> (\<nu>, \<tau>, NonFin) \<in> rtcl_linhis D"
  | rtcl_linhis_continue: "(\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> D \<Longrightarrow> (\<kappa>, \<tau>\<^sub>2, \<omega>) \<in> rtcl_linhis D \<Longrightarrow> (\<nu>, \<tau>\<^sub>1 @ \<tau>\<^sub>2, \<omega>) \<in> rtcl_linhis D"

text \<open>Iteration operator\<close>
fun iterate_linhis :: "nat \<Rightarrow> ('a, 'b) domain set \<Rightarrow> ('a, 'b) domain set"
  where
    "iterate_linhis 0 D = I\<^sub>\<D>"
  | "iterate_linhis (Suc n) D = (botop D \<union> (D \<triangleright> (iterate_linhis n D)))"

lemma unroll_iteration: "(\<Union>n. iterate_linhis n D) = iterate_linhis 0 D \<union> (\<Union>n. iterate_linhis (Suc n) D)"
proof -
  have "\<And>f. \<Union> (range f) = (f 0::('a, 'b) domain set) \<union> (\<Union>n. f (Suc n))" using union_unroll by metis
  then show ?thesis by meson
qed

lemma iteration_Suc_compose [simp]: "(\<Union>n. iterate_linhis (Suc n) D) = D \<Zsemi> (\<Union>n. iterate_linhis n D)"
  by auto

text \<open>The reflexive-transitive closure for the denotations equals the union of all their final
iterations.\<close>
theorem linhis_rtcl_eq_iteration: "rtcl_linhis D = (\<Union>n. iterate_linhis n D)"
proof
  have "\<And>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> rtcl_linhis D \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> (\<Union>n. iterate_linhis n D)"
  proof -
    fix \<nu> \<tau> \<omega>
    show "(\<nu>, \<tau>, \<omega>) \<in> rtcl_linhis D \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> (\<Union>n. iterate_linhis n D)"
    proof (induction rule: rtcl_linhis.induct)
      case (rtcl_linhis_pc_base \<nu>)
      thus ?case by (metis (mono_tags, lifting) UNIV_I UN_I Un_iff mem_Collect_eq iterate_linhis.simps(1)) 
    next
      case (rtcl_linhis_base_id \<nu>)
      thus ?case by (metis (mono_tags, lifting) UNIV_I UN_I Un_iff mem_Collect_eq iterate_linhis.simps(1)) 
    next
      case (rtcl_linhis_pc_step \<nu> \<tau> \<kappa>)
      thus ?case by (metis (mono_tags, lifting) CollectI UNIV_I UN_I UnCI botop.simps iterate_linhis.simps(2))
    next
      case (rtcl_linhis_continue \<nu> \<tau>\<^sub>1 \<kappa> \<tau>\<^sub>2 \<omega>)
      have "(\<kappa>, \<tau>\<^sub>2, \<omega>) \<in> (\<Union>n. iterate_linhis n D)"
        using rtcl_linhis_continue.IH by blast
      then obtain n where "(\<kappa>, \<tau>\<^sub>2, \<omega>) \<in> iterate_linhis n D" by auto
      hence "(\<nu>, \<tau>\<^sub>1 @ \<tau>\<^sub>2, \<omega>) \<in> (D \<triangleright> (iterate_linhis n D))"
        using rtcl_linhis_continue.hyps(1) by auto
      hence "(\<nu>, \<tau>\<^sub>1 @ \<tau>\<^sub>2, \<omega>) \<in> iterate_linhis (n+1) D" by force
      thus "(\<nu>, \<tau>\<^sub>1 @ \<tau>\<^sub>2, \<omega>) \<in> (\<Union>n. iterate_linhis n D)" by blast
    qed
  qed
  hence "\<And>c. c \<in> rtcl_linhis D \<Longrightarrow> c \<in> (\<Union>n. iterate_linhis n D)" by force
  thus "rtcl_linhis D \<subseteq> (\<Union>n. iterate_linhis n D)" by blast 
next
  have "\<And>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> (\<Union>n. iterate_linhis n D) \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> rtcl_linhis D"
  proof -
    fix \<nu> \<tau> \<omega> n
    show "(\<nu>, \<tau>, \<omega>) \<in> (\<Union>n. iterate_linhis n D) \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> rtcl_linhis D"
    proof -
      assume "(\<nu>, \<tau>, \<omega>) \<in> (\<Union>n. iterate_linhis n D)"
      then obtain n where "(\<nu>, \<tau>, \<omega>) \<in> iterate_linhis n D" by auto
      have "(\<nu>, \<tau>, \<omega>) \<in> iterate_linhis n D \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> rtcl_linhis D"
      proof (induction n arbitrary: \<nu> \<tau> \<omega>)
        case 0
        thus ?case using rtcl_linhis.rtcl_linhis_base_id rtcl_linhis.rtcl_linhis_pc_base by fastforce 
      next
        case 0: (Suc n)
        hence "(\<nu>, \<tau>, \<omega>) \<in> botop D \<union> (D \<triangleright> (iterate_linhis n D))" by auto
        thus "(\<nu>, \<tau>, \<omega>) \<in> rtcl_linhis D"
        proof (cases "(\<nu>, \<tau>, \<omega>) \<in> botop D")
          case True
          thus ?thesis using rtcl_linhis.rtcl_linhis_pc_step by fastforce
        next
          case False
          then obtain \<tau>\<^sub>1 \<kappa> \<tau>\<^sub>2 where "(\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> D" and "(\<kappa>, \<tau>\<^sub>2, \<omega>) \<in> iterate_linhis n D" and "\<tau> = \<tau>\<^sub>1 @ \<tau>\<^sub>2"
            using \<open>(\<nu>, \<tau>, \<omega>) \<in> botop D \<union> D \<triangleright> (iterate_linhis n D)\<close> by auto
          hence "(\<kappa>, \<tau>\<^sub>2, \<omega>) \<in> rtcl_linhis D" using 0 by auto
          hence "(\<nu>, \<tau>\<^sub>1 @ \<tau>\<^sub>2, \<omega>) \<in> rtcl_linhis D" using \<open>(\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> D\<close> by (simp add: rtcl_linhis.rtcl_linhis_continue)
          thus "(\<nu>, \<tau>, \<omega>) \<in> rtcl_linhis D" using \<open>\<tau> = \<tau>\<^sub>1 @ \<tau>\<^sub>2\<close> by auto
        qed
      qed
      show ?thesis
        by (simp add: \<open>(\<nu>, \<tau>, \<omega>) \<in> iterate_linhis n D \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> rtcl_linhis D\<close> \<open>(\<nu>, \<tau>, \<omega>) \<in> iterate_linhis n D\<close>)
    qed
  qed
  hence "\<And>c. c \<in> (\<Union>n. iterate_linhis n D) \<Longrightarrow> c \<in> rtcl_linhis D" by force
  thus "(\<Union>n. iterate_linhis n D) \<subseteq> rtcl_linhis D" by auto
qed

lemma unroll_rtcl_linhis: "rtcl_linhis D = I\<^sub>\<D> \<union> (D \<Zsemi> (rtcl_linhis D))"
proof -
  have "(\<Union>n. iterate_linhis n D) = I\<^sub>\<D> \<union> (\<Union>n. iterate_linhis (Suc n) D)" 
    using unroll_iteration by simp
  thus ?thesis using iteration_Suc_compose by (metis linhis_rtcl_eq_iteration)
qed

lemma zero_iterations: "iterate_linhis 0 D \<subseteq> rtcl_linhis D" 
  using linhis_rtcl_eq_iteration by blast



subsection \<open>Prefix-closedness and Totality of the Semantics\<close>

inductive pc :: "('a, 'b) domain set \<Rightarrow> bool"
  where "(\<And>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> D \<Longrightarrow> (\<And>\<tau>' \<omega>'. (\<tau>', \<omega>') \<sqsubseteq> (\<tau>, \<omega>) \<Longrightarrow> (\<nu>, \<tau>', \<omega>') \<in> D)) \<Longrightarrow> pc D"

inductive total :: "('a, 'b) domain set \<Rightarrow> bool"
  where "(\<And>\<nu>. (\<exists>\<tau> \<omega>. ((\<nu>, \<tau>, \<omega>) \<in> D))) \<Longrightarrow> total D"

lemma total_least [simp]: "(\<And>\<nu>. (\<nu>, [], NonFin) \<in> D) \<Longrightarrow> total D" by (meson total.intros)

lemma leastComp_pc: "pc \<bottom>\<^sub>\<D>"
  using pc.simps obspref_def by fastforce

lemma leastComp_total: "total \<bottom>\<^sub>\<D>"
  by (simp add: total.intros)

lemma botop_pc: "pc D \<Longrightarrow> pc (botop D)"
proof
  fix \<nu> \<tau> \<omega> \<tau>' \<omega>'
  assume 0: "pc D"
  show "(\<nu>, \<tau>, \<omega>) \<in> botop D \<Longrightarrow> (\<tau>', \<omega>') \<sqsubseteq> (\<tau>, \<omega>) \<Longrightarrow> (\<nu>, \<tau>', \<omega>') \<in> botop D"
  proof -
    assume inBot: "(\<nu>, \<tau>, \<omega>) \<in> botop D"
    hence "\<exists>\<omega>\<^sub>0. (\<nu>, \<tau>, \<omega>\<^sub>0) \<in> D" by auto
    then obtain \<omega>\<^sub>0 where inD: "(\<nu>, \<tau>, \<omega>\<^sub>0) \<in> D" by auto
    assume pref: "(\<tau>', \<omega>') \<sqsubseteq> (\<tau>, \<omega>)"
    hence "\<omega>' = NonFin" using obspref_def inBot by auto
    hence "(\<tau>', \<omega>') \<sqsubseteq> (\<tau>, \<omega>\<^sub>0)" using pref by (metis (mono_tags, lifting) case_prodD case_prodI obspref_def prefix_order.dual_order.refl) 
      (*using inBot obspref_def prefix_def by auto*)
    hence "(\<nu>, \<tau>', \<omega>') \<in> D" by (meson inD 0 pc.cases)
    thus "(\<nu>, \<tau>', \<omega>') \<in> botop D" using pref inBot obspref_def by auto
  qed
qed

lemma botop_total: "total D \<Longrightarrow> total (botop D)"
  using total.simps total.cases by fastforce

lemma compose_pc: "pc D\<^sub>1 \<Longrightarrow> pc D\<^sub>2 \<Longrightarrow> pc (D\<^sub>1 \<Zsemi> D\<^sub>2)"
proof 
  fix \<nu> \<tau> \<omega> \<tau>' \<omega>'
  assume 0: "pc D\<^sub>1" and 1: "pc D\<^sub>2"
  assume run: "(\<nu>, \<tau>, \<omega>) \<in> D\<^sub>1 \<Zsemi> D\<^sub>2"
  assume obs: "(\<tau>', \<omega>') \<sqsubseteq> (\<tau>, \<omega>)"
  have "(\<nu>, \<tau>', \<omega>') \<notin> botop D\<^sub>1 \<Longrightarrow> (\<nu>, \<tau>', \<omega>') \<in> D\<^sub>1 \<triangleright> D\<^sub>2"
  proof -
    assume no1: "(\<nu>, \<tau>', \<omega>') \<notin> botop D\<^sub>1"
    show "(\<nu>, \<tau>', \<omega>') \<in> D\<^sub>1 \<triangleright> D\<^sub>2"
    proof (cases "\<omega>' = NonFin")
      case True
      hence "(\<nu>, \<tau>, \<omega>) \<in> D\<^sub>1 \<triangleright> D\<^sub>2" using run 0 UnE botop_pc no1 obs pc.cases unfolding compose.simps by meson
      then obtain \<tau>\<^sub>1 \<kappa> \<tau>\<^sub>2 where sub_runs: "(\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> D\<^sub>1 \<and> (\<kappa>, \<tau>\<^sub>2, \<omega>) \<in> D\<^sub>2 \<and> \<tau> = \<tau>\<^sub>1 @ \<tau>\<^sub>2" by auto
      have "\<not>(\<tau>' \<preceq> \<tau>\<^sub>1)" using True 0 no1 obspref_alt pc.simps sub_runs by fastforce
      hence "\<tau>\<^sub>1 \<preceq> \<tau>'" by (metis obs obspref_alt prefixI prefix_same_cases sub_runs)
      then obtain \<tau>\<^sub>2' where "\<tau>' = \<tau>\<^sub>1 @ \<tau>\<^sub>2'" using prefix_def by blast
      hence "(\<kappa>, \<tau>\<^sub>2', \<omega>') \<in> D\<^sub>2" by (metis (no_types, lifting) 1 obs obspref_alt pc.cases prefix_order.dual_order.eq_iff same_prefix_prefix sub_runs)
      thus ?thesis using \<open>\<tau>' = \<tau>\<^sub>1 @ \<tau>\<^sub>2'\<close> sub_runs by auto
    next
      case False
      thus ?thesis by (metis UnE run no1 obs obspref_alt compose.simps)
    qed
  qed
  thus "(\<nu>, \<tau>', \<omega>') \<in> D\<^sub>1 \<Zsemi> D\<^sub>2" unfolding compose.simps by blast
qed

lemma compose_total: "total D\<^sub>1  \<Longrightarrow> total (D\<^sub>1 \<Zsemi> D\<^sub>2)"
  unfolding compose.simps by (meson UnI1 botop_total total.cases total.intros)

lemma iterate_linhis_pc: "pc D \<Longrightarrow> pc (iterate_linhis n D)"
proof (induction n)
  case 0
  show "pc (iterate_linhis 0 D)" unfolding pc.simps obspref_def by fastforce
next
  case (Suc m)
  hence "pc (botop D \<union> (D \<triangleright> (iterate_linhis m D)))" using compose_pc unfolding compose.simps by blast
  thus "pc (iterate_linhis (Suc m) D)" by simp
qed

lemma iterate_linhis_total: "total D \<Longrightarrow> total (iterate_linhis n D)"
  apply (cases n) 
  using total.simps apply auto[1] 
  using compose_total by auto

lemma any_union_pc: "(\<And>n. pc (D n)) \<Longrightarrow> pc (\<Union>n. D n)"
proof
  fix \<nu> \<tau> \<omega> \<tau>' \<omega>'
  assume 0: "\<And>n. pc (D n)"
  assume "(\<nu>, \<tau>, \<omega>) \<in> (\<Union>n. D n)"
  then obtain n where run: "(\<nu>, \<tau>, \<omega>) \<in> (D n)" by auto
  assume "(\<tau>', \<omega>') \<sqsubseteq> (\<tau>, \<omega>)"
  hence "(\<nu>, \<tau>', \<omega>') \<in> (D n)" by (meson 0 pc.cases run)
  thus "(\<nu>, \<tau>', \<omega>') \<in> (\<Union>n. D n)" by blast
qed

lemma rtcl_linhis_pc: "pc D \<Longrightarrow> pc (rtcl_linhis D)"
  by (simp add: iterate_linhis_pc linhis_rtcl_eq_iteration any_union_pc)

lemma rtcl_linhis_total: "total (rtcl_linhis D)"
  by (meson rtcl_linhis.rtcl_linhis_base_id total.intros)



subsection \<open>Algebraic-properties of the Operators\<close>

lemma domain_subseteqI: "(\<And>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> (D :: ('a, 'b) domain set) \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> M) \<Longrightarrow> D \<subseteq> M"
  by force

lemma leastComp_is_least: "pc D \<Longrightarrow> total D \<Longrightarrow> \<bottom>\<^sub>\<D> \<subseteq> D"
proof (rule domain_subseteqI)
  fix \<nu> \<tau> \<omega>
  show "pc D \<Longrightarrow> total D \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> \<bottom>\<^sub>\<D> \<Longrightarrow> (\<nu>, \<tau>, \<omega>) \<in> D" using mem_Collect_eq obspref_least pc.cases total.cases by (smt (verit))
qed

lemma denotations_contain_bot:
  assumes "pc D"
  shows "botop D \<subseteq> D"
proof (rule domain_subseteqI)
  fix \<nu> \<tau> \<omega>
  assume "(\<nu>, \<tau>, \<omega>) \<in> botop D"
  then obtain \<omega>\<^sub>0 where "(\<nu>, \<tau>, \<omega>\<^sub>0) \<in> D" by fastforce
  moreover have "(\<tau>, \<omega>) \<sqsubseteq> (\<tau>, \<omega>\<^sub>0)" using \<open>(\<nu>, \<tau>, \<omega>) \<in> botop D\<close> obspref_alt by fastforce
  ultimately show "(\<nu>, \<tau>, \<omega>) \<in> D" by (meson assms pc.cases)
qed

lemma neutComp_is_neut: 
  assumes "pc D"
  shows "D \<Zsemi> I\<^sub>\<D> = D"
proof (rule; rule)
  fix x
  assume 0: "x \<in> D \<Zsemi> I\<^sub>\<D>"
  then obtain \<nu> \<tau> \<omega> where 1: "x = (\<nu>, \<tau>, \<omega>)" using prod_cases3 by blast
  show "x \<in> D"
  proof (cases "(\<nu>, \<tau>, \<omega>) \<in> botop D")
    case True
    thus ?thesis using 1 assms denotations_contain_bot by blast
  next
    case False
    thus ?thesis using 0 1 by auto
  qed
next
  fix x
  assume 0: "x \<in> D"
  then obtain \<nu> \<tau> \<omega> where 1: "x = (\<nu>, \<tau>, \<omega>)" using prod_cases3 by blast
  show "x \<in> D \<Zsemi> I\<^sub>\<D>"
  proof (cases "\<omega> = NonFin")
    case True
    thus ?thesis using 0 1 by auto
  next
    case False
    then obtain \<omega>' where "\<omega> = Fin \<omega>'" using reachedstate.collapse by metis
    thus ?thesis using 0 1 by auto
  qed
qed

lemma iterate_one_idem: "pc D \<Longrightarrow> iterate_linhis 1 D = D"
  using neutComp_is_neut by fastforce



lemma neutComp_is_lneut: "I\<^sub>\<D> \<triangleright> D = D" by auto

lemma continue_r_subneut: "D \<triangleright> I\<^sub>\<S> \<subseteq> D" by fastforce

lemma continue_assoc: "(U \<triangleright> M) \<triangleright> L = U \<triangleright> (M \<triangleright> L)"
proof (rule; rule)
  fix x
  assume "x \<in> (U \<triangleright> M) \<triangleright> L"
  then obtain \<nu> \<tau>\<^sub>1 \<kappa>\<^sub>1 \<tau>\<^sub>2 \<kappa>\<^sub>2 \<tau>\<^sub>3 \<omega> where "(\<nu>, \<tau>\<^sub>1, Fin \<kappa>\<^sub>1) \<in> U \<and> (\<kappa>\<^sub>1, \<tau>\<^sub>2, Fin \<kappa>\<^sub>2) \<in> M \<and> (\<kappa>\<^sub>2, \<tau>\<^sub>3, \<omega>) \<in> L \<and> x = (\<nu>, \<tau>\<^sub>1@\<tau>\<^sub>2@\<tau>\<^sub>3, \<omega>)" by auto
  thus "x \<in> U \<triangleright> (M \<triangleright> L)" unfolding continue.simps by fast
next
  fix x
  assume "x \<in> U \<triangleright> (M \<triangleright> L)"
  then obtain \<nu> \<tau>\<^sub>1 \<kappa>\<^sub>1 \<tau>\<^sub>2 \<kappa>\<^sub>2 \<tau>\<^sub>3 \<omega> where "(\<nu>, \<tau>\<^sub>1, Fin \<kappa>\<^sub>1) \<in> U \<and> (\<kappa>\<^sub>1, \<tau>\<^sub>2, Fin \<kappa>\<^sub>2) \<in> M \<and> (\<kappa>\<^sub>2, \<tau>\<^sub>3, \<omega>) \<in> L \<and> x = (\<nu>, (\<tau>\<^sub>1@\<tau>\<^sub>2)@\<tau>\<^sub>3, \<omega>)" by auto
  thus "x \<in> (U \<triangleright> M) \<triangleright> L" unfolding continue.simps by fast
qed

lemma compose_assoc: "U \<Zsemi> (M \<Zsemi> L) = (U \<Zsemi> M) \<Zsemi> L"
proof (rule; rule)
  fix x
  assume 0: "x \<in> U \<Zsemi> (M \<Zsemi> L)"
  then obtain \<nu> \<tau> \<omega> where 1: "x = (\<nu>, \<tau>, \<omega>)" by auto
  show "x \<in> (U \<Zsemi> M) \<Zsemi> L"
  proof (cases "(\<nu>, \<tau>, \<omega>) \<in> botop U")
    case True
    hence "(\<nu>, \<tau>, \<omega>) \<in> botop (U \<Zsemi> M)" by auto
    thus ?thesis unfolding compose.simps using 1 by blast
  next
    case False
    hence 2: "(\<nu>, \<tau>, \<omega>) \<in> U \<triangleright> (M \<Zsemi> L)" using 0 1 by auto
    then obtain \<tau>\<^sub>1 \<kappa> \<tau>\<^sub>2 where continueSem: "\<tau> = \<tau>\<^sub>1 @ \<tau>\<^sub>2 \<and> (\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> U \<and> (\<kappa>, \<tau>\<^sub>2, \<omega>) \<in> M \<Zsemi> L" by fastforce
    show ?thesis
    proof (cases "(\<kappa>, \<tau>\<^sub>2, \<omega>) \<in> botop M")
      case True
      hence "(\<nu>, \<tau>, \<omega>) \<in> botop (U \<triangleright> M)" using continueSem by auto
      hence "(\<nu>, \<tau>, \<omega>) \<in> botop (U \<Zsemi> M)" using False by simp
      thus ?thesis unfolding compose.simps using 1 by blast
    next
      case False
      hence "(\<kappa>, \<tau>\<^sub>2, \<omega>) \<in> M \<triangleright> L" using continueSem by auto
      hence "(\<nu>, \<tau>, \<omega>) \<in> U \<triangleright> (M \<triangleright> L)" using continueSem unfolding continue.simps by fast
      hence "(\<nu>, \<tau>, \<omega>) \<in> (U \<triangleright> M) \<triangleright> L" using continue_assoc by blast
      thus ?thesis using 1 by auto
    qed
  qed
next
  fix x
  assume 0: "x \<in> (U \<Zsemi> M) \<Zsemi> L"
  then obtain \<nu> \<tau> \<omega> where 1: "x = (\<nu>, \<tau>, \<omega>)" by auto
  show "x \<in> U \<Zsemi> (M \<Zsemi> L)"
  proof (cases "(\<nu>, \<tau>, \<omega>) \<in> botop (U \<Zsemi> M)")
    case True
    show ?thesis
    proof (cases "(\<nu>, \<tau>, \<omega>) \<in> botop U")
      case True
      thus ?thesis using 0 1 by auto
    next
      case False
      hence "(\<nu>, \<tau>, \<omega>) \<in> botop (U \<triangleright> M)" using True by auto
      then obtain \<tau>\<^sub>1 \<kappa> \<tau>\<^sub>2 where continueSem: "\<tau> = \<tau>\<^sub>1 @ \<tau>\<^sub>2 \<and> (\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> U \<and> (\<kappa>, \<tau>\<^sub>2, \<omega>) \<in> M \<Zsemi> L" by auto
      hence "(\<nu>, \<tau>, \<omega>) \<in> U \<triangleright> (M \<Zsemi> L)" using True False by auto
      thus ?thesis using 1 by simp
    qed
  next
    case False
    hence "(\<nu>, \<tau>, \<omega>) \<in> (U \<triangleright> M) \<triangleright> L" using 0 1 False by auto
    hence "(\<nu>, \<tau>, \<omega>) \<in> U \<triangleright> (M \<triangleright> L)" using continue_assoc by blast
    thus ?thesis using 1 by auto
  qed
qed

lemma iterate_linhis_assoc:
  assumes "pc D"
  assumes "total D"
  shows "(iterate_linhis n D) \<Zsemi> D = D \<Zsemi> (iterate_linhis n D)"
proof (induction n)
  case 0
  have "(iterate_linhis 0 D) \<Zsemi> D = D" using neutComp_is_lneut leastComp_is_least assms unfolding compose.simps iterate_linhis.simps(1) botop.simps by blast
  also have "... = D \<Zsemi> (iterate_linhis 0 D)" using assms(1) neutComp_is_neut unfolding compose.simps iterate_linhis.simps(1) by blast
  finally show ?case by blast
next
  case (Suc n)
  have "(iterate_linhis (Suc n) D) \<Zsemi> D = (D \<Zsemi> (iterate_linhis n D)) \<Zsemi> D" unfolding compose.simps iterate_linhis.simps(2) by blast
  also have "... = D \<Zsemi> ((iterate_linhis n D) \<Zsemi> D)" using compose_assoc by blast
  also have "... = D \<Zsemi> (D \<Zsemi> (iterate_linhis n D))" using Suc by presburger
  also have "... = D \<Zsemi> (iterate_linhis (Suc n) D)" unfolding compose.simps iterate_linhis.simps(2) by blast
  finally show ?case by blast 
qed

lemma iteration_linhis_assoc:
  assumes "pc D"
  assumes "total D"
  shows "(\<Union>n. iterate_linhis n D) \<Zsemi> D = D \<Zsemi> (\<Union>n. iterate_linhis n D)"
proof (rule; rule)
  fix \<nu>
  assume "\<nu> \<in> (\<Union>n. iterate_linhis n D) \<Zsemi> D"
  then obtain n where "\<nu> \<in> (iterate_linhis n D) \<Zsemi> D" by fastforce
  moreover have "D \<Zsemi> (iterate_linhis n D) \<subseteq> D \<Zsemi> (\<Union>n. iterate_linhis n D)" by fastforce
  ultimately show "\<nu> \<in> D \<Zsemi> (\<Union>n. iterate_linhis n D)" using iterate_linhis_assoc assms by blast
next
  fix \<nu>
  assume "\<nu> \<in> D \<Zsemi> (\<Union>n. iterate_linhis n D)"
  then obtain n where "\<nu> \<in> D \<Zsemi> (iterate_linhis n D)" by fastforce
  moreover have "(iterate_linhis n D) \<Zsemi> D \<subseteq> (\<Union>n. iterate_linhis n D) \<Zsemi> D" by fastforce
  ultimately show "\<nu> \<in> (\<Union>n. iterate_linhis n D) \<Zsemi> D" using iterate_linhis_assoc assms by blast
qed

lemma rtcl_assoc: "pc D \<Longrightarrow> total D \<Longrightarrow> (rtcl_linhis D) \<Zsemi> D = D \<Zsemi> (rtcl_linhis D)"
  using linhis_rtcl_eq_iteration iteration_linhis_assoc by metis

abbreviation nocom_denotation :: "('a, 'b) domain set \<Rightarrow> bool"
  where "nocom_denotation D \<equiv> (\<forall>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> D \<longrightarrow> \<tau> = [])"

lemma nocom_leastComp_is_total_and_pc:
  assumes 0: "nocom_denotation D"
  assumes 1: "\<bottom>\<^sub>\<D> \<subseteq> D"
  shows "total D \<and> pc D"
proof (* rule pc.intros *)
  show "total D" using total.simps 1 by fastforce
next
  show "pc D"
  proof
    fix \<nu> \<tau> \<omega> \<tau>' \<omega>'
    assume "(\<nu>, \<tau>, \<omega>) \<in> D"
    hence empty: "\<tau> = []" using 0 by auto  
    assume "(\<tau>', \<omega>') \<sqsubseteq> (\<tau>, \<omega>)"
    hence "\<tau>' \<preceq> \<tau>" using obspref_def prefix_order.eq_iff by fastforce 
    hence "\<tau>' = []" using empty prefix_def by auto 
    show "(\<nu>, \<tau>', \<omega>') \<in> D"
    proof (cases "\<omega>' = NonFin")
      case True
      hence "(\<nu>, \<tau>', \<omega>') \<in> \<bottom>\<^sub>\<D>" using \<open>\<tau>' = []\<close> by blast 
      thus "(\<nu>, \<tau>', \<omega>') \<in> D" using 1 by auto
    next
      case False
      hence "\<omega>' = \<omega>" using \<open>(\<tau>', \<omega>') \<sqsubseteq> (\<tau>, \<omega>)\<close> obspref_def by auto
      thus "(\<nu>, \<tau>', \<omega>') \<in> D" using \<open>(\<nu>, \<tau>, \<omega>) \<in> D\<close> \<open>\<tau>' = []\<close> empty by force 
    qed
  qed
qed



subsection \<open>Induction by Iteration\<close>

text \<open>Alternative induction schema for repetition that is based on iteration rather the 
reflexive-transitive closure.\<close>
theorem step_wise_induct:
  assumes base: "\<And>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> I\<^sub>\<D> \<Longrightarrow> P \<nu> \<tau> \<omega>" 
  assumes step: "\<And>n. (\<And>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> iterate_linhis n D \<Longrightarrow> P \<nu> \<tau> \<omega>) 
    \<Longrightarrow> (\<And>\<nu> \<tau> \<omega>. (\<nu>, \<tau>, \<omega>) \<in> iterate_linhis (n+1) D \<Longrightarrow> P \<nu> \<tau> \<omega>)"
  shows "(\<nu>, \<tau>, \<omega>) \<in> rtcl_linhis D \<Longrightarrow> P \<nu> \<tau> \<omega>"
proof -
  assume 0: "(\<nu>, \<tau>, \<omega>) \<in> rtcl_linhis D"
  have "(\<nu>, \<tau>, \<omega>) \<in> (\<Union>n. iterate_linhis n D)" using 0 linhis_rtcl_eq_iteration by auto
  then obtain n where "(\<nu>, \<tau>, \<omega>) \<in> iterate_linhis n D" by auto
  moreover have "(\<nu>, \<tau>, \<omega>) \<in> iterate_linhis n D \<Longrightarrow> P \<nu> \<tau> \<omega>" 
    apply (induction n arbitrary: \<nu> \<tau> \<omega>) 
    using base apply simp 
    using step Suc_eq_plus1 by metis
  ultimately show "P \<nu> \<tau> \<omega>" by auto
qed

end