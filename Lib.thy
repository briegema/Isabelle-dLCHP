theory "Lib"
imports
  Complex_Main
  "HOL-Library.Sublist"
begin 
section \<open>Generic Mathematical Background Lemmas\<close>

lemma finite_subset [simp]: "finite M \<Longrightarrow> finite {x\<in>M. P x}"
  by simp

lemma finite_powerset [simp]: "finite M \<Longrightarrow> finite {S. S\<subseteq>M}"
  by simp

lemma fst_pair [simp]: "fst(a,b) = a" 
  by simp

lemma snd_pair [simp]: "snd(a,b) = b" 
  by simp

definition fst_proj:: "('a*'b) set \<Rightarrow> 'a set"
  where "fst_proj M \<equiv> {A. \<exists>B. (A,B)\<in>M}"

definition snd_proj:: "('a*'b) set \<Rightarrow> 'b set"
  where "snd_proj M \<equiv> {B. \<exists>A. (A,B)\<in>M}"

lemma fst_proj_mem [simp]: "(A \<in> fst_proj M) = (\<exists>B. (A,B)\<in>M)"
  unfolding fst_proj_def by auto
  
lemma snd_proj_mem [simp]: "(B \<in> snd_proj M) = (\<exists>A. (A,B)\<in>M)"
  unfolding snd_proj_def by auto

lemma fst_proj_prop: "\<forall>x\<in>fst_proj {(A,B)| A B. P A \<and> R A B}. P(x)"
  unfolding fst_proj_def by auto

lemma snd_proj_prop: "\<forall>x\<in>snd_proj {(A,B) | A B. P B \<and> R A B}. P(x)"
  unfolding snd_proj_def by auto

lemma map_cons: "map f (Cons x xs) = Cons (f x) (map f xs)"
  by (rule List.list.map)
lemma map_append: "map f (append xs ys) = append (map f xs) (map f ys)"
  by simp

lemma union_unroll: "(\<Union>(n::nat). R n) = R 0 \<union> (\<Union>n. R (Suc n))"
  apply auto
  by (metis not0_implies_Suc)


lemma map_snd_Some: "f x \<noteq> None \<Longrightarrow> (g ++ f) x = f x"
  by (auto simp add: map_add_def)

lemma map_snd_None: "f x = None \<Longrightarrow> (g ++ f) x = g x"
  by (simp add: map_add_def)

lemma map_fst_None: "g x = None \<Longrightarrow> (g ++ f) x = f x"
  by (simp add: map_add_def option.case_eq_if)

lemma map_one [simp]: "map f [e] = [f e]" by force


paragraph \<open>Lemmas about Lists\<close>

lemma pref_split: "prefix \<tau>' \<tau> \<Longrightarrow> strict_prefix \<tau>' \<tau> \<or> \<tau>' = \<tau>" by auto

lemma pref_spref_non_empty_extension: "\<tau>\<^sub>2 \<noteq> [] \<Longrightarrow> prefix \<tau>' \<tau>\<^sub>1 \<Longrightarrow> strict_prefix \<tau>' (\<tau>\<^sub>1 @ \<tau>\<^sub>2)"
  by (metis prefix_order.le_neq_trans prefix_prefix same_prefix_nil)

lemma strict_perfix_singleton: "strict_prefix \<tau>' [\<rho>] \<Longrightarrow> \<tau>' = []"
  apply (simp add: strict_prefix_def prefix_def) 
  using Cons_eq_append_conv by fastforce

fun rmsuffix :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rmsuffix [] _ = []" |
  "rmsuffix xs [] = xs" |
  "rmsuffix (x#xs) ys = (if (x#xs) = ys then [] else x # rmsuffix xs ys)"

lemma rmsuffix_same [simp]: "rmsuffix xs xs = []"
  apply (induction xs)
  by auto

lemma rmsuffix_correct: "rmsuffix (xs @ ys) ys = xs"
  apply (induction xs)
   apply simp
  by (cases ys, auto)

lemma list_termination: "e \<in> set \<Theta> \<Longrightarrow> size e < Suc (size_list size \<Theta>)"
  apply (induction \<Theta>)
  by auto

lemma filter_add_empty_pred: "(filter p (\<tau> :: 'a list)) = [] \<Longrightarrow> (filter f \<tau>) = (filter (\<lambda>x. f x \<or> p x) \<tau>)"
proof (induction \<tau>, simp)
  case (Cons \<rho> \<tau>\<^sub>0)
  hence IH: "(filter f \<tau>\<^sub>0) = (filter (\<lambda>x. f x \<or> p x) \<tau>\<^sub>0)" by (metis filter.simps(2) list.distinct(1))
  show "(filter f (\<rho> # \<tau>\<^sub>0)) = (filter (\<lambda>x. f x \<or> p x) (\<rho> # \<tau>\<^sub>0))"
    apply (cases "f \<rho>")
     apply (simp add: IH)
    using Cons IH by fastforce
qed

lemma filter_hd_in_middle: "filter f \<tau> = \<rho>' # \<tau>\<^sub>0 \<Longrightarrow> \<exists>\<tau>\<^sub>1 \<tau>\<^sub>2. \<tau> = \<tau>\<^sub>1 @ [\<rho>'] @ \<tau>\<^sub>2 \<and> filter f \<tau>\<^sub>1 = []"
proof (induction \<tau>, simp)
  case (Cons \<rho> \<tau>\<^sub>0)
  then show ?case
  proof (cases "f \<rho>")
    case True (* this case does not use the IH *)
    hence "\<rho> # \<tau>\<^sub>0 = [] @ [\<rho>'] @ \<tau>\<^sub>0 \<and> (filter f []) = []" using Cons by auto
    thus "\<exists>\<tau>\<^sub>1 \<tau>\<^sub>2. \<rho> # \<tau>\<^sub>0 = \<tau>\<^sub>1 @ [\<rho>'] @ \<tau>\<^sub>2 \<and> (filter f \<tau>\<^sub>1) = []" by blast
  next
    case False
    hence "\<exists>\<tau>\<^sub>1 \<tau>\<^sub>2. \<tau>\<^sub>0 = \<tau>\<^sub>1 @ [\<rho>'] @ \<tau>\<^sub>2 \<and> (filter f \<tau>\<^sub>1) = []" using Cons by auto (* IH *)
    from this obtain \<tau>\<^sub>1 \<tau>\<^sub>2 where "\<tau>\<^sub>0 = \<tau>\<^sub>1 @ [\<rho>'] @ \<tau>\<^sub>2 \<and> (filter f \<tau>\<^sub>1) = []" by auto
    hence "\<rho> # \<tau>\<^sub>0 = (\<rho> # \<tau>\<^sub>1) @ [\<rho>'] @ \<tau>\<^sub>2 \<and> (filter f ((\<rho> # \<tau>\<^sub>1))) = []" using False by auto
    thus "\<exists>\<tau>\<^sub>1 \<tau>\<^sub>2. \<rho> # \<tau>\<^sub>0 = \<tau>\<^sub>1 @ [\<rho>'] @ \<tau>\<^sub>2 \<and> (filter f \<tau>\<^sub>1) = [] " by blast
  qed
qed

lemma unfiltered_sprefix_exists: "strict_prefix \<tau>'' (filter f \<tau>) \<Longrightarrow> \<exists>\<tau>'. strict_prefix \<tau>' \<tau> \<and> \<tau>'' = (filter f \<tau>')"
proof (induction \<tau>'' arbitrary: \<tau>)
  case Nil
  then show ?case by (metis filter.simps(1) prefix_bot.not_eq_extremum)
next
  case (Cons \<rho> \<tau>\<^sub>0'')
  then obtain \<tau>\<^sub>1 \<tau>\<^sub>2 where 0: "\<tau> = \<tau>\<^sub>1 @ [\<rho>] @ \<tau>\<^sub>2 \<and> (filter f \<tau>\<^sub>1) = [] \<and> f \<rho>" by (metis append_Cons filter_eq_Cons_iff filter_hd_in_middle strict_prefixE')
  hence "strict_prefix (Cons \<rho> \<tau>\<^sub>0'') (filter f ([\<rho>] @ \<tau>\<^sub>2))" using Cons.prems by auto
  hence "strict_prefix \<tau>\<^sub>0'' (filter f \<tau>\<^sub>2)" using 0 by simp
  then obtain \<tau>\<^sub>0' where "strict_prefix \<tau>\<^sub>0' \<tau>\<^sub>2 \<and> \<tau>\<^sub>0'' = (filter f \<tau>\<^sub>0')" using Cons.IH by blast  
  hence "strict_prefix (\<tau>\<^sub>1 @ [\<rho>] @ \<tau>\<^sub>0') \<tau> \<and> (Cons \<rho> \<tau>\<^sub>0'') = (filter f (\<tau>\<^sub>1 @ [\<rho>] @ \<tau>\<^sub>0'))" using 0 by (simp add: prefix_order.less_le)
  thus ?case by blast
qed

abbreviation prefrel where "prefrel rel \<equiv> rel = strict_prefix \<or> rel = prefix"
                                                    
lemma not_prefix_of_append_left:
  shows "prefrel rel \<Longrightarrow> rel \<tau>' (\<tau>\<^sub>1 @ \<tau>\<^sub>2) \<Longrightarrow> \<not> rel \<tau>' \<tau>\<^sub>1 \<Longrightarrow> \<exists>\<tau>\<^sub>2'. \<tau>' = \<tau>\<^sub>1 @ \<tau>\<^sub>2' \<and> rel \<tau>\<^sub>2' \<tau>\<^sub>2"
  apply (cases "rel = prefix \<or> \<tau>' = \<tau>\<^sub>1")
  using prefix_append strict_prefixE' apply fastforce
  using prefix_append prefix_order.less_le by blast

lemma subrel3I: "(\<And>x y z. (x, y, z) \<in> r \<Longrightarrow> (x, y, z) \<in> s) \<Longrightarrow> r \<subseteq> s" by auto

lemma eq3I: "(\<And>x y z. (x, y, z) \<in> r = ((x, y, z) \<in> s)) \<Longrightarrow> r = s" by auto

lemma singleton_image_inter: "(W \<inter> U) `` {h} = (W `` {h} \<inter> U `` {h})" by auto

lemma singleton_compl_image_same: "(-{(h, ch)}) `` {h} = -{ch}" by auto

lemma singleton_compl_image_other: "h\<^sub>0 \<noteq> h \<Longrightarrow> (- {(h\<^sub>0, ch)}) `` {h} = UNIV" by auto
  

end