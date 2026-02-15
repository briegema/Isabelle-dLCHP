theory "USubst"
imports
  Complex_Main
  "Syntax"          
  "Least_Static_Semantics"
  "Computable_Static_Semantics"
  "Denotational_Semantics"
begin 

section \<open>Uniform Substitution\<close>

subsection \<open>Substitutions\<close>

text \<open>A substitution is a partial map from the set of symbols (constants, functions, predicates,
program symbols) to an expressions/program of the same type. In particular, function and predicate
symbols of first-order real arithmetic can only be replaced with terms and formulas of first-order
arithmetic. Substitutions are implemented as record.\<close>

paragraph \<open>Substitution for Spaces\<close>

type_synonym cusubst = "ident \<rightharpoonup> cspace"
type_synonym vusubst = "ident \<rightharpoonup> vspace"

text \<open>The replacement for a real variable space constant must evaluate to a set of real variables.\<close>
definition is_rspace_vusubst :: "vusubst \<Rightarrow> bool"
  where "is_rspace_vusubst \<sigma>\<^sub>V = (\<forall>Z. case \<sigma>\<^sub>V Z of None \<Rightarrow> True | Some \<sigma>\<^sub>V \<Rightarrow> \<sigma>\<^sub>V \<in> rspace)"

definition is_busubst :: "cusubst \<times> vusubst \<Rightarrow> bool"
  where "is_busubst \<sigma> = (case \<sigma> of (_, \<sigma>\<^sub>V) \<Rightarrow> is_rspace_vusubst \<sigma>\<^sub>V)"

abbreviation empty_busubst_raw :: "cusubst \<times> vusubst"
  where "empty_busubst_raw \<equiv> (\<lambda>_. None, \<lambda>_. None)"

lemma empty_busubst_is_busubst [simp, intro]: "is_busubst empty_busubst_raw"
  unfolding is_busubst_def is_rspace_vusubst_def by simp

lemma trivial_busubst_is_busubst [simp, intro]: "is_busubst (\<sigma>\<^sub>C, \<lambda>_. None)"
  unfolding is_busubst_def is_rspace_vusubst_def by simp

text \<open>Type of substitutions for space constants\<close>
typedef busubst = "{\<sigma>:: cusubst \<times> vusubst. is_busubst \<sigma>}"
  morphisms busubst_raw well_vusubst
  by blast

setup_lifting type_definition_busubst


lift_definition SChanSpaces :: "busubst \<Rightarrow> cusubst" is "\<lambda>(\<sigma>\<^sub>C, _). \<sigma>\<^sub>C" .
lift_definition SVarSpaces :: "busubst \<Rightarrow> vusubst" is "\<lambda>(_, \<sigma>\<^sub>V). \<sigma>\<^sub>V" .

lemma SVarSpaces_correct [simp]: "is_rspace_vusubst (SVarSpaces \<sigma>)"
  by (transfer, unfold is_busubst_def, auto)

lift_definition mkbusubst :: "cusubst \<times> vusubst \<Rightarrow> busubst"
  is "\<lambda>(\<sigma>\<^sub>C, \<sigma>\<^sub>V). if is_busubst (\<sigma>\<^sub>C, \<sigma>\<^sub>V) then (\<sigma>\<^sub>C, \<sigma>\<^sub>V) else (\<sigma>\<^sub>C, \<lambda>_. None)"
  by auto

lemma access_mkbusubst [simp]: 
  shows "SVarSpaces (mkbusubst (\<sigma>\<^sub>\<Omega>, \<sigma>\<^sub>V)) = (if is_busubst (\<sigma>\<^sub>\<Omega>, \<sigma>\<^sub>V) then \<sigma>\<^sub>V else (\<lambda>_. None))"
    and "SChanSpaces (mkbusubst (\<sigma>\<^sub>\<Omega>, \<sigma>\<^sub>V)) = \<sigma>\<^sub>\<Omega>"
  by (transfer, auto)+

lemma busubst_eq [iff]: "(SChanSpaces \<sigma>\<^sub>1 = SChanSpaces \<sigma>\<^sub>2 \<and> SVarSpaces \<sigma>\<^sub>1 = SVarSpaces \<sigma>\<^sub>2) = (\<sigma>\<^sub>1 = \<sigma>\<^sub>2)"
  apply transfer by auto

lifting_update busubst.lifting
lifting_forget busubst.lifting

definition empty_busubst :: "busubst"
  where "empty_busubst = mkbusubst (empty_busubst_raw)"

lemma busubst_eqI [simp, intro]: "SChanSpaces \<sigma>\<^sub>1 = SChanSpaces \<sigma>\<^sub>2 \<Longrightarrow> SVarSpaces \<sigma>\<^sub>1 = SVarSpaces \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (meson busubst_eq)

lemma mkbusubst_self [simp]: "mkbusubst (SChanSpaces \<sigma>, SVarSpaces \<sigma>) = \<sigma>"
  by (simp add: is_busubst_def)

lemma is_busubstI: "is_rspace_vusubst \<sigma>\<^sub>Z \<Longrightarrow> is_busubst (\<sigma>\<^sub>Y, \<sigma>\<^sub>Z)"
  unfolding is_busubst_def by simp

lemma SVarSpaces_correct_Some0 [simp, intro]:
  assumes "SVarSpaces \<sigma> Z \<noteq> None"
  shows "the(SVarSpaces \<sigma> Z) \<in> rspace"
proof -
  have "is_rspace_vusubst (SVarSpaces \<sigma>)" by simp
  thus ?thesis unfolding is_rspace_vusubst_def by (simp add: assms option.case_eq_if)
qed


lemma SVarSpaces_correct_Some: "SVarSpaces \<sigma> Z = Some \<sigma>Z \<Longrightarrow> \<sigma>Z \<in> rspace"
  using SVarSpaces_correct_Some0 by fastforce



paragraph \<open>Types for Pure Real Polynomials and First-order Real Arithmetic\<close>

lemma dflt_QRpolynom [simp, intro]: "isQRpolynom (Number 0)" by simp

text \<open>Pure real polynomials as custom type\<close>
typedef QRpolynom = "{\<theta> :: rtrm. isQRpolynom \<theta>}"
  morphisms QRpolynom_raw well_isQRpolynom
  by auto

setup_lifting type_definition_QRpolynom

lemma QRpolynom_raw_correct [simp, intro]: "isQRpolynom (QRpolynom_raw \<theta>)"
  by transfer simp

lift_definition mkQRpolynom:: "rtrm \<Rightarrow> QRpolynom" 
  is "\<lambda>\<theta>. if isQRpolynom \<theta> then \<theta> else (Number 0)"
  by simp

lemma mkQRpolynom_access [simp]:
    "QRpolynom_raw (mkQRpolynom \<theta>) = (if isQRpolynom \<theta> then \<theta> else (Number 0))"
  by transfer simp

lifting_update QRpolynom.lifting
lifting_forget QRpolynom.lifting

definition dflt_FOL\<^sub>R :: fml
  where "dflt_FOL\<^sub>R = Geq (Number 0) (Number 0)"

lemma isFOL\<^sub>R_dflt_FOL\<^sub>R [simp, intro]: "isFOL\<^sub>R dflt_FOL\<^sub>R" 
  by (simp add: dflt_FOL\<^sub>R_def)

text \<open>First-order real arithmetic as custom type\<close>
typedef FOL\<^sub>R = "{\<phi> :: fml. isFOL\<^sub>R \<phi>}"
  morphisms FOL\<^sub>R_raw well_FOL\<^sub>R
  by auto

setup_lifting type_definition_FOL\<^sub>R

lemma FOL\<^sub>R_raw_correct [simp, intro]: "isFOL\<^sub>R (FOL\<^sub>R_raw \<phi>)"
  by transfer simp

lift_definition mkFOL\<^sub>R:: "fml \<Rightarrow> FOL\<^sub>R" 
  is "\<lambda>\<phi>. if isFOL\<^sub>R \<phi> then \<phi> else dflt_FOL\<^sub>R"
  by simp

lemma mkFOL\<^sub>R_access [simp]:
    "FOL\<^sub>R_raw (mkFOL\<^sub>R \<phi>) = (if isFOL\<^sub>R \<phi> then \<phi> else dflt_FOL\<^sub>R)"
  by transfer simp

lifting_update FOL\<^sub>R.lifting
lifting_forget FOL\<^sub>R.lifting



paragraph \<open>Definition of Substitutions\<close>

text \<open>Uniform substitution representation as record of partial maps from identifiers to well-formed
and type-compatible replacements.\<close>

record usubst =
  \<comment> \<open>Substitution for real-valued (constant and function) symbols separate for pure real 
  polynomials and general real terms\<close>
  SQRConsts0 :: "ident \<Rightarrow> nat \<rightharpoonup> QRpolynom"
  SRConsts :: "ident \<Rightarrow> nat \<rightharpoonup> rtrm"
  SQRFuncs0 :: "ident \<rightharpoonup> QRpolynom"
  SRFuncs :: "ident \<rightharpoonup> rtrm"
  \<comment> \<open>Substitution for trace-valued symbols\<close>
  STConsts :: "ident \<Rightarrow> nat \<rightharpoonup> ttrm"
  STFuncs :: "ident \<rightharpoonup> ttrm"
  \<comment> \<open>Substitution for predicate symbols separate for first-order real arithmetic and general formulas\<close>
  SFOL\<^sub>RPsymbs0 :: "ident \<rightharpoonup> FOL\<^sub>R"
  SPsymbs :: "ident \<rightharpoonup> fml"
  \<comment> \<open>Substitution for program symbols\<close>
  SChps0 :: "ident \<rightharpoonup> chp"
  \<comment> \<open>Substitution for space symbols\<close>
  SBindrs :: "busubst"

abbreviation empty_usubst :: usubst
  where "empty_usubst \<equiv> \<lparr> 
    SQRConsts0 = \<lambda>_ _. None,
    SRConsts = \<lambda>_ _. None,
    SQRFuncs0 = \<lambda>_. None, 
    SRFuncs = \<lambda>_. None, 
    STConsts = \<lambda>_ _. None, 
    STFuncs = \<lambda>_. None,
    SFOL\<^sub>RPsymbs0 = \<lambda>_. None,
    SPsymbs = \<lambda>_. None,
    SChps0 = \<lambda>_. None,
    SBindrs = empty_busubst\<rparr>"

definition SQRConsts :: "usubst \<Rightarrow> (ident \<Rightarrow> nat \<rightharpoonup> rtrm)"
  where "SQRConsts \<sigma> = (\<lambda>c n. case (SQRConsts0 \<sigma>) c n of
    None \<Rightarrow> None 
  | Some \<sigma>c \<Rightarrow> Some (QRpolynom_raw \<sigma>c))"

definition SAllRConsts
  where "SAllRConsts \<sigma> b c n \<equiv> if b then SQRConsts \<sigma> c n else SRConsts \<sigma> c n"

definition SQRFuncs :: "usubst \<Rightarrow> (ident \<rightharpoonup> rtrm)"
  where "SQRFuncs \<sigma> = (\<lambda>f. case (SQRFuncs0 \<sigma>) f of
    None \<Rightarrow> None 
  | Some \<sigma>f \<Rightarrow> Some (QRpolynom_raw \<sigma>f))"

definition SAllRFuncs
  where "SAllRFuncs \<sigma> b f \<equiv> if b then SQRFuncs \<sigma> f else SRFuncs \<sigma> f"

definition SFOL\<^sub>RPsymbs :: "usubst \<Rightarrow> (ident \<rightharpoonup> fml)"
  where "SFOL\<^sub>RPsymbs \<sigma> = (\<lambda>p. case (SFOL\<^sub>RPsymbs0 \<sigma>) p of
    None \<Rightarrow> None 
  | Some \<sigma>p \<Rightarrow> Some (FOL\<^sub>R_raw \<sigma>p))"

definition SAllPsymbs :: "usubst \<Rightarrow> bool \<Rightarrow> (ident \<rightharpoonup> fml)"
  where "SAllPsymbs \<sigma> b p \<equiv> if b then SFOL\<^sub>RPsymbs \<sigma> p else SPsymbs \<sigma> p"

definition SConsts\<^sub>\<Omega> :: "usubst \<Rightarrow> cusubst"
  where "SConsts\<^sub>\<Omega> \<sigma> = SChanSpaces (SBindrs \<sigma>)"

definition SConsts\<^sub>V :: "usubst \<Rightarrow> vusubst"
  where "SConsts\<^sub>V \<sigma> = SVarSpaces (SBindrs \<sigma>)"



paragraph \<open>Simple Properties of Substitutions for Automation\<close>

lemma SQRConsts_conv: "SQRConsts \<sigma> c n = None \<Longrightarrow> SQRConsts0 \<sigma> c n = None"
  apply (cases "SQRConsts0 \<sigma> c n")
  by (simp_all add: SQRConsts_def)

lemma SQRFuncs_conv: "SQRFuncs \<sigma> f = None \<Longrightarrow> SQRFuncs0 \<sigma> f = None"
  apply (cases "SQRFuncs0 \<sigma> f")
  by (simp_all add: SQRFuncs_def)

lemma SFOL\<^sub>RPsymbs_conv: "SFOL\<^sub>RPsymbs \<sigma> p = None \<Longrightarrow> SFOL\<^sub>RPsymbs0 \<sigma> p = None"
  apply (cases "SFOL\<^sub>RPsymbs0 \<sigma> p")
  by (simp_all add: SFOL\<^sub>RPsymbs_def)

lemma SQRConsts_empty_usubst [simp]: "SQRConsts empty_usubst c n = None" by (simp add: SQRConsts_def)
lemma SQRFuncs_empty_usubst [simp]: "SQRFuncs empty_usubst f = None" by (simp add: SQRFuncs_def)
lemma SFOL\<^sub>RPsymbs_empty_usubst [simp]: "SFOL\<^sub>RPsymbs empty_usubst p = None" by (simp add: SFOL\<^sub>RPsymbs_def)



paragraph \<open>Union of Substitutions\<close>

abbreviation busubst_raw_sum :: "busubst \<Rightarrow> busubst \<Rightarrow> cusubst \<times> vusubst"
  where "busubst_raw_sum \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<equiv> (SChanSpaces \<sigma>\<^sub>1 ++ SChanSpaces \<sigma>\<^sub>2, SVarSpaces \<sigma>\<^sub>1 ++ SVarSpaces \<sigma>\<^sub>2)"

definition busubst_sum :: "busubst \<Rightarrow> busubst \<Rightarrow> busubst" (infixr "++\<^sub>B" 100)
  where "busubst_sum \<sigma>\<^sub>1 \<sigma>\<^sub>2 = mkbusubst (busubst_raw_sum \<sigma>\<^sub>1 \<sigma>\<^sub>2)"

lemma is_is_rspace_vusubst_ususbt_sum: "is_rspace_vusubst (SVarSpaces \<sigma>\<^sub>1 ++ SVarSpaces \<sigma>\<^sub>2)"
  unfolding is_rspace_vusubst_def
  by (simp add: map_add_def option.case_eq_if)

lemma is_busubst_raw_sum [simp]: "is_busubst (busubst_raw_sum \<sigma>\<^sub>1 \<sigma>\<^sub>2)"
  by (simp add: is_is_rspace_vusubst_ususbt_sum is_busubstI)

lemma empty_busubst_lneut [simp, intro]: "empty_busubst ++\<^sub>B \<sigma> = \<sigma>"
  unfolding busubst_sum_def empty_busubst_def by simp

text \<open>Union of substitutions as union of the underlying partial maps\<close>
definition usubst_sum :: "usubst \<Rightarrow> usubst \<Rightarrow> usubst" (infixr "+++" 100)
  where "usubst_sum \<sigma>\<^sub>1 \<sigma>\<^sub>2 = \<lparr> 
    SQRConsts0 = (\<lambda>c. SQRConsts0 \<sigma>\<^sub>1 c ++ SQRConsts0 \<sigma>\<^sub>2 c),
    SRConsts = (\<lambda>c. SRConsts \<sigma>\<^sub>1 c ++ SRConsts \<sigma>\<^sub>2 c), 
    SQRFuncs0 = SQRFuncs0 \<sigma>\<^sub>1 ++ SQRFuncs0 \<sigma>\<^sub>2,
    SRFuncs = SRFuncs \<sigma>\<^sub>1 ++ SRFuncs \<sigma>\<^sub>2, 
    STConsts = (\<lambda>f. STConsts \<sigma>\<^sub>1 f ++ STConsts \<sigma>\<^sub>2 f), 
    STFuncs = STFuncs \<sigma>\<^sub>1 ++ STFuncs \<sigma>\<^sub>2, 
    SFOL\<^sub>RPsymbs0 = SFOL\<^sub>RPsymbs0 \<sigma>\<^sub>1 ++ SFOL\<^sub>RPsymbs0 \<sigma>\<^sub>2,
    SPsymbs = SPsymbs \<sigma>\<^sub>1 ++ SPsymbs \<sigma>\<^sub>2,
    SChps0 = SChps0 \<sigma>\<^sub>1 ++ SChps0 \<sigma>\<^sub>2,
    SBindrs = SBindrs \<sigma>\<^sub>1 ++\<^sub>B SBindrs \<sigma>\<^sub>2\<rparr>"



paragraph \<open>Size of Substitutions\<close>

text \<open>Coarse approximation of size which is enough for termination arguments\<close>
definition usubstsize:: "usubst \<Rightarrow> nat"
  where "usubstsize \<sigma> = (if (dom (SQRFuncs \<sigma>) = {} \<and> dom (SRFuncs \<sigma>) = {} \<and> dom (STFuncs \<sigma>) = {}
                           \<and> dom (SFOL\<^sub>RPsymbs \<sigma>) = {} \<and> dom (SPsymbs \<sigma>) = {}) then 1 else 2)"

lemma usubstsize_empty_usubst [simp, intro]: "usubstsize (empty_usubst) = 1"
  by (simp add: usubstsize_def SQRFuncs_def SFOL\<^sub>RPsymbs_def)

lemma dom_SQRFuncs: "(dom (SQRFuncs \<sigma>) = {}) = (dom (SQRFuncs0 \<sigma>) = {})"
  apply (simp add: SQRFuncs_def)
  by (metis map_option_case option.map_disc_iff)

lemma dom_SFOL\<^sub>RPsymbs: "(dom (SFOL\<^sub>RPsymbs \<sigma>) = {}) = (dom (SFOL\<^sub>RPsymbs0 \<sigma>) = {})"
  apply (simp add: SFOL\<^sub>RPsymbs_def)
  by (metis map_option_case option.map_disc_iff)
  
lemma usubstsize_empty_dom_sum: "usubstsize \<sigma>\<^sub>1 = 1 \<Longrightarrow> usubstsize \<sigma>\<^sub>2 = 1 \<Longrightarrow> usubstsize (\<sigma>\<^sub>1 +++ \<sigma>\<^sub>2) = 1"
  apply (simp only: usubstsize_def dom_SQRFuncs dom_SFOL\<^sub>RPsymbs)
  apply (simp add: usubst_sum_def)
  using n_not_Suc_n numeral_2_eq_2 by presburger

  

subsection \<open>Strict Mechanism for Handling Substitution Partiality in Isabelle\<close>

text \<open>f on defined arguments, strict undeft otherwise \<close>
fun Unaryo :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b option"
  where
  "Unaryo f (Some e) = Some (f e)"
| "Unaryo _ _ = None"

text \<open>f on defined arguments, strict undeft otherwise \<close>
fun Binaryo :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a option \<Rightarrow> 'b option \<Rightarrow> 'c option"
  where
  "Binaryo f (Some e\<^sub>1) (Some e\<^sub>2) = Some (f e\<^sub>1 e\<^sub>2)"
| "Binaryo _ _ _ = None"

text \<open>Optional terms that result from a substitution, are either actually a term or just None to 
indicate that the substitution clashed\<close>
type_synonym 'a trmo = "'a option"

abbreviation undeft:: "'a trmo" where "undeft \<equiv> None"
abbreviation Aterm:: "'a \<Rightarrow> 'a trmo" where "Aterm \<equiv> Some"

lemma undeft_equiv: "(\<theta>\<noteq>undeft) = (\<exists>t. \<theta>=Aterm t)" by simp

abbreviation Pluso :: "rtrm trmo \<Rightarrow> rtrm trmo \<Rightarrow> rtrm trmo" where "Pluso \<equiv> Binaryo Plus"
abbreviation Timeso :: "rtrm trmo \<Rightarrow> rtrm trmo \<Rightarrow> rtrm trmo" where "Timeso \<equiv> Binaryo Times"
abbreviation ChanOfo :: "ttrm trmo \<Rightarrow> rtrm trmo" where "ChanOfo \<equiv> Unaryo ChanOf"
abbreviation ValOfo :: "ttrm trmo \<Rightarrow> rtrm trmo" where "ValOfo \<equiv> Unaryo ValOf"
abbreviation TimeOfo :: "ttrm trmo \<Rightarrow> rtrm trmo" where "TimeOfo \<equiv> Unaryo TimeOf"
abbreviation LenTo :: "ttrm trmo \<Rightarrow> rtrm trmo" where "LenTo \<equiv> Unaryo LenT"

abbreviation ComItmo :: "chan \<Rightarrow> rtrm trmo \<Rightarrow> rtrm trmo \<Rightarrow> ttrm trmo" where "ComItmo ch \<equiv> Binaryo (ComItm ch)"
abbreviation Concato :: "ttrm trmo \<Rightarrow> ttrm trmo \<Rightarrow> ttrm trmo" where "Concato \<equiv> Binaryo Concat"
abbreviation Projo :: "ttrm trmo \<Rightarrow> cspace \<Rightarrow> ttrm trmo" where "Projo te Y \<equiv> Unaryo (\<lambda>te. Proj te Y) te"
abbreviation Accesso :: "ttrm trmo \<Rightarrow> rtrm trmo \<Rightarrow> ttrm trmo" where "Accesso \<equiv> Binaryo Access"  

abbreviation RArgo :: "rtrm trmo \<Rightarrow> arg trmo" where "RArgo \<equiv> Unaryo RArg"
abbreviation TArgo :: "ttrm trmo \<Rightarrow> arg trmo" where "TArgo \<equiv> Unaryo TArg"

abbreviation Argso :: "arg trmo \<Rightarrow> (arg list) trmo \<Rightarrow> (arg list) trmo" where "Argso \<equiv> Binaryo Cons"

lemma Pluso_undef: "(Pluso \<theta>\<^sub>1 \<theta>\<^sub>2 = None) = (\<theta>\<^sub>1=None \<or> \<theta>\<^sub>2=None)" by (metis Binaryo.elims option.distinct(1))
lemma Timeso_undef: "(Timeso \<theta>\<^sub>1 \<theta>\<^sub>2 = None) = (\<theta>\<^sub>1=None \<or> \<theta>\<^sub>2=None)" by (metis Binaryo.elims option.distinct(1))
lemma ChanOfo_undef: "(ChanOfo te = None) = (te=None)" by (metis Unaryo.elims option.distinct(1))
lemma ValOfo_undef: "(ValOfo te = None) = (te=None)" by (metis Unaryo.elims option.distinct(1))
lemma TimeOfo_undef: "(TimeOfo te = None) = (te=None)" by (metis Unaryo.elims option.distinct(1))
lemma LenTo_undef: "(LenTo te = None) = (te=None)" by (metis Unaryo.elims option.distinct(1))

lemma ComItmo_undef: "(ComItmo ch \<theta> \<eta> = undeft) = (\<theta>=undeft \<or> \<eta>=undeft)" by (metis Binaryo.elims option.distinct(1))
lemma Concato_undef: "(Concato te\<^sub>1 te\<^sub>2 = None) = (te\<^sub>1=None \<or> te\<^sub>2=None)" by (metis Binaryo.elims option.distinct(1))
lemma Projo_undef: "(Projo te Y = undeft) = (te=undeft)" by (metis Unaryo.elims option.distinct(1))
lemma Accesso_undef: "(Accesso te \<theta> = None) = (te=None \<or> \<theta>=None)" by (metis Binaryo.elims option.distinct(1))

lemma RArgo_undef: "(RArgo e = undeft) = (e=undeft)" by (metis Unaryo.elims option.distinct(1))
lemma TArgo_undef: "(TArgo e = undeft) = (e=undeft)" by (metis Unaryo.elims option.distinct(1))

lemma Argso_undef: "(Argso te \<theta> = None) = (te=None \<or> \<theta>=None)" by (metis Binaryo.elims option.distinct(1))

type_synonym fmlo = "fml option"

abbreviation undeff:: fmlo where "undeff \<equiv> None"
abbreviation Afml:: "fml \<Rightarrow> fmlo" where "Afml \<equiv> Some"

type_synonym chpo = "chp option"

abbreviation undefp:: chpo where "undefp \<equiv> None"
abbreviation Achp:: "chp \<Rightarrow> chpo" where "Achp \<equiv> Some"

lemma undeff_equiv: "(\<phi>\<noteq>undeff) = (\<exists>f. \<phi>=Afml f)" by simp
lemma undefp_equiv: "(\<alpha>\<noteq>undefp) = (\<exists>g. \<alpha>=Achp g)" by simp

abbreviation Geqo :: "rtrm trmo \<Rightarrow> rtrm trmo \<Rightarrow> fmlo" where "Geqo \<equiv> Binaryo Geq"
abbreviation Prefo :: "ttrm trmo \<Rightarrow> ttrm trmo \<Rightarrow> fmlo" where "Prefo \<equiv> Binaryo Pref"
abbreviation Noto :: "fmlo \<Rightarrow> fmlo" where "Noto \<equiv> Unaryo Not"
abbreviation Ando :: "fmlo \<Rightarrow> fmlo \<Rightarrow> fmlo" where "Ando \<equiv> Binaryo And"
abbreviation Existso :: "variable \<Rightarrow> fmlo \<Rightarrow> fmlo" where "Existso z \<equiv> Unaryo (Exists z)"
abbreviation Boxo :: "chpo \<Rightarrow> fmlo \<Rightarrow> fmlo" where "Boxo \<equiv> Binaryo Box"

fun AcBoxo :: "chpo \<Rightarrow> fmlo \<Rightarrow> fmlo \<Rightarrow> fmlo \<Rightarrow> fmlo" where
  "AcBoxo (Achp \<alpha>) (Afml A) (Afml C) (Afml \<psi>) = Afml(AcBox \<alpha> A C \<psi>)"
| "AcBoxo _ _ _ _ = undeff"

abbreviation ChanIno :: "rtrm trmo \<Rightarrow> cspace \<Rightarrow> fmlo" where "ChanIno ch Y \<equiv> Unaryo (\<lambda>ch. ChanIn ch Y) ch"

lemma Geqo_undef: "(Geqo \<theta>\<^sub>1 \<theta>\<^sub>2 = None) = (\<theta>\<^sub>1=None \<or> \<theta>\<^sub>2=None)" by (metis Binaryo.elims option.distinct(1))
lemma Prefo_undef: "(Prefo \<theta>\<^sub>1 \<theta>\<^sub>2 = None) = (\<theta>\<^sub>1=None \<or> \<theta>\<^sub>2=None)" by (metis Binaryo.elims option.distinct(1))
lemma Noto_undef: "(Noto \<phi> = undeff) = (\<phi>=undeff)" by (metis Unaryo.elims option.distinct(1))
lemma Ando_undef: "(Ando \<phi> \<psi> = undeff) = (\<phi>=undeff \<or> \<psi>=undeff)" by (metis Binaryo.elims option.distinct(1))
lemma Existso_undef: "(Existso z \<phi> = undeff) = (\<phi>=undeff)" by (metis Unaryo.elims option.distinct(1))  
lemma Boxo_undef: "(Boxo \<alpha> \<psi> = undeff) = (\<alpha>=undefp \<or> \<psi>=undeff)" by (metis Binaryo.elims option.distinct(1))
lemma AcBoxo_undef: "(AcBoxo \<alpha> A C \<psi> = undeff) = (\<alpha>=undefp \<or> A=undeff \<or> C=undeff \<or> \<psi>=undeff)" using AcBoxo.elims by blast
lemma ChanIno_undef: "(ChanIno ch Y = undeff) = (ch=undeft)" by (metis Unaryo.elims option.distinct(1))

abbreviation Assigno :: "rvar \<Rightarrow> rtrm trmo \<Rightarrow> chpo" where "Assigno x \<equiv> Unaryo (Assign x)"
abbreviation Testo :: "fmlo \<Rightarrow> chpo" where "Testo \<equiv> Unaryo Test"
abbreviation Evolutiono :: "ident \<Rightarrow> rtrm trmo \<Rightarrow> fmlo \<Rightarrow> chpo" where "Evolutiono x \<equiv> Binaryo (\<lambda>\<theta> \<phi>. Evolution x \<theta> \<phi>)"
abbreviation Choiceo :: "chpo \<Rightarrow> chpo \<Rightarrow> chpo" where "Choiceo \<equiv> Binaryo Choice"
abbreviation Composeo :: "chpo \<Rightarrow> chpo \<Rightarrow> chpo" where "Composeo \<equiv> Binaryo Compose"
abbreviation Loopo :: "chpo \<Rightarrow> chpo" where "Loopo \<equiv> Unaryo Loop"
abbreviation Sendo :: "chan \<Rightarrow> tvar \<Rightarrow> rtrm trmo \<Rightarrow> chpo" where "Sendo ch h \<equiv> Unaryo (Send ch h)"
abbreviation Paro :: "chpo \<Rightarrow> chpo \<Rightarrow> chpo" where "Paro \<equiv> Binaryo Par"

lemma Assigno_undef: "(Assigno x \<theta> = undefp) = (\<theta>=undeft)"  by (metis Unaryo.elims option.distinct(1))
lemma Evolutiono_undef: "(Evolutiono x \<theta> \<phi> = undefp) = (\<theta>=undeft \<or> \<phi>=undeff)"  by (metis Binaryo.elims option.distinct(1))
lemma Testo_undef: "(Testo \<phi> = undefp) = (\<phi>=undeff)"  by (metis Unaryo.elims option.distinct(1))
lemma Choiceo_undef: "(Choiceo \<alpha> \<beta> = None) = (\<alpha>=None \<or> \<beta>=None)" by (metis Binaryo.elims option.distinct(1))
lemma Composeo_undef: "(Composeo \<alpha> \<beta> = None) = (\<alpha>=None \<or> \<beta>=None)" by (metis Binaryo.elims option.distinct(1))
lemma Loopo_undef: "(Loopo \<alpha> = None) = (\<alpha>=None)" by (metis Unaryo.elims option.distinct(1))
lemma Sendo_undef: "(Sendo ch h \<theta> = undefp) = (\<theta>=undeft)"        by (metis Unaryo.elims option.distinct(1))
lemma Paro_undef: "(Paro \<alpha> \<beta> = None) = (\<alpha>=None \<or> \<beta>=None)" by (metis Binaryo.elims option.distinct(1))



subsection \<open>Recursive Application of One-Pass Uniform Substitution\<close>

text \<open>Taboo sets represet names bound by the context of the current expression\<close>
type_synonym taboo = "bindr set"

text \<open>A uniform substitution takes a substitution, a static semantics, and a taboo set,
then returns the actual substitution function\<close>
type_synonym 'a usubs = "usubst \<Rightarrow> stat_sem \<Rightarrow> taboo \<Rightarrow> 'a"



paragraph \<open>Substitutions of the Reserved Constant Symbol Dot\<close>

text \<open>Rdot and Tdot are some fixed constant function symbols that are reserved for the purposes of 
the substitution, which handles arguments of function and predicate symbols by creating a 
substitution of the argument for the special symbol Rdot or Tdot depending on the argument type.
Pure real polynomials require no extra constant, because the type of the argument itself remains 
untouched by the dot substitution.\<close>
definition Rdot :: "nat \<Rightarrow> rtrm" where "Rdot n = GRConst dotid n"
definition Tdot :: "nat \<Rightarrow> ttrm" where "Tdot n = TConst dotid n"

definition rdotsubst:: "nat \<Rightarrow> rtrm \<Rightarrow> usubst" 
  where "rdotsubst m \<theta> = empty_usubst \<lparr> SRConsts := (\<lambda>f n. (if f=dotid \<and> n=m then (Some(\<theta>)) else None)) \<rparr>"

definition tdotsubst:: "nat \<Rightarrow> ttrm \<Rightarrow> usubst" 
  where "tdotsubst m te = empty_usubst \<lparr> STConsts := \<lambda>f n. (if f=dotid \<and> n=m then (Some(te)) else None) \<rparr>"

text \<open>\<open>dotsubst m \<theta>\<close> creates the dot substitution \<open>{.m ~> \<theta>}\<close> substituting a term for the .m function symbol\<close>
fun dotsubst :: "nat \<Rightarrow> arg \<Rightarrow> usubst" where
  "dotsubst m (RArg \<theta>) = rdotsubst m \<theta>"
| "dotsubst m (TArg te) = tdotsubst m te"

fun dotsubst_vec_rec :: "nat \<Rightarrow> arg list \<Rightarrow> usubst" where
  "dotsubst_vec_rec n [] = empty_usubst"
| "dotsubst_vec_rec n (e # \<Theta>) = (dotsubst n e) +++ (dotsubst_vec_rec (n+1) \<Theta>)"

text \<open>\<open>dotsubst_vec {e\<^sub>0, \<dots>, e\<^sub>n}\<close> creates the vectorial dot substitution \<open>{.0 ~> e\<^sub>0, \<dots>, .n ~> e\<^sub>n}\<close>\<close>
definition dotsubst_vec :: "arg list \<Rightarrow> usubst" 
  where "dotsubst_vec \<Theta> = dotsubst_vec_rec 0 \<Theta>"



paragraph \<open>Uniform Substitution for Spaces\<close>

fun cusubst:: "busubst \<Rightarrow> (cspace \<Rightarrow> cspace)"
  where                                   
  "cusubst \<sigma> \<top>\<^sub>\<Omega> = \<top>\<^sub>\<Omega>"
| "cusubst \<sigma> (CChan ch) = CChan ch"
| "cusubst \<sigma> (CConst Y) = (case SChanSpaces \<sigma> Y of
    Some \<sigma>Y \<Rightarrow> \<sigma>Y
  | None \<Rightarrow> CConst Y)"
| "cusubst \<sigma> (-\<^sub>\<Omega> Y) = -\<^sub>\<Omega> (cusubst \<sigma> Y)"
| "cusubst \<sigma> (C \<inter>\<^sub>\<Omega> Y) = (cusubst \<sigma> C) \<inter>\<^sub>\<Omega> (cusubst \<sigma> Y)"    

fun vusubst :: "busubst \<Rightarrow> vspace \<Rightarrow> vspace"
  where                                   
  "vusubst \<sigma> \<top>\<^sub>R = \<top>\<^sub>R"
| "vusubst \<sigma> (VRVar x) = VRVar x"
| "vusubst \<sigma> (VTVar h) = VTVar h"
| "vusubst \<sigma> (VRConst X) = (case (SVarSpaces \<sigma>) X of
    Some \<sigma>X \<Rightarrow> \<sigma>X
  | None \<Rightarrow> VRConst X)"
| "vusubst \<sigma> (-\<^sub>V Z) = -\<^sub>V (vusubst \<sigma> Z)"
| "vusubst \<sigma> (X \<inter>\<^sub>V Z) = (vusubst \<sigma> X) \<inter>\<^sub>V (vusubst \<sigma> Z)"



paragraph \<open>One-pass Uniform Substitution for Terms\<close>

text \<open>Uniform substitution for real-valued constant symbols\<close>
definition rusappconst:: "(bool \<Rightarrow> ident \<Rightarrow> nat \<Rightarrow> rtrm trmo) usubs"
  where "rusappconst \<sigma> \<L> U b c n \<equiv> (case SAllRConsts \<sigma> b c n of 
     Some \<sigma>c \<Rightarrow> if (FNE\<^sub>\<L> \<L> (Ertrm \<sigma>c))\<inter>U={} then Aterm(\<sigma>c) else undeft 
   | None \<Rightarrow> Aterm(RConst b c n))"

text \<open>Uniform substitution for trace-valued constant symbols\<close>
definition tusappconst:: "(ident \<Rightarrow> nat \<Rightarrow> ttrm trmo) usubs"
  where "tusappconst \<sigma> \<L> U c n \<equiv> (case STConsts \<sigma> c n of 
     Some \<sigma>c \<Rightarrow> if (FNE\<^sub>\<L> \<L> (Ettrm \<sigma>c))\<inter>U={} then Aterm(\<sigma>c) else undeft 
   | None \<Rightarrow> Aterm(TConst c n))"

text \<open>Lifts the uniform substitution \<sigma> on arguments to lists of arguments\<close>
fun alusubst_pre :: "(arg \<Rightarrow> arg trmo) usubs \<Rightarrow> (arg list \<Rightarrow> (arg list) trmo) usubs"
  where 
  "alusubst_pre ausubst \<sigma> \<L> U [] = Aterm []"
| "alusubst_pre ausubst \<sigma> \<L> U (e # \<Theta>) = Argso (ausubst \<sigma> \<L> U e) (alusubst_pre ausubst \<sigma> \<L> U \<Theta>)"

text \<open>Combines uniform substitution for variable spaces and argument lists\<close>
definition salusubst_pre :: "(arg \<Rightarrow> arg trmo) usubs \<Rightarrow> (vspace \<Rightarrow> arg list \<Rightarrow> (vspace \<times> arg list) option) usubs"
  where "salusubst_pre ausubst \<sigma> \<L> U Z \<Theta> = (case alusubst_pre ausubst \<sigma> \<L> U \<Theta> of 
      undeft \<Rightarrow> None
    | Some \<sigma>\<Theta> \<Rightarrow> Some (vusubst (SBindrs \<sigma>) Z, \<sigma>\<Theta>))"

text \<open>Congruence lemmas are required for function termination when higher-order callbacks occur.\<close>
lemma alusubst_pre_cong [fundef_cong]: "\<lbrakk> \<sigma>\<^sub>1 = \<sigma>\<^sub>2; \<L>\<^sub>1 = \<L>\<^sub>2; U = V; \<Theta>\<^sub>1 = \<Theta>\<^sub>2;
  \<And>e. e \<in> set \<Theta>\<^sub>1 \<Longrightarrow> \<sigma>\<^sub>A\<^sub>1 \<sigma>\<^sub>1 \<L>\<^sub>1 U e = \<sigma>\<^sub>A\<^sub>2 \<sigma>\<^sub>2 \<L>\<^sub>2 V e \<rbrakk> \<Longrightarrow> alusubst_pre \<sigma>\<^sub>A\<^sub>1 \<sigma>\<^sub>1 \<L>\<^sub>1 U \<Theta>\<^sub>1 = alusubst_pre \<sigma>\<^sub>A\<^sub>2 \<sigma>\<^sub>2 \<L>\<^sub>2 V \<Theta>\<^sub>2"
  apply (induction \<Theta>\<^sub>1 arbitrary: \<Theta>\<^sub>2)
  apply simp by force

lemma salusubst_pre_cong [fundef_cong]: "\<lbrakk> \<sigma>\<^sub>1 = \<sigma>\<^sub>2; \<L>\<^sub>1 = \<L>\<^sub>2; U = V; Z\<^sub>1 = Z\<^sub>2; \<Theta>\<^sub>1 = \<Theta>\<^sub>2;
  \<And>e. e \<in> set \<Theta>\<^sub>1 \<Longrightarrow> \<sigma>\<^sub>A\<^sub>1 \<sigma>\<^sub>1 \<L>\<^sub>1 U e = \<sigma>\<^sub>A\<^sub>2 \<sigma>\<^sub>2 \<L>\<^sub>2 V e \<rbrakk> \<Longrightarrow> salusubst_pre \<sigma>\<^sub>A\<^sub>1 \<sigma>\<^sub>1 \<L>\<^sub>1 U Z\<^sub>1 \<Theta>\<^sub>1 = salusubst_pre \<sigma>\<^sub>A\<^sub>2 \<sigma>\<^sub>2 \<L>\<^sub>2 V Z\<^sub>2 \<Theta>\<^sub>2"
  by (metis salusubst_pre_def alusubst_pre_cong)

text \<open>Uniform substitution for real and trace terms\<close>
function rusubst:: "usubst \<Rightarrow> stat_sem \<Rightarrow> taboo \<Rightarrow> (rtrm \<Rightarrow> rtrm trmo)"
     and tusubst:: "usubst \<Rightarrow> stat_sem \<Rightarrow> taboo \<Rightarrow> (ttrm \<Rightarrow> ttrm trmo)"
     and ausubst:: "usubst \<Rightarrow> stat_sem \<Rightarrow> taboo \<Rightarrow> (arg \<Rightarrow> arg trmo)"
where
  "rusubst \<sigma> \<L> U (RVar x) = Aterm (RVar x)"
| "rusubst \<sigma> \<L> U (RConst b c n) = rusappconst \<sigma> \<L> U b c n"
| "rusubst \<sigma> \<L> U (RFunc b f Z \<Theta>)  = (case salusubst_pre ausubst \<sigma> \<L> U Z \<Theta> of
      None \<Rightarrow> undeft
    | Some (\<sigma>Z, \<sigma>\<Theta>) \<Rightarrow> (case SAllRFuncs \<sigma> b f of 
        Some \<sigma>f \<Rightarrow> if ((FNE\<^sub>\<L> \<L> (Ertrm \<sigma>f)) - (FVN\<^sub>\<L> \<L> \<sigma>Z)) \<inter> U = {} 
          then rusubst (dotsubst_vec \<sigma>\<Theta>) \<L> {} \<sigma>f else undeft 
      | None \<Rightarrow> Aterm(RFunc b f \<sigma>Z \<sigma>\<Theta>)))"
| "rusubst \<sigma> \<L> U (Number r) = Aterm (Number r)"
| "rusubst \<sigma> \<L> U (Plus \<theta> \<eta>) = Pluso (rusubst \<sigma> \<L> U \<theta>) (rusubst \<sigma> \<L> U \<eta>)"
| "rusubst \<sigma> \<L> U (Times \<theta> \<eta>) = Timeso (rusubst \<sigma> \<L> U \<theta>) (rusubst \<sigma> \<L> U \<eta>)"
| "rusubst \<sigma> \<L> U (ChanOf te) = ChanOfo (tusubst \<sigma> \<L> U te)"
| "rusubst \<sigma> \<L> U (ValOf te) = ValOfo (tusubst \<sigma> \<L> U te)"
| "rusubst \<sigma> \<L> U (TimeOf te) = TimeOfo (tusubst \<sigma> \<L> U te)"
| "rusubst \<sigma> \<L> U (LenT te) = LenTo (tusubst \<sigma> \<L> U te)"

| "tusubst \<sigma> \<L> U (TVar h) = Aterm (TVar h)"
| "tusubst \<sigma> \<L> U (TConst c n) = tusappconst \<sigma> \<L> U c n"
| "tusubst \<sigma> \<L> U (TFunc f Z \<Theta>) = (case salusubst_pre ausubst \<sigma> \<L> U Z \<Theta> of
      None \<Rightarrow> undeft
    | Some (\<sigma>Z, \<sigma>\<Theta>) \<Rightarrow> (case STFuncs \<sigma> f of 
        Some \<sigma>f \<Rightarrow> if ((FNE\<^sub>\<L> \<L> (Ettrm \<sigma>f)) - (FVN\<^sub>\<L> \<L> \<sigma>Z)) \<inter> U = {} 
          then tusubst (dotsubst_vec \<sigma>\<Theta>) \<L> {} \<sigma>f else undeft 
      | None \<Rightarrow> Aterm(TFunc f \<sigma>Z \<sigma>\<Theta>)))"
| "tusubst \<sigma> \<L> U Empty = Aterm Empty"
| "tusubst \<sigma> \<L> U (ComItm ch \<theta>\<^sub>1 \<theta>\<^sub>2) = ComItmo ch (rusubst \<sigma> \<L> U \<theta>\<^sub>1) (rusubst \<sigma> \<L> U \<theta>\<^sub>2)"
| "tusubst \<sigma> \<L> U (Concat te\<^sub>1 te\<^sub>2) = Concato (tusubst \<sigma> \<L> U te\<^sub>1) (tusubst \<sigma> \<L> U te\<^sub>2)"
| "tusubst \<sigma> \<L> U (Proj te Y) = Projo (tusubst \<sigma> \<L> U te) (cusubst (SBindrs \<sigma>) Y)"
| "tusubst \<sigma> \<L> U (Access te \<theta>) = Accesso (tusubst \<sigma> \<L> U te) (rusubst \<sigma> \<L> U \<theta>)"

| "ausubst \<sigma> \<L> U (RArg \<theta>) = RArgo (rusubst \<sigma> \<L> U \<theta>)"
| "ausubst \<sigma> \<L> U (TArg te) = TArgo (tusubst \<sigma> \<L> U te)"
  by pat_completeness auto

abbreviation alusubst :: "usubst \<Rightarrow> stat_sem \<Rightarrow> taboo \<Rightarrow> (arg list \<Rightarrow> (arg list) trmo)"
  where "alusubst \<sigma> \<L> U \<Theta> \<equiv> alusubst_pre ausubst \<sigma> \<L> U \<Theta>"

(* uniform substitution for space and argument list (sal) *)
definition salusubst :: "usubst \<Rightarrow> stat_sem \<Rightarrow> taboo \<Rightarrow> (vspace \<Rightarrow> arg list \<Rightarrow> (vspace \<times> arg list) option)"
  where "salusubst \<sigma> \<L> U Z \<Theta> \<equiv> salusubst_pre ausubst \<sigma> \<L> U Z \<Theta>"

(* This simp rule makes salusubst_pre in the usubst algorithms appear as if it was never there *)
lemma salusubst_pre_salusubst [simp]: "salusubst_pre ausubst \<sigma> \<L> U Z \<Theta> = salusubst \<sigma> \<L> U Z \<Theta>"
  by (simp add: salusubst_def)

(* not simp because there are lemmas about salusubst *)
lemma salusubst_simp: "salusubst \<sigma> \<L> U Z \<Theta> = (case alusubst \<sigma> \<L> U \<Theta> of 
    undeft \<Rightarrow> None
  | Some \<sigma>\<Theta> \<Rightarrow> Some (vusubst (SBindrs \<sigma>) Z, \<sigma>\<Theta>))"
  unfolding salusubst_def salusubst_pre_def by presburger



paragraph \<open>Termination of Uniform Substitution for Terms\<close>

lemma usubstsize_rdotsubst: "usubstsize (rdotsubst n \<theta>) = 1" 
  unfolding usubstsize_def rdotsubst_def dom_SQRFuncs dom_SFOL\<^sub>RPsymbs by auto

lemma usubstsize_tdotsubst: "usubstsize (tdotsubst n te) = 1"
  unfolding usubstsize_def tdotsubst_def dom_SQRFuncs dom_SFOL\<^sub>RPsymbs by auto

lemma usubstsize_dotsubst [simp, intro]: "usubstsize (dotsubst n e) = 1"
  apply (cases e)
  by (simp_all add: usubstsize_rdotsubst usubstsize_tdotsubst)

lemma usubstsize_dotsubst_vec_rec [simp, intro]: "usubstsize (dotsubst_vec_rec n \<Theta>) = 1"
  apply (induction \<Theta> arbitrary: n)
   apply simp
  by(simp add: usubstsize_empty_dom_sum)

lemma usubstsize_dotsubst_vec [simp]: "usubstsize (dotsubst_vec \<Theta>) = 1"
  unfolding dotsubst_vec_def by simp

lemma usubstsize_qrfuncs_subst [simp]: "SQRFuncs \<sigma> f = Aterm \<sigma>f \<Longrightarrow> usubstsize \<sigma> = 2"
  unfolding usubstsize_def by auto

lemma usubstsize_rfuncs_subst [simp]: "SRFuncs \<sigma> f = Aterm \<sigma>f \<Longrightarrow> usubstsize \<sigma> = 2"
  unfolding usubstsize_def by auto

lemma usubstsize_all_rfuncs_subst [simp]: "SAllRFuncs \<sigma> b f = Aterm \<sigma>f \<Longrightarrow> usubstsize \<sigma> = 2"
  apply (cases b)
  by (simp_all add: SAllRFuncs_def)

lemma usubstsize_tfuncs_subst [simp]: "STFuncs \<sigma> f = Aterm \<sigma>f \<Longrightarrow> usubstsize \<sigma> = 2"
  unfolding usubstsize_def by auto

lemma usubstsize_gpsymbs_subst [simp]: "SPsymbs \<sigma> p = Aterm \<sigma>p \<Longrightarrow> usubstsize \<sigma> = 2"
  unfolding usubstsize_def by auto

termination
  apply (relation "measures [
    \<lambda>k. usubstsize (case k of 
        Inl(\<sigma>,J,U,\<theta>) \<Rightarrow> \<sigma> 
      | Inr(Inl(\<sigma>,J,U,te)) \<Rightarrow> \<sigma>
      | Inr(Inr(\<sigma>,J,U,a)) \<Rightarrow> \<sigma>), 
    \<lambda>k. (case k of 
        Inl(\<sigma>,J,U,\<theta>) \<Rightarrow> size \<theta> 
      | Inr(Inl(\<sigma>,J,U,te)) \<Rightarrow> size te
      | Inr(Inr(\<sigma>,J,U,a)) \<Rightarrow> size a)
  ]")
  by (simp_all add: list_termination)



paragraph \<open>One-pass Uniform Substitution for Formulas and Programs\<close>

(* Expand let constructs automatically *)
declare Let_def [simp]

text \<open>Bindables for output taboo do not need trace variables, because they are covered as recorders\<close>
abbreviation BNPout :: "stat_sem \<Rightarrow> chp \<Rightarrow> bindr set"
  where "BNPout \<L> \<alpha> \<equiv> BNP\<^sub>\<L> \<L> \<alpha> - \<iota>\<^sub>V (\<iota>\<^sub>T \<V>\<^sub>T)"


fun concrete_vspace_chp :: "chp \<Rightarrow> bool" where
  "concrete_vspace_chp (Chp a Z Y) = (concrete_vspace Z \<and> concrete_cspace Y)"
| "concrete_vspace_chp (\<alpha> \<union>\<union> \<beta>) = (concrete_vspace_chp \<alpha> \<and> concrete_vspace_chp \<beta>)"
| "concrete_vspace_chp (\<alpha> ;; \<beta>) = (concrete_vspace_chp \<alpha> \<and> concrete_vspace_chp \<beta>)"
| "concrete_vspace_chp (Loop \<alpha>) = concrete_vspace_chp \<alpha>"
| "concrete_vspace_chp (Par \<alpha> \<beta>) = (concrete_vspace_chp \<alpha> \<and> concrete_vspace_chp \<beta>)"
| "concrete_vspace_chp _ = True"


text \<open>Uniform substitution for program symbols\<close>
definition usubstchp :: "(ident \<Rightarrow> vspace \<Rightarrow> cspace \<Rightarrow> taboo \<times> chpo) usubs"
  where "usubstchp \<sigma> \<L> U = (\<lambda>a \<sigma>Z \<sigma>Y. (case SChps0 \<sigma> a of
      Some \<sigma>a \<Rightarrow> (U \<union> BNPout \<L> \<sigma>a, 
        if concrete_vspace \<sigma>Z \<and> concrete_cspace \<sigma>Y \<and> concrete_vspace_chp \<sigma>a 
          \<and> CN\<^sub>P \<sigma>a = UCN\<^sub>C \<sigma>Y \<and> BVP\<^sub>\<L> \<L> \<sigma>a \<subseteq> UAV\<^sub>\<L> \<L> \<sigma>Z \<and> FVP\<^sub>\<L> \<L> \<sigma>a \<subseteq> UAV\<^sub>\<L> \<L> \<sigma>Z
        then Achp \<sigma>a else undeft)
    | None \<Rightarrow> (U \<union> BNPout \<L> (Chp a \<sigma>Z \<sigma>Y), Achp (Chp a \<sigma>Z \<sigma>Y))))"

lemma usubstsize_all_psymbs_subst [simp]: "SAllPsymbs \<sigma> b p = Afml \<sigma>p \<Longrightarrow> usubstsize \<sigma> = 2"
  apply (cases b)
   apply (simp_all add: SAllPsymbs_def)
  using usubstsize_def by force

text \<open>Uniform substitution for formulas and programs\<close>
function usubstf:: "usubst \<Rightarrow> stat_sem \<Rightarrow> taboo \<Rightarrow> (fml \<Rightarrow> fmlo)"
     and usubstp:: "usubst \<Rightarrow> stat_sem \<Rightarrow> taboo \<Rightarrow> (chp \<Rightarrow> taboo \<times> chpo)"
where
  "usubstf \<sigma> \<L> U (GPsymb b p Z \<Theta>) = (case salusubst_pre ausubst \<sigma> \<L> U Z \<Theta> of
      None \<Rightarrow> undeft
    | Some (\<sigma>Z, \<sigma>\<Theta>) \<Rightarrow> (case SAllPsymbs \<sigma> b p of 
        Some \<sigma>p \<Rightarrow> if ((FNE\<^sub>\<L> \<L> (Efml \<sigma>p)) - FVN\<^sub>\<L> \<L> \<sigma>Z) \<inter> U = {}
          then usubstf (dotsubst_vec \<sigma>\<Theta>) \<L> {} \<sigma>p else undeft 
      | None \<Rightarrow> Aterm(GPsymb b p \<sigma>Z \<sigma>\<Theta>)))"
| "usubstf \<sigma> \<L> U (Geq \<theta> \<eta>)    = Geqo (rusubst \<sigma> \<L> U \<theta>) (rusubst \<sigma> \<L> U \<eta>)"
| "usubstf \<sigma> \<L> U (Pref te\<^sub>1 te\<^sub>2)    = Prefo (tusubst \<sigma> \<L> U te\<^sub>1) (tusubst \<sigma> \<L> U te\<^sub>2)"
| "usubstf \<sigma> \<L> U (Not \<phi>)      = Noto (usubstf \<sigma> \<L> U \<phi>)"
| "usubstf \<sigma> \<L> U (And \<phi> \<psi>)    = Ando (usubstf \<sigma> \<L> U \<phi>) (usubstf \<sigma> \<L> U \<psi>)"
| "usubstf \<sigma> \<L> U (Exists z \<phi>) = Existso z (usubstf \<sigma> \<L> (U\<union>{Bv z}) \<phi>)"
| "usubstf \<sigma> \<L> U (Box \<alpha> \<psi>) = (let V\<alpha> = usubstp \<sigma> \<L> U \<alpha> 
    in Boxo (snd V\<alpha>) (usubstf \<sigma> \<L> (fst V\<alpha>) \<psi>))"
| "usubstf \<sigma> \<L> U (AcBox \<alpha> A C \<psi>) = (let V\<alpha> = usubstp \<sigma> \<L> U \<alpha> 
    in AcBoxo (snd V\<alpha>) (usubstf \<sigma> \<L> (fst V\<alpha>) A) (usubstf \<sigma> \<L> (fst V\<alpha>) C) (usubstf \<sigma> \<L> (fst V\<alpha>) \<psi>))"
| "usubstf \<sigma> \<L> U (ChanIn ch Y) = ChanIno (rusubst \<sigma> \<L> U ch) (cusubst (SBindrs \<sigma>) Y)"

| "usubstp \<sigma> \<L> U (Chp a Z Y) = usubstchp \<sigma> \<L> U a (vusubst (SBindrs \<sigma>) Z) (cusubst (SBindrs \<sigma>) Y)"
| "usubstp \<sigma> \<L> U (x := \<theta>) = (U\<union>{Bv(Rv x)}, Assigno x (rusubst \<sigma> \<L> U \<theta>))"
| "usubstp \<sigma> \<L> U (x := *) = (U\<union>{Bv(Rv x)}, Achp (x := *))"
| "usubstp \<sigma> \<L> U (Test \<phi>) = (U, Testo (usubstf \<sigma> \<L> U \<phi>))"
| "usubstp \<sigma> \<L> U (Evolution x \<theta> \<phi>) = (U\<union>\<iota>\<^sub>V(bvrident x), 
    Evolutiono x (rusubst \<sigma> \<L> (U\<union>\<iota>\<^sub>V(bvrident x)) \<theta>) (usubstf \<sigma> \<L> (U\<union>\<iota>\<^sub>V(bvrident x)) \<phi>))"
| "usubstp \<sigma> \<L> U (Choice \<alpha> \<beta>) =
    (let V\<alpha> = usubstp \<sigma> \<L> U \<alpha> in
      let V\<beta> = usubstp \<sigma> \<L> U \<beta> in
        (fst V\<alpha>\<union>fst V\<beta>, Choiceo (snd V\<alpha>) (snd V\<beta>)))"
| "usubstp \<sigma> \<L> U (Compose \<alpha> \<beta>) =
    (let V\<alpha> = usubstp \<sigma> \<L> U \<alpha> in
      let W\<beta> = usubstp \<sigma> \<L> (fst V\<alpha>) \<beta> in
        (fst W\<beta>, Composeo (snd V\<alpha>) (snd W\<beta>)))"
| "usubstp \<sigma> \<L> U (Loop \<alpha>) =
    (let V = fst(usubstp \<sigma> \<L> U \<alpha>) in
     (V, Loopo (snd(usubstp \<sigma> \<L> V \<alpha>))))"
| "usubstp \<sigma> \<L> U (Send ch h \<theta>) = (U\<union>{Bv (Tv h), Bc h ch}, Sendo ch h (rusubst \<sigma> \<L> U \<theta>))"
| "usubstp \<sigma> \<L> U (Receive ch h x) = (U\<union>{Bv (Tv h), Bc h ch, Bv (Rv x)}, Achp (Receive ch h x))"
| "usubstp \<sigma> \<L> U (Par \<alpha> \<beta>) =
    (let V\<alpha> = usubstp \<sigma> \<L> U \<alpha> in
      let V\<beta> = usubstp \<sigma> \<L> U \<beta> in
        ((fst V\<alpha>)\<union>(fst V\<beta>), Paro (snd V\<alpha>) (snd V\<beta>)))"
by pat_completeness auto
termination
  apply (relation "measures [
    \<lambda>k. usubstsize (case k of 
        Inl(\<sigma>,J,U,\<phi>) \<Rightarrow> \<sigma> 
      | Inr(\<sigma>,J,U,\<alpha>) \<Rightarrow> \<sigma>), 
    \<lambda>k. (case k of 
        Inl(\<sigma>,J,U,\<phi>) \<Rightarrow> size \<phi> 
      | Inr(\<sigma>,J,U,\<alpha>) \<Rightarrow> size \<alpha>)
  ]")
  by simp_all

text \<open>Induction principles for uniform substitutions\<close>
lemmas usubstappt_rta_induct = rusubst_tusubst_ausubst.induct [case_names RVar RConst RFunc Number Plus Times ChanOf ValOf TimeOf LenT TVar TConst TFunc Empty ComItm Concat Proj Access RArg TArg]
lemmas usubstfp_induct = usubstf_usubstp.induct [case_names GPsymb Geq Pref Not And Exists Box AcBox ChanIn Chp Assign Nondet Test Evolution Choice Compose Loop Send Receive Par]

abbreviation usubstpp :: "usubst \<Rightarrow> stat_sem \<Rightarrow> taboo \<Rightarrow> (chp \<Rightarrow> chp)"
  where "usubstpp \<sigma> \<L> U \<alpha> \<equiv> the(snd(usubstp \<sigma> \<L> U \<alpha>))"

lemma usubst_TT_deff: "usubstf \<sigma> \<L> U TT \<noteq> undeff"
  by (simp add: TT_def)

lemma usubst_test_TT_defp: "snd(usubstp \<sigma> \<L> U (? TT)) \<noteq> undefp"
  by (simp add: Testo_undef usubst_TT_deff)

lemma usubstpp_test_TT: "usubstpp \<sigma> \<L> U (? TT) = ? TT"
  by (simp add: TT_def)
  

  
subsection \<open>Simple Observations for Automation\<close>

paragraph \<open>Observations for Spaces and Argument Lists\<close>

lemma vusubst_simp [simp]: 
  shows "SVarSpaces \<sigma> X = Some \<sigma>X \<Longrightarrow> vusubst \<sigma> (VRConst X) = \<sigma>X"
    and "SVarSpaces \<sigma> X = None \<Longrightarrow> vusubst \<sigma> (VRConst X) = VRConst X"
  by simp_all

lemma cusubst_simp [simp]: 
  shows "SChanSpaces \<sigma> Y = Some \<sigma>Y \<Longrightarrow> cusubst \<sigma> (CConst Y) = \<sigma>Y"
    and "SChanSpaces \<sigma> Y = None \<Longrightarrow> cusubst \<sigma> (CConst Y) = CConst Y"
  by simp_all

lemma salusubst_undeft: "alusubst \<sigma> \<L> U \<Theta> = undeft \<Longrightarrow> salusubst \<sigma> \<L> U Z \<Theta> = undeft"
  by (auto simp add: salusubst_simp salusubst_pre_def option.case_eq_if)

lemma alusubst_conv: "alusubst \<sigma> \<L> U \<Theta> \<noteq> undeft \<Longrightarrow> (\<And>e. e \<in> set \<Theta> \<Longrightarrow> ausubst \<sigma> \<L> U e \<noteq> undeft)"
  apply (induction \<Theta>)  
  using Argso_undef by auto

lemma salusubst_conv: 
  shows "salusubst \<sigma> \<L> U Z \<Theta> \<noteq> undeft \<Longrightarrow> alusubst \<sigma> \<L> U \<Theta> \<noteq> undeft"
     and "salusubst \<sigma> \<L> U Z \<Theta> \<noteq> undeft \<Longrightarrow> (\<And>e. e \<in> set \<Theta> \<Longrightarrow> ausubst \<sigma> \<L> U e \<noteq> undeft)"
  by (meson salusubst_undeft alusubst_conv)+

text \<open>Introduction rule for argument list equality\<close>
lemma alusubst_eqI:
  "(\<And>e. e \<in> set \<Theta> \<Longrightarrow> ausubst \<sigma> \<L> U e = ausubst \<sigma> \<L> V e) \<Longrightarrow> alusubst \<sigma> \<L> U \<Theta> = alusubst \<sigma> \<L> V \<Theta>"
  apply (induction \<Theta>)
  by simp_all 

text \<open>Introduction rule for space and argument list equality\<close>
lemma salusubst_eqI:
  assumes saldeft: "salusubst \<sigma> \<L> U Z \<Theta> \<noteq> undeft \<and> salusubst \<sigma> \<L> V Z \<Theta> \<noteq> undeft"
  assumes IH: "\<And>e. e \<in> set \<Theta> \<Longrightarrow> ausubst \<sigma> \<L> U e \<noteq> undeft \<Longrightarrow> ausubst \<sigma> \<L> V e \<noteq> undeft 
    \<Longrightarrow> ausubst \<sigma> \<L> U e = ausubst \<sigma> \<L> V e"
  shows "salusubst \<sigma> \<L> U Z \<Theta> = salusubst \<sigma> \<L> V Z \<Theta>"
proof -
  have "\<And>e. e \<in> set \<Theta> \<Longrightarrow> ausubst \<sigma> \<L> U e \<noteq> undeft \<and> ausubst \<sigma> \<L> V e \<noteq> undeft" 
    using saldeft salusubst_conv by blast
  hence "\<And>e. e \<in> set \<Theta> \<Longrightarrow> ausubst \<sigma> \<L> U e = ausubst \<sigma> \<L> V e" using IH by presburger
  thus "salusubst \<sigma> \<L> U Z \<Theta> = salusubst \<sigma> \<L> V Z \<Theta>" 
    unfolding salusubst_simp by (metis alusubst_eqI)
qed



paragraph \<open>Observations for Terms\<close>

lemma rusappconst_simp [simp]: 
  shows "SAllRConsts \<sigma> b c n = Some \<sigma>c \<Longrightarrow> (FNE\<^sub>\<L> \<L> (Ertrm \<sigma>c))\<inter>U={} \<Longrightarrow> rusappconst \<sigma> \<L> U b c n = Aterm(\<sigma>c)"
    and "SAllRConsts \<sigma> b c n = None \<Longrightarrow> rusappconst \<sigma> \<L> U b c n = Aterm(RConst b c n)"
    and "SAllRConsts \<sigma> b c n = Some \<sigma>c \<Longrightarrow> (FNE\<^sub>\<L> \<L> (Ertrm \<sigma>c))\<inter>U\<noteq>{} \<Longrightarrow> rusappconst \<sigma> \<L> U b c n = undeft"
  by (simp_all add: rusappconst_def SAllRConsts_def)

lemma rusappconst_conv: "rusappconst \<sigma> \<L> U b c n \<noteq> undeft
  \<Longrightarrow> SAllRConsts \<sigma> b c n = None \<or> (\<exists>\<sigma>c. SAllRConsts \<sigma> b c n = Some \<sigma>c \<and> (FNE\<^sub>\<L> \<L> (Ertrm \<sigma>c))\<inter>U={})"
  unfolding rusappconst_def  
  apply (cases "SAllRConsts \<sigma> b c n")
  unfolding SAllRConsts_def by force+

lemma tusappconst_simp [simp]: 
  shows "STConsts \<sigma> c n = Some \<sigma>c \<Longrightarrow> (FNE\<^sub>\<L> \<L> (Ettrm \<sigma>c))\<inter>U={} \<Longrightarrow> tusappconst \<sigma> \<L> U c n = Aterm(\<sigma>c)"
    and "STConsts \<sigma> c n = None \<Longrightarrow> tusappconst \<sigma> \<L> U c n = Aterm(TConst c n)"
    and "STConsts \<sigma> c n = Some \<sigma>c \<Longrightarrow> (FNE\<^sub>\<L> \<L> (Ettrm \<sigma>c))\<inter>U\<noteq>{} \<Longrightarrow> tusappconst \<sigma> \<L> U c n = undeft"
  by (simp add: tusappconst_def)+

lemma tusappconst_conv: "tusappconst \<sigma> \<L> U c n \<noteq> undeft
  \<Longrightarrow> STConsts \<sigma> c n = None \<or> (\<exists>\<sigma>c. STConsts \<sigma> c n = Some \<sigma>c \<and> (FNE\<^sub>\<L> \<L> (Ettrm \<sigma>c))\<inter>U={})"
  unfolding tusappconst_def 
  apply (cases "STConsts \<sigma> c n")
  by force+

lemma rusubst_func [simp]: 
  shows "SAllRFuncs \<sigma> b f = Some \<sigma>f \<Longrightarrow> salusubst \<sigma> \<L> U Z \<Theta> = Some (\<sigma>Z, \<sigma>\<Theta>) \<Longrightarrow> ((FNE\<^sub>\<L> \<L> (Ertrm \<sigma>f)) - FVN\<^sub>\<L> \<L> \<sigma>Z) \<inter> U = {} 
      \<Longrightarrow> rusubst \<sigma> \<L> U (RFunc b f Z \<Theta>) = rusubst (dotsubst_vec \<sigma>\<Theta>) \<L> {} \<sigma>f"
    and "SAllRFuncs \<sigma> b f = undeft \<Longrightarrow> salusubst \<sigma> \<L> U Z \<Theta> = Some (\<sigma>Z, \<sigma>\<Theta>) \<Longrightarrow> rusubst \<sigma> \<L> U (RFunc b f Z \<Theta>) = Aterm (RFunc b f \<sigma>Z \<sigma>\<Theta>)"
    and "salusubst \<sigma> \<L> U Z \<Theta> = undeft \<Longrightarrow> rusubst \<sigma> \<L> U (RFunc b f Z \<Theta>) = undeft"
  by (simp_all add: option.case_eq_if SAllRFuncs_def)

lemma tusubst_func [simp]: 
  shows "STFuncs \<sigma> f = Some \<sigma>f \<Longrightarrow> salusubst \<sigma> \<L> U Z \<Theta> = Some (\<sigma>Z, \<sigma>\<Theta>) \<Longrightarrow> ((FNE\<^sub>\<L> \<L> (Ettrm \<sigma>f)) - FVN\<^sub>\<L> \<L> \<sigma>Z) \<inter> U = {} 
      \<Longrightarrow> tusubst \<sigma> \<L> U (TFunc f Z \<Theta>) = tusubst (dotsubst_vec \<sigma>\<Theta>) \<L> {} \<sigma>f"
    and "STFuncs \<sigma> f = undeft \<Longrightarrow> salusubst \<sigma> \<L> U Z \<Theta> = Some (\<sigma>Z, \<sigma>\<Theta>) \<Longrightarrow> tusubst \<sigma> \<L> U (TFunc f Z \<Theta>) = Aterm (TFunc f \<sigma>Z \<sigma>\<Theta>)"
    and "salusubst \<sigma> \<L> U Z \<Theta> = undeft \<Longrightarrow> tusubst \<sigma> \<L> U (TFunc f Z \<Theta>) = undeft"
  by (simp_all add: option.case_eq_if)
  
lemma rusubst_func_clash [simp]: "SAllRFuncs \<sigma> b f = Some \<sigma>f \<Longrightarrow> salusubst \<sigma> \<L> U Z \<Theta> = Some (\<sigma>Z, \<sigma>\<Theta>) 
    \<Longrightarrow> ((FNE\<^sub>\<L> \<L> (Ertrm \<sigma>f)) - FVN\<^sub>\<L> \<L> \<sigma>Z) \<inter> U \<noteq> {} \<Longrightarrow> rusubst \<sigma> \<L> U (RFunc b f Z \<Theta>) = undeft"
  apply (cases "alusubst \<sigma> \<L> U \<Theta>")
  by force+

lemma tusubst_func_clash [simp]: "STFuncs \<sigma> f = Some \<sigma>f \<Longrightarrow> salusubst \<sigma> \<L> U Z \<Theta> = Some (\<sigma>Z, \<sigma>\<Theta>)  
    \<Longrightarrow> ((FNE\<^sub>\<L> \<L> (Ettrm \<sigma>f)) - FVN\<^sub>\<L> \<L> \<sigma>Z) \<inter> U \<noteq> {} \<Longrightarrow> tusubst \<sigma> \<L> U (TFunc f Z \<Theta>) = undeft"
  apply (cases "alusubst \<sigma> \<L> U \<Theta>")
  by force+

lemma rusubst_func_conv: "rusubst \<sigma> \<L> U (RFunc b f Z \<Theta>) \<noteq> undeft \<Longrightarrow> salusubst \<sigma> \<L> U Z \<Theta> \<noteq> undeft 
    \<and> (SAllRFuncs \<sigma> b f = None \<or> (\<exists>\<sigma>f. SAllRFuncs \<sigma> b f = Some \<sigma>f \<and> ((FNE\<^sub>\<L> \<L> (Ertrm \<sigma>f)) - FVN\<^sub>\<L> \<L> (vusubst (SBindrs \<sigma>) Z)) \<inter> U = {}))" 
  apply (cases "SAllRFuncs \<sigma> b f")
   apply (meson rusubst_func(3))
  by (metis (no_types, lifting) option.case_eq_if rusubst_func(3) rusubst_func_clash salusubst_simp)
  
lemma tusubst_func_conv: "tusubst \<sigma> \<L> U (TFunc f Z \<Theta>) \<noteq> undeft \<Longrightarrow> salusubst \<sigma> \<L> U Z \<Theta> \<noteq> undeft 
    \<and> (STFuncs \<sigma> f = None \<or> (\<exists>\<sigma>f. STFuncs \<sigma> f = Some \<sigma>f \<and> ((FNE\<^sub>\<L> \<L> (Ettrm \<sigma>f)) - FVN\<^sub>\<L> \<L> (vusubst (SBindrs \<sigma>) Z)) \<inter> U = {}))"
  apply (cases "STFuncs \<sigma> f")
   apply (meson tusubst_func(3))
  by (metis (no_types, lifting) option.case_eq_if tusubst_func(3) tusubst_func_clash salusubst_simp)

lemma usubstappt_plus_conv: "rusubst \<sigma> \<L> U (Plus \<theta> \<eta>) \<noteq> undeft \<Longrightarrow>
  rusubst \<sigma> \<L> U \<theta> \<noteq> undeft \<and> rusubst \<sigma> \<L> U \<eta> \<noteq> undeft"
  by (simp add: Pluso_undef)

lemma usubstappt_times_conv: "rusubst \<sigma> \<L> U (Times \<theta> \<eta>) \<noteq> undeft \<Longrightarrow>
  rusubst \<sigma> \<L> U \<theta> \<noteq> undeft \<and> rusubst \<sigma> \<L> U \<eta> \<noteq> undeft"
  by (simp add: Timeso_undef)

lemma usubstappt_chan_of_conv: "rusubst \<sigma> \<L> U (ChanOf te) \<noteq> undeft \<Longrightarrow> tusubst \<sigma> \<L> U te \<noteq> undeft"
  by (simp add: ChanOfo_undef)

lemma usubstappt_val_of_conv: "rusubst \<sigma> \<L> U (ValOf te) \<noteq> undeft \<Longrightarrow> tusubst \<sigma> \<L> U te \<noteq> undeft"
  by (simp add: ValOfo_undef)

lemma usubstappt_time_of_conv: "rusubst \<sigma> \<L> U (TimeOf te) \<noteq> undeft \<Longrightarrow> tusubst \<sigma> \<L> U te \<noteq> undeft"
  by (simp add: TimeOfo_undef)

lemma usubstappt_lent_conv: "rusubst \<sigma> \<L> U (LenT te) \<noteq> undeft \<Longrightarrow> tusubst \<sigma> \<L> U te \<noteq> undeft"
  by (simp add: LenTo_undef)

lemma usubstappt_concat_conv: "tusubst \<sigma> \<L> U (Concat te\<^sub>1 te\<^sub>2) \<noteq> undeft \<Longrightarrow>
  tusubst \<sigma> \<L> U te\<^sub>1 \<noteq> undeft \<and> tusubst \<sigma> \<L> U te\<^sub>2 \<noteq> undeft"
  by (simp add: Concato_undef)

lemma usubstappt_proj_conv: "tusubst \<sigma> \<L> U (Proj te Y) \<noteq> undeft \<Longrightarrow>
  tusubst \<sigma> \<L> U te \<noteq> undeft"
  by (simp add: Projo_undef)

lemma usubstappt_access_conv: "tusubst \<sigma> \<L> U (Access te \<theta>) \<noteq> undeft \<Longrightarrow>
  tusubst \<sigma> \<L> U te \<noteq> undeft \<and> rusubst \<sigma> \<L> U \<theta> \<noteq> undeft"
  by (simp add: Accesso_undef)



paragraph \<open>Observations for Formulas\<close>

lemma usubstf_gpsymb [simp]: 
  shows "SAllPsymbs \<sigma> b p = Some \<sigma>p \<Longrightarrow> salusubst \<sigma> \<L> U Z \<Theta> = Some (\<sigma>Z, \<sigma>\<Theta>) \<Longrightarrow> ((FNE\<^sub>\<L> \<L> (Efml \<sigma>p)) - FVN\<^sub>\<L> \<L> \<sigma>Z) \<inter> U = {}
      \<Longrightarrow> usubstf \<sigma> \<L> U (GPsymb b p Z \<Theta>) = usubstf (dotsubst_vec \<sigma>\<Theta>) \<L> {} \<sigma>p"
    and "SAllPsymbs \<sigma> b p = undeff \<Longrightarrow> salusubst \<sigma> \<L> U Z \<Theta> = Some (\<sigma>Z, \<sigma>\<Theta>) \<Longrightarrow> usubstf \<sigma> \<L> U (GPsymb b p Z \<Theta>) = Aterm (GPsymb b p \<sigma>Z \<sigma>\<Theta>)"
    and "salusubst \<sigma> \<L> U Z \<Theta> = undeft \<Longrightarrow> usubstf \<sigma> \<L> U (GPsymb b p Z \<Theta>) = undeft" 
  by (simp_all add: option.case_eq_if SAllPsymbs_def)

lemma usubstf_gpsymb_clash [simp]: "SAllPsymbs \<sigma> b p = Some \<sigma>p \<Longrightarrow> salusubst \<sigma> \<L> U Z \<Theta> = Some (\<sigma>Z, \<sigma>\<Theta>) 
    \<Longrightarrow> ((FNE\<^sub>\<L> \<L> (Efml \<sigma>p)) - FVN\<^sub>\<L> \<L> \<sigma>Z) \<inter> U \<noteq> {} \<Longrightarrow> usubstf \<sigma> \<L> U (GPsymb b p Z \<Theta>) = undeft"
  apply (cases "alusubst \<sigma> \<L> U \<Theta>")
  by force+

lemma usubstf_gpsymb_conv: "usubstf \<sigma> \<L> U (GPsymb b p Z \<Theta>) \<noteq> undeft \<Longrightarrow> salusubst \<sigma> \<L> U Z \<Theta> \<noteq> undeft 
    \<and> (SAllPsymbs \<sigma> b p = None \<or> (\<exists>\<sigma>p. SAllPsymbs \<sigma> b p = Some \<sigma>p \<and> (((FNE\<^sub>\<L> \<L> (Efml \<sigma>p)) - FVN\<^sub>\<L> \<L> (vusubst (SBindrs \<sigma>) Z)) \<inter> U = {})))"
  apply (cases "SAllPsymbs \<sigma> b p")
   apply (meson usubstf_gpsymb(3))
  by (metis (no_types, lifting) option.case_eq_if salusubst_simp usubstf_gpsymb(3) usubstf_gpsymb_clash)
  
lemma usubstf_geq: "rusubst \<sigma> \<L> U \<theta> \<noteq> undeft \<Longrightarrow> rusubst \<sigma> \<L> U \<eta> \<noteq> undeft \<Longrightarrow>
  usubstf \<sigma> \<L> U (Geq \<theta> \<eta>) = Afml(Geq (the(rusubst \<sigma> \<L> U \<theta>)) (the(rusubst \<sigma> \<L> U \<eta>)))"
  by fastforce

lemma usubstf_geq_conv: "usubstf \<sigma> \<L> U (Geq \<theta> \<eta>) \<noteq> undeff \<Longrightarrow>
  rusubst \<sigma> \<L> U \<theta> \<noteq> undeft \<and> rusubst \<sigma> \<L> U \<eta> \<noteq> undeft"
  by (simp add: Geqo_undef)

lemma usubstf_pref: "tusubst \<sigma> \<L> U te\<^sub>1 \<noteq> undeft \<Longrightarrow> tusubst \<sigma> \<L> U te\<^sub>2 \<noteq> undeft \<Longrightarrow>
  usubstf \<sigma> \<L> U (Pref te\<^sub>1 te\<^sub>2) = Afml(Pref (the(tusubst \<sigma> \<L> U te\<^sub>1)) (the(tusubst \<sigma> \<L> U te\<^sub>2)))"
  by fastforce

lemma usubstf_pref_conv: "usubstf \<sigma> \<L> U (Pref te\<^sub>1 te\<^sub>2) \<noteq> undeff \<Longrightarrow>
  tusubst \<sigma> \<L> U te\<^sub>1 \<noteq> undeft \<and> tusubst \<sigma> \<L> U te\<^sub>2 \<noteq> undeft"
  by (simp add: Prefo_undef)

lemma usubstf_chan_in_conv: "usubstf \<sigma> \<L> U (ChanIn ch Y) \<noteq> undeff \<Longrightarrow> rusubst \<sigma> \<L> U ch \<noteq> undeft"
  by (simp add: ChanIno_undef)



paragraph \<open>Observations for Programs\<close>

lemma usubstp_chp [simp]: "SChps0 \<sigma> a = Some \<sigma>a \<Longrightarrow> concrete_vspace (vusubst (SBindrs \<sigma>) Z) \<and> concrete_cspace (cusubst (SBindrs \<sigma>) Y) \<and> concrete_vspace_chp \<sigma>a 
  \<Longrightarrow> CN\<^sub>P \<sigma>a = UCN\<^sub>C (cusubst (SBindrs \<sigma>) Y) 
    \<and> BVP\<^sub>\<L> \<L> \<sigma>a \<subseteq> UAV\<^sub>\<L> \<L> (vusubst (SBindrs \<sigma>) Z) 
    \<and> FVP\<^sub>\<L> \<L> \<sigma>a \<subseteq> UAV\<^sub>\<L> \<L> (vusubst (SBindrs \<sigma>) Z)
  \<Longrightarrow> usubstp \<sigma> \<L> U (Chp a Z Y) = (U \<union> BNPout \<L> \<sigma>a, Achp \<sigma>a)"
  by (simp add: usubstchp_def)

lemma usubstapp_chp_conv: "snd(usubstp \<sigma> \<L> U (Chp a Z Y)) \<noteq> undefp 
  \<Longrightarrow> \<sigma>Y = cusubst (SBindrs \<sigma>) Y \<Longrightarrow> \<sigma>Z = vusubst (SBindrs \<sigma>) Z
  \<Longrightarrow> SChps0 \<sigma> a = None 
    \<or> (\<exists>\<sigma>a. SChps0 \<sigma> a = Achp \<sigma>a \<and> concrete_vspace \<sigma>Z \<and> concrete_cspace \<sigma>Y \<and> concrete_vspace_chp \<sigma>a \<and> CN\<^sub>P \<sigma>a = UCN\<^sub>C \<sigma>Y \<and> BVP\<^sub>\<L> \<L> \<sigma>a \<subseteq> UAV\<^sub>\<L> \<L> \<sigma>Z \<and> FVP\<^sub>\<L> \<L> \<sigma>a \<subseteq> UAV\<^sub>\<L> \<L> \<sigma>Z)"  apply (cases "SChps0 \<sigma> a")
  apply (simp_all add: usubstchp_def)
  by (meson option.simps(2))

lemma usubstp_assign_conv: "snd(usubstp \<sigma> \<L> U (x := \<theta>)) \<noteq> undefp \<Longrightarrow> rusubst \<sigma> \<L> U \<theta> \<noteq> undeft"
  by (simp add: Assigno_undef)

lemma usubstp_choice [simp]: "usubstp \<sigma> \<L> U (Choice \<alpha> \<beta>) =
  (fst(usubstp \<sigma> \<L> U \<alpha>)\<union>fst(usubstp \<sigma> \<L> U \<beta>), Choiceo (snd(usubstp \<sigma> \<L> U \<alpha>)) (snd(usubstp \<sigma> \<L> U \<beta>)))"
  by simp

lemma usubstp_choice_conv: "snd(usubstp \<sigma> \<L> U (Choice \<alpha> \<beta>)) \<noteq> undefp \<Longrightarrow>
  snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp \<and> snd(usubstp \<sigma> \<L> U \<beta>) \<noteq> undefp"
  by (simp add: Choiceo_undef)

lemma usubstp_compose [simp]: "usubstp \<sigma> \<L> U (\<alpha> ;; \<beta>) =
  (fst(usubstp \<sigma> \<L> (fst(usubstp \<sigma> \<L> U \<alpha>)) \<beta>), Composeo (snd(usubstp \<sigma> \<L> U \<alpha>)) (snd(usubstp \<sigma> \<L> (fst(usubstp \<sigma> \<L> U \<alpha>)) \<beta>)))"
  by simp

lemma usubstp_compose_conv: "snd(usubstp \<sigma> \<L> U (\<alpha> ;; \<beta>)) \<noteq> undefp \<Longrightarrow>
  snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp \<and> (let V = fst(usubstp \<sigma> \<L> U \<alpha>) in snd(usubstp \<sigma> \<L> V \<beta>) \<noteq> undefp)"
  by (simp add: Composeo_undef)

lemma usubstp_loop [simp]: "usubstp \<sigma> \<L> U (Loop \<alpha>) =
  (fst(usubstp \<sigma> \<L> U \<alpha>), Loopo (snd(usubstp \<sigma> \<L> (fst(usubstp \<sigma> \<L> U \<alpha>)) \<alpha>)))"
  by simp

lemma usubstp_loop_conv: "snd(usubstp \<sigma> \<L> U \<alpha>**) \<noteq> undefp \<Longrightarrow> snd(usubstp \<sigma> \<L> (fst(usubstp \<sigma> \<L> U \<alpha>)) \<alpha>) \<noteq> undefp"
  using snd_conv by fastforce

lemma usubstp_send_conv: "snd(usubstp \<sigma> \<L> U (Send ch h \<theta>)) \<noteq> undefp \<Longrightarrow> rusubst \<sigma> \<L> U \<theta> \<noteq> undeft"
  by (simp add: Sendo_undef)

lemma usubstp_par [simp]: "usubstp \<sigma> \<L> U (\<alpha> par \<beta>) =
  (fst(usubstp \<sigma> \<L> U \<alpha>)\<union>fst(usubstp \<sigma> \<L> U \<beta>), Paro (snd(usubstp \<sigma> \<L> U \<alpha>)) (snd(usubstp \<sigma> \<L> U \<beta>)))"
  by simp

lemma usubstp_par_conv: "snd(usubstp \<sigma> \<L> U (\<alpha> par \<beta>)) \<noteq> undefp 
  \<Longrightarrow> snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp \<and> snd(usubstp \<sigma> \<L> U \<beta>) \<noteq> undefp"
  by (simp add: Paro_undef)



section \<open>Soundness of Uniform Substitution\<close>

subsection \<open>Uniform Substitution is a Function of Deterministic Result\<close>

lemma rusappt_det: "rusubst \<sigma> \<L> U \<theta> \<noteq> undeft \<Longrightarrow> rusubst \<sigma> \<L> V \<theta> \<noteq> undeft \<Longrightarrow> rusubst \<sigma> \<L> U \<theta> = rusubst \<sigma> \<L> V \<theta>"
  and tusappt_det: "tusubst \<sigma> \<L> U te \<noteq> undeft \<Longrightarrow> tusubst \<sigma> \<L> V te \<noteq> undeft \<Longrightarrow> tusubst \<sigma> \<L> U te = tusubst \<sigma> \<L> V te"
  and ausappt_det: "ausubst \<sigma> \<L> U e \<noteq> undeft \<Longrightarrow> ausubst \<sigma> \<L> V e \<noteq> undeft \<Longrightarrow> ausubst \<sigma> \<L> U e = ausubst \<sigma> \<L> V e"
proof (induction \<theta> and te and e arbitrary: U V and U V and U V)
  case (RConst b c n)
  then show ?case
    apply (cases "SAllRConsts \<sigma> b c n") 
     apply (simp add: rusappconst_def SAllRConsts_def) 
    by (metis rusappconst_simp(1,3) rusubst.simps(2))
next
  case (RFunc b f Z \<Theta>)
  hence saldeft: "salusubst \<sigma> \<L> U Z \<Theta> \<noteq> undeft \<and> salusubst \<sigma> \<L> V Z \<Theta> \<noteq> undeft" using rusubst_func_conv by blast
  hence sal_det: "salusubst \<sigma> \<L> U Z \<Theta> = salusubst \<sigma> \<L> V Z \<Theta>" using RFunc.IH salusubst_eqI by presburger
  show ?case
  proof (cases "SAllRFuncs \<sigma> b f")
    case None
    then show ?thesis using sal_det saldeft SAllRFuncs_def by force
  next
    case (Some \<sigma>f)
    then obtain \<sigma>Z \<sigma>\<Theta> where 0: "salusubst \<sigma> \<L> U Z \<Theta> = Aterm (\<sigma>Z, \<sigma>\<Theta>) \<and> salusubst \<sigma> \<L> V Z \<Theta> = Aterm (\<sigma>Z, \<sigma>\<Theta>)"
      using sal_det saldeft by auto
    hence "(FNE\<^sub>\<L> \<L> (Ertrm \<sigma>f) - FVN\<^sub>\<L> \<L> \<sigma>Z) \<inter> U = {}" by (meson RFunc.prems(1) Some rusubst_func_clash)
    then show ?thesis using 0 by (metis RFunc.prems(2) Some rusubst_func(1) rusubst_func_clash)
  qed
next
  case (Plus \<theta> \<eta>)
  then show ?case using Pluso_undef by (metis rusubst.simps(5))
next
  case (Times \<theta> \<eta>)
  then show ?case using Timeso_undef by (metis rusubst.simps(6))
next
  case (ChanOf te)
  hence "tusubst \<sigma> \<L> U te = tusubst \<sigma> \<L> V te" using usubstappt_chan_of_conv by presburger
  then show ?case by auto
next
  case (ValOf te)
  hence "tusubst \<sigma> \<L> U te = tusubst \<sigma> \<L> V te" using usubstappt_val_of_conv by presburger
  then show ?case by auto
next
  case (TimeOf te)
  hence "tusubst \<sigma> \<L> U te = tusubst \<sigma> \<L> V te" using usubstappt_time_of_conv by presburger
  then show ?case by auto
next
  case (LenT te)
  hence "tusubst \<sigma> \<L> U te = tusubst \<sigma> \<L> V te" using usubstappt_lent_conv by presburger
  then show ?case by auto                                         
next
  case (TConst c n)
  then show ?case
  proof (cases "STConsts \<sigma> c n")
    case None
    then show ?thesis by (simp add: tusappconst_def) 
  next
    case (Some a)
    then show ?thesis by (metis TConst.prems(1) TConst.prems(2) tusappconst_simp(1) tusappconst_simp(3) tusubst.simps(2))
  qed 
next
  case (TFunc f Z \<Theta>)
  hence saldeft: "salusubst \<sigma> \<L> U Z \<Theta> \<noteq> undeft \<and> salusubst \<sigma> \<L> V Z \<Theta> \<noteq> undeft" using tusubst_func_conv by blast
  hence sal_det: "salusubst \<sigma> \<L> U Z \<Theta> = salusubst \<sigma> \<L> V Z \<Theta>" using TFunc.IH salusubst_eqI by presburger
  show ?case
  proof (cases "STFuncs \<sigma> f")
    case None
    then show ?thesis using sal_det saldeft by force
  next
    case (Some \<sigma>f)
    then obtain \<sigma>Z \<sigma>\<Theta> where 0: "salusubst \<sigma> \<L> U Z \<Theta> = Aterm (\<sigma>Z, \<sigma>\<Theta>) \<and> salusubst \<sigma> \<L> V Z \<Theta> = Aterm (\<sigma>Z, \<sigma>\<Theta>)"
      using sal_det saldeft by auto
    hence "(FNE\<^sub>\<L> \<L> (Ettrm \<sigma>f) - FVN\<^sub>\<L> \<L> \<sigma>Z) \<inter> U = {}" by (meson TFunc.prems(1) Some tusubst_func_clash)
    then show ?thesis using 0 by (metis TFunc.prems(2) Some tusubst_func(1) tusubst_func_clash)
  qed
next
  case (Concat te\<^sub>1 te\<^sub>2)
  then show ?case using Concato_undef by (metis tusubst.simps(6))
next
  case (Proj te Y)
  then show ?case by (metis tusubst.simps(7) usubstappt_proj_conv)
next
  case (ComItm ch \<theta> \<eta>)
  hence "rusubst \<sigma> \<L> U \<theta> = rusubst \<sigma> \<L> V \<theta> \<and> rusubst \<sigma> \<L> U \<eta> = rusubst \<sigma> \<L> V \<eta>" using ComItmo_undef by auto
  then show ?case by auto
next
  case (Access te \<theta>)
  hence "tusubst \<sigma> \<L> U te = tusubst \<sigma> \<L> V te \<and> rusubst \<sigma> \<L> U \<theta> = rusubst \<sigma> \<L> V \<theta>"
    using usubstappt_access_conv by presburger
  then show ?case by auto
next
  case (RArg \<theta>)
  then show ?case by (metis Unaryo.simps(2) ausubst.simps(1))
next
  case (TArg te)
  then show ?case by (metis Unaryo.simps(2) ausubst.simps(2))
qed (auto)

lemma usubstf_det: "usubstf \<sigma> \<L> U \<phi> \<noteq> undeff \<Longrightarrow> usubstf \<sigma> \<L> V \<phi> \<noteq> undeff \<Longrightarrow> usubstf \<sigma> \<L> U \<phi> = usubstf \<sigma> \<L> V \<phi>"
  and usubstp_det: "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp \<Longrightarrow> snd(usubstp \<sigma> \<L> V \<alpha>) \<noteq> undefp \<Longrightarrow> snd(usubstp \<sigma> \<L> U \<alpha>) = snd(usubstp \<sigma> \<L> V \<alpha>)"
proof (induction \<phi> and \<alpha> arbitrary: U V and U V)
  case (GPsymb b p Z \<Theta>)
  hence saldeft: "salusubst \<sigma> \<L> U Z \<Theta> \<noteq> undeft \<and> salusubst \<sigma> \<L> V Z \<Theta> \<noteq> undeft" using usubstf_gpsymb_conv by blast
  hence sal_det: "salusubst \<sigma> \<L> U Z \<Theta> = salusubst \<sigma> \<L> V Z \<Theta>" using ausappt_det salusubst_eqI by presburger
  show ?case
  proof (cases "SAllPsymbs \<sigma> b p")
    case None
    then show ?thesis using sal_det saldeft SAllPsymbs_def by force
  next
    case (Some \<sigma>p)
    then obtain \<sigma>Z \<sigma>\<Theta> where 0: "salusubst \<sigma> \<L> U Z \<Theta> = Aterm (\<sigma>Z, \<sigma>\<Theta>) \<and> salusubst \<sigma> \<L> V Z \<Theta> = Aterm (\<sigma>Z, \<sigma>\<Theta>)"
      using sal_det saldeft by auto
    hence "(FNE\<^sub>\<L> \<L> (Efml \<sigma>p) - FVN\<^sub>\<L> \<L> \<sigma>Z) \<inter> U = {}" by (meson GPsymb.prems(1) Some usubstf_gpsymb_clash)
    then show ?thesis using 0 by (metis GPsymb.prems(2) Some usubstf_gpsymb(1) usubstf_gpsymb_clash)
  qed
next
  case (Geq x1 x2)
  then show ?case by (metis Geqo_undef rusappt_det usubstf.simps(2))
next
  case (Pref x1 x2)
  then show ?case by (metis Prefo_undef tusappt_det usubstf.simps(3))
next
  case (Not x)
  then show ?case by (metis Noto_undef usubstf.simps(4))
next
  case (And x1 x2)
  then show ?case by (metis Ando_undef usubstf.simps(5))
next
  case (Exists x1 x2)
  then show ?case by (metis Existso_undef usubstf.simps(6))
next
  case (Box x1 x2)
  then show ?case by (metis Boxo_undef usubstf.simps(7))    
next
  case (AcBox \<alpha> A C \<psi>)
  let ?Z\<^sub>U = "fst(usubstp \<sigma> \<L> U \<alpha>)"
  let ?Z\<^sub>V = "fst(usubstp \<sigma> \<L> V \<alpha>)"

  have "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp" and "usubstf \<sigma> \<L> ?Z\<^sub>U A \<noteq> undeff"
     and "usubstf \<sigma> \<L> ?Z\<^sub>U C \<noteq> undeff" and "usubstf \<sigma> \<L> ?Z\<^sub>U \<psi> \<noteq> undeff" 
    using AcBox AcBoxo_undef by simp_all
  moreover have "snd(usubstp \<sigma> \<L> V \<alpha>) \<noteq> undefp" and "usubstf \<sigma> \<L> ?Z\<^sub>V A \<noteq> undeff"
     and "usubstf \<sigma> \<L> ?Z\<^sub>V C \<noteq> undeff" and "usubstf \<sigma> \<L> ?Z\<^sub>V \<psi> \<noteq> undeff" 
    using AcBox AcBoxo_undef by simp_all
  ultimately have "snd(usubstp \<sigma> \<L> U \<alpha>) = snd(usubstp \<sigma> \<L> V \<alpha>)" and "usubstf \<sigma> \<L> ?Z\<^sub>U A = usubstf \<sigma> \<L> ?Z\<^sub>V A"
    and "usubstf \<sigma> \<L> ?Z\<^sub>U C = usubstf \<sigma> \<L> ?Z\<^sub>V C" and "usubstf \<sigma> \<L> ?Z\<^sub>U \<psi> = usubstf \<sigma> \<L> ?Z\<^sub>V \<psi>"
    using AcBox by presburger+
  then show ?case by simp
next
  case (ChanIn \<theta> Y)
  then show ?case by (metis ChanIno_undef rusappt_det usubstf.simps(9))
next
  case (Chp a Y Z)
  then show ?case using usubstapp_chp_conv usubstchp_def by (simp add: option.case_eq_if)
next
  case (Assign x1 x2)
  then show ?case by (metis Assigno_undef rusappt_det sndI usubstp.simps(2))
next
  case (Test x)
  then show ?case by (metis Testo_undef sndI usubstp.simps(4))
next
  case (Evolution x \<theta> \<phi>)
  then show ?case by (metis Evolutiono_undef rusappt_det sndI usubstp.simps(5))
next
  case (Choice x1 x2)
  then show ?case by (metis Choiceo_undef sndI usubstp.simps(6))
next
  case (Compose x1 x2)
  then show ?case by (metis Composeo_undef sndI usubstp.simps(7))
next
  case (Loop x)
  then show ?case by (metis Loopo_undef sndI usubstp.simps(8))
next
  case (Send x1 x2 x3)
  then show ?case by (metis Sendo_undef sndI rusappt_det usubstp.simps(9))
next
  case (Par \<alpha> \<beta>)
  then show ?case by (metis Paro_undef sndI usubstp.simps(11))
qed (auto)



subsection \<open>Uniform Substitutions are Antimonotone in Taboos\<close>

text \<open>The output taboo of uniform substitution for programs always contains the input taboo\<close>
lemma usubst_taboo_pre_fp: "fst(usubstp \<sigma> \<L> U \<alpha>) \<supseteq> U"
  apply (induction \<alpha> arbitrary: U rule: chp_induct) 
  by (auto simp add: usubstchp_def option.case_eq_if)

lemma salusubst_antimonI:
  assumes deft: "salusubst \<sigma> \<L> U Z \<Theta> = Some (\<sigma>Z, \<sigma>\<Theta>)"
  assumes IH: "\<And>e. e \<in> set \<Theta> \<Longrightarrow> V\<subseteq>U \<Longrightarrow> ausubst \<sigma> \<L> U e \<noteq> undeft \<Longrightarrow> ausubst \<sigma> \<L> U e = ausubst \<sigma> \<L> V e"
  shows "V\<subseteq>U \<Longrightarrow> salusubst \<sigma> \<L> U Z \<Theta> = salusubst \<sigma> \<L> V Z \<Theta>"
proof -
  assume 0: "V\<subseteq>U"
  hence "alusubst \<sigma> \<L> U \<Theta> = alusubst \<sigma> \<L> V \<Theta>"
    using deft IH by (metis alusubst_eqI option.distinct(1) salusubst_conv(2))
  thus "salusubst \<sigma> \<L> U Z \<Theta> = salusubst \<sigma> \<L> V Z \<Theta>" using salusubst_simp by simp
qed

lemma rusubst_antimon: "V\<subseteq>U \<Longrightarrow> rusubst \<sigma> \<L> U \<theta> \<noteq> undeft \<Longrightarrow> rusubst \<sigma> \<L> U \<theta> = rusubst \<sigma> \<L> V \<theta>"
  and tusubst_antimon: "V\<subseteq>U \<Longrightarrow> tusubst \<sigma> \<L> U te \<noteq> undeft \<Longrightarrow> tusubst \<sigma> \<L> U te = tusubst \<sigma> \<L> V te"
  and ausubst_antimon: "V\<subseteq>U \<Longrightarrow> ausubst \<sigma> \<L> U e \<noteq> undeft \<Longrightarrow> ausubst \<sigma> \<L> U e = ausubst \<sigma> \<L> V e"
proof (induction \<theta> and te and e)
  case (RVar x)
  then show ?case by simp
next
  case (RConst b c n)
  then show ?case 
  proof (cases "SAllRConsts \<sigma> b c n")
    case None
    then show ?thesis by (simp add: rusappconst_def SAllRConsts_def)
  next
    case (Some \<sigma>c)
    hence bindrcond: "(FNE\<^sub>\<L> \<L> (Ertrm \<sigma>c))\<inter>U={}" by (metis RConst.prems(2) rusappconst_simp(3) rusubst.simps(2))
    hence "(FNE\<^sub>\<L> \<L> (Ertrm \<sigma>c))\<inter>V={}" using RConst by auto
    then show ?thesis by (simp add: Some bindrcond)
  qed  
next
  case (RFunc b f Z \<Theta>)
  then obtain \<sigma>Z \<sigma>\<Theta> where sal: "salusubst \<sigma> \<L> U Z \<Theta> = Some (\<sigma>Z, \<sigma>\<Theta>)" by (metis option.exhaust rusubst_func_conv surj_pair)
  have sal_antimon: "salusubst \<sigma> \<L> U Z \<Theta> = salusubst \<sigma> \<L> V Z \<Theta>" using RFunc sal salusubst_antimonI by blast
  show ?case
  proof (cases "SAllRFuncs \<sigma> b f")
    case None
    then show ?thesis using sal sal_antimon SAllRFuncs_def by auto
  next
    case (Some \<sigma>f)
    hence bindrcond: "((FNE\<^sub>\<L> \<L> (Ertrm \<sigma>f)) - FVN\<^sub>\<L> \<L> \<sigma>Z) \<inter> U = {}" by (meson RFunc.prems(2) rusubst_func_clash sal)
    hence bindrcond: "((FNE\<^sub>\<L> \<L> (Ertrm \<sigma>f)) - FVN\<^sub>\<L> \<L> \<sigma>Z) \<inter> V = {}" using RFunc by auto
    then show ?thesis by (metis RFunc.prems(2) Some rusubst_func(1) rusubst_func_clash sal sal_antimon)
  qed
next
  case (Number r)
  then show ?case by simp
next
  case (Plus x1 x2)
  then show ?case using usubstappt_plus_conv by auto
next
  case (Times x1 x2)
  then show ?case using usubstappt_times_conv by auto
next
  case (ChanOf x)
  then show ?case by force
next
  case (ValOf x)
  then show ?case by force
next
  case (TimeOf x)
  then show ?case by force
next
  case (LenT x)
  then show ?case by force
next
  case (TVar x)
  then show ?case by simp
next
  case (TConst c n)
  then show ?case
  proof (cases "STConsts \<sigma> c n")
    case None
    then show ?thesis by (simp add: rusappconst_def)
  next
    case (Some \<sigma>c)
    hence bindrcond: "(FNE\<^sub>\<L> \<L> (Ettrm \<sigma>c))\<inter>U={}" by (metis TConst.prems(2) tusappconst_simp(3) tusubst.simps(2))
    hence "(FNE\<^sub>\<L> \<L> (Ettrm \<sigma>c))\<inter>V={}" using TConst by auto
    then show ?thesis by (simp add: Some bindrcond)
  qed  
next
  case (TFunc f Z \<Theta>)
  then obtain \<sigma>Z \<sigma>\<Theta> where sal: "salusubst \<sigma> \<L> U Z \<Theta> = Some (\<sigma>Z, \<sigma>\<Theta>)" by (metis option.exhaust tusubst_func_conv surj_pair)
  have sal_antimon: "salusubst \<sigma> \<L> U Z \<Theta> = salusubst \<sigma> \<L> V Z \<Theta>" using TFunc sal salusubst_antimonI by blast
  show ?case
  proof (cases "STFuncs \<sigma> f")
    case None
    then show ?thesis using sal sal_antimon by auto
  next
    case (Some \<sigma>f)
    hence bindrcond: "((FNE\<^sub>\<L> \<L> (Ettrm \<sigma>f)) - FVN\<^sub>\<L> \<L> \<sigma>Z) \<inter> U = {}" by (meson TFunc.prems(2) tusubst_func_clash sal)
    hence bindrcond: "((FNE\<^sub>\<L> \<L> (Ettrm \<sigma>f)) - FVN\<^sub>\<L> \<L> \<sigma>Z) \<inter> V = {}" using TFunc by auto
    then show ?thesis by (metis TFunc.prems(2) Some tusubst_func(1) tusubst_func_clash sal sal_antimon)
  qed
next
  case Empty
  then show ?case by simp
next
  case (ComItm x1 x2 x3)
  then show ?case by force
next
  case (Concat x1 x2)
  then show ?case using usubstappt_concat_conv by auto
next
  case (Proj x1 x2)
  then show ?case using usubstappt_proj_conv by auto
next
  case (Access x1 x2)
  then show ?case using usubstappt_access_conv by auto
next
  case (RArg x)
  then show ?case by force
next
  case (TArg x)
  then show ?case by force
qed

text \<open>Uniform substitutions of programs have monotone taboo output\<close>
lemma usubstp_fst_mono: "U\<subseteq>V \<Longrightarrow> fst(usubstp \<sigma> \<L> U \<alpha>) \<subseteq> fst(usubstp \<sigma> \<L> V \<alpha>)"
proof (induction \<alpha> arbitrary: U V rule: chp_induct)
  case (Chp a Y X Z)
  then show ?case 
    apply (cases "SChps0 \<sigma> a")
    by (auto simp add: usubstchp_def)
next
  case (Choice \<alpha> \<beta>)
  then show ?case by (metis Un_mono fst_pair usubstp_choice) 
next
  case (Compose \<alpha> \<beta>)
  then show ?case by (metis fst_pair usubstp_compose) 
next
  case (Loop \<alpha>)
  then show ?case by (metis fst_pair usubstp_loop)
next
  case (Par \<alpha> \<beta>)
  then show ?case by (simp, blast)
qed (auto)

lemma usubstf_antimon: "V\<subseteq>U \<Longrightarrow> usubstf \<sigma> \<L> U \<phi> \<noteq> undeff \<Longrightarrow> usubstf \<sigma> \<L> V \<phi> \<noteq> undeff"
  and usubstp_antimon: "V\<subseteq>U \<Longrightarrow> snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp \<Longrightarrow> snd(usubstp \<sigma> \<L> V \<alpha>) \<noteq> undefp"
proof (induction \<phi> and \<alpha> arbitrary: U V and U V)                  
  case (GPsymb b p Z \<Theta>)
  then obtain \<sigma>Z \<sigma>\<Theta> where sal: "salusubst \<sigma> \<L> U Z \<Theta> = Some (\<sigma>Z, \<sigma>\<Theta>)"
    by (metis not_Some_eq old.prod.exhaust usubstf_gpsymb(3))
  have sal_antimon: "salusubst \<sigma> \<L> U Z \<Theta> = salusubst \<sigma> \<L> V Z \<Theta>"
    using GPsymb.prems(1) ausubst_antimon sal salusubst_antimonI by presburger
  show ?case
  proof (cases "SAllPsymbs \<sigma> b p")
    case None
    then show ?thesis using sal sal_antimon SAllPsymbs_def by auto
  next
    case (Some \<sigma>f)
    hence bindrcond: "((FNE\<^sub>\<L> \<L> (Efml \<sigma>f)) - FVN\<^sub>\<L> \<L> \<sigma>Z) \<inter> U = {}" by (meson GPsymb.prems(2) usubstf_gpsymb_clash sal)
    hence bindrcond: "((FNE\<^sub>\<L> \<L> (Efml \<sigma>f)) - FVN\<^sub>\<L> \<L> \<sigma>Z) \<inter> V = {}" using GPsymb by auto
    then show ?thesis by (metis GPsymb.prems(2) Some sal sal_antimon usubstf_gpsymb(1) usubstf_gpsymb_clash)
  qed
next
  case (Geq x1 x2)
  then show ?case by (metis usubstf.simps(2) Geqo_undef rusubst_antimon)
next
  case (Pref x1 x2)
  then show ?case by (metis usubstf.simps(3) Prefo_undef tusubst_antimon)
next
  case (Not x)
  then show ?case by (simp add: Noto_undef)
next
  case (And x1 x2)
  then show ?case by (simp add: Ando_undef)
next
  case (Exists x1 x2)
  then show ?case by (simp) (metis insert_mono undeft_equiv Existso_undef)
next
  case (Box x1 x2)
  then show ?case by (metis Boxo_undef usubstf.simps(7) usubstp_fst_mono)
next
  case (AcBox \<alpha> A C \<psi>)
  let ?Z = "\<lambda>U. fst(usubstp \<sigma> \<L> U \<alpha>)"
  have "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp" and AUdef: "usubstf \<sigma> \<L> (?Z U) A \<noteq> undeff"
    and CUdef: "usubstf \<sigma> \<L> (?Z U) C \<noteq> undeff" and PUdef: "usubstf \<sigma> \<L> (?Z U) \<psi> \<noteq> undeff" 
    using AcBox by (simp add: AcBoxo_undef)+
  hence "snd(usubstp \<sigma> \<L> V \<alpha>) \<noteq> undefp" and "usubstf \<sigma> \<L> (?Z V) A \<noteq> undeff"
    and "usubstf \<sigma> \<L> (?Z V) C \<noteq> undeff" and "usubstf \<sigma> \<L> (?Z V) \<psi> \<noteq> undeff" 
    using AcBox apply blast
    by (meson AcBox.IH AcBox.prems(1) AUdef CUdef PUdef usubstp_fst_mono)+
  then show ?case by auto
next
  case (ChanIn ch Y)
  then show ?case using ChanIno_undef rusubst_antimon by simp
next
  case (Chp a Y X Z)
  then show ?case
    apply (cases "SChps0 \<sigma> a")
    by (simp_all add: usubstchp_def)
next
  case (Assign x1 x2)
  then show ?case using Assigno_undef rusubst_antimon by auto
next
  case (Evolution x \<theta> \<phi>)
  hence antimono: "V\<union>\<iota>\<^sub>V(bvrident x) \<subseteq> U\<union>\<iota>\<^sub>V(bvrident x)" by auto

  hence "rusubst \<sigma> \<L> (U\<union>\<iota>\<^sub>V(bvrident x)) \<theta> \<noteq> undeft"
    using Evolutiono_undef Evolution by simp
  hence theta: "rusubst \<sigma> \<L> (V\<union>\<iota>\<^sub>V(bvrident x)) \<theta> \<noteq> undeft" using antimono rusubst_antimon by presburger

  have "usubstf \<sigma> \<L> (U\<union>\<iota>\<^sub>V(bvrident x)) \<phi> \<noteq> undeft"
    using Evolutiono_undef Evolution.prems(2) by auto
  hence "usubstf \<sigma> \<L> (V\<union>\<iota>\<^sub>V(bvrident x)) \<phi> \<noteq> undeft" using antimono Evolution.IH by blast
  
  then show ?case using theta Evolutiono_undef by simp
next
  case (Test x)
  then show ?case by (simp add: Testo_undef)
next
  case (Choice x1 x2)
  then show ?case by (simp add: Choiceo_undef)
next
  case (Compose \<alpha> \<beta>)
  let ?Z = "\<lambda>U. fst(usubstp \<sigma> \<L> U \<alpha>)"
  have "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp" and bUdef: "snd(usubstp \<sigma> \<L> (?Z U) \<beta>) \<noteq> undefp"
    using Compose by (simp add: Composeo_undef)+
  hence "snd(usubstp \<sigma> \<L> V \<alpha>) \<noteq> undefp" and "snd(usubstp \<sigma> \<L> (?Z V) \<beta>) \<noteq> undefp"
    using Compose.IH Compose.prems 
     apply presburger 
    by (meson Compose.IH(2) Compose.prems(1) bUdef usubstp_fst_mono)
  then show ?case by auto
next
  case (Loop x)
  then show ?case by (metis Loopo_undef snd_eqD usubstp.simps(8) usubstp_fst_mono)
next
  case (Send x1 x2 x3)
  then show ?case by (metis Unaryo.simps(2) sndI usubstp.simps(9) rusubst_antimon)
next
  case (Par \<alpha> \<beta>)
  hence "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp" and "snd(usubstp \<sigma> \<L> U \<beta>) \<noteq> undefp" by (meson usubstp_par_conv)+
  then show ?case using Par.IH Par.prems(1) by (simp add: Paro_undef)
qed (simp_all)



subsection \<open>Taboo Lemmas\<close>





 
lemma BVP\<^sub>\<L>_simps [simp]: 
  assumes "algebraically_sound \<L>"
    shows "BVP\<^sub>\<L> \<L> (x := \<theta>) \<subseteq> {Rv x}"
      and "BVP\<^sub>\<L> \<L> (x := *) \<subseteq> {Rv x}"
  using assms unfolding algebraically_sound_def BVP\<^sub>\<L>_def pi_vars_def by auto

lemma CNP\<^sub>\<L>_simps [simp]: 
  assumes "algebraically_sound \<L>"
    shows "CNP\<^sub>\<L> \<L> (x := \<theta>) = {}"
      and "CNP\<^sub>\<L> \<L> (x := *) = {}"
  using assms unfolding algebraically_sound_def CNP\<^sub>\<L>_def pi_comtar_def by auto


lemma algebraically_sound_BNPout:
  "algebraically_sound \<L> \<Longrightarrow> 
   ((\<forall>x \<theta>. BNPout \<L> (x := \<theta>) \<subseteq> {Bv (Rv x)}) 
      \<and> (\<forall>x. BNPout \<L> (x := *) \<subseteq> {Bv (Rv x)})
      \<and> (\<forall>\<phi>. BNPout \<L> (? \<phi>) \<subseteq> {})
      \<and> (\<forall>x \<theta> \<phi>. BNPout \<L> (Evolution x \<theta> \<phi>) \<subseteq> \<iota>\<^sub>V (bvrident x))
      \<and> (\<forall>\<alpha> \<beta>. BNPout \<L> (\<alpha> \<union>\<union> \<beta>) \<subseteq> BNPout \<L> \<alpha> \<union> BNPout \<L> \<beta>)
      \<and> (\<forall>\<alpha> \<beta>. BNPout \<L> (\<alpha> ;; \<beta>) \<subseteq> BNPout \<L> \<alpha> \<union> BNPout \<L> \<beta>)
      \<and> (\<forall>\<alpha>. BNPout \<L> (Loop \<alpha>) \<subseteq> BNPout \<L> \<alpha>)
      \<and> (\<forall>\<alpha> \<beta>. BNPout \<L> (\<alpha> par \<beta>) \<subseteq> BNPout \<L> \<alpha> \<union> BNPout \<L> \<beta>))"
  unfolding algebraically_sound_def
  apply auto
  apply blast+
  by (meson UnE subset_iff)

text \<open>Lemma 13 of \<^url>\<open>https://doi.org/10.1007/978-3-031-38499-8_6\<close>\<close>
lemma output_taboo_correct: 
  assumes sound_stat: "is_sound_stat_sem \<L>"
  assumes undefp: "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp"
  defines usubs:  "\<sigma>\<alpha> \<equiv> usubstpp \<sigma> \<L> U \<alpha>"
  defines taboo:  "Z \<equiv> fst(usubstp \<sigma> \<L> U \<alpha>)"      
    shows "Z \<supseteq> U \<union> BNPout \<L> \<sigma>\<alpha>"
using sound_stat undefp usubs taboo proof (induction \<alpha> arbitrary: U Z \<sigma>\<alpha> rule: chp_induct)
  case (Chp a Z Y)
  then show ?case 
    apply (cases "SChps0 \<sigma> a")
     apply (simp_all add: usubstchp_def)
    by (metis option.distinct(1))
next
  case (Assign x \<theta>)
  hence "usubstpp \<sigma> \<L> U (x := \<theta>) = Assign x (the(rusubst \<sigma> \<L> U \<theta>))" using Assigno_undef by auto
  hence "BNP\<^sub>\<L> \<L> (usubstpp \<sigma> \<L> U (x := \<theta>)) \<subseteq> {Bv (Rv x)}"
    using Assign is_sound_stat_sem_def algebraically_sound_def by simp
  thus ?case by auto
next
  case (Nondet x)
  hence "usubstpp \<sigma> \<L> U (x := *) = x := *" by auto
  thus ?case using Nondet is_sound_stat_sem_def algebraically_sound_def by auto
next
  case (Test \<phi>)
  hence "usubstpp \<sigma> \<L> U (? \<phi>) = ? (the(usubstf \<sigma> \<L> U \<phi>))" 
    by (metis Unaryo.elims option.sel snd_pair usubstp.simps(4))
  thus ?case using Test is_sound_stat_sem_def algebraically_sound_def by simp
next
  case (Evolution x \<theta> \<phi>)
  hence "usubstpp \<sigma> \<L> U (Evolution x \<theta> \<phi>) = (Evolution x (the(rusubst \<sigma> \<L> (U\<union>\<iota>\<^sub>V(bvrident x)) \<theta>)) (the(usubstf \<sigma> \<L> (U\<union>\<iota>\<^sub>V(bvrident x)) \<phi>)))" 
    using Evolutiono_undef by auto
  hence "BNP\<^sub>\<L> \<L> (usubstpp \<sigma> \<L> U (Evolution x \<theta> \<phi>)) \<subseteq> \<iota>\<^sub>V (bvrident x)"
    using Evolution is_sound_stat_sem_def algebraically_sound_def by simp
  thus ?case by auto
next
  case (Choice \<alpha> \<beta>)
  hence defp: "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp \<and> snd(usubstp \<sigma> \<L> U \<beta>) \<noteq> undefp" 
    using usubstp_choice_conv by simp

  let ?\<sigma>\<alpha> = "usubstpp \<sigma> \<L> U \<alpha>"
  let ?\<sigma>\<beta> = "usubstpp \<sigma> \<L> U \<beta>"

  have "fst(usubstp \<sigma> \<L> U \<alpha>) \<supseteq> U \<union> BNPout \<L> ?\<sigma>\<alpha>" using Choice defp by simp
  moreover have "fst(usubstp \<sigma> \<L> U \<beta>) \<supseteq> U \<union> BNPout \<L> ?\<sigma>\<beta>" using Choice defp by presburger
  ultimately have "fst(usubstp \<sigma> \<L> U \<alpha>) \<union> fst(usubstp \<sigma> \<L> U \<beta>) \<supseteq> U \<union> BNPout \<L> (?\<sigma>\<alpha> \<union>\<union> ?\<sigma>\<beta>)" 
    using Choice is_sound_stat_sem_def algebraically_sound_BNPout by blast
  thus ?case using defp by auto
next
  case (Compose \<alpha> \<beta>)
  let ?V = "fst(usubstp \<sigma> \<L> U \<alpha>)"
  let ?\<sigma>\<alpha> = "usubstpp \<sigma> \<L> U \<alpha>"
  let ?\<sigma>\<beta> = "usubstpp \<sigma> \<L> ?V \<beta>"

  have defp: "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp \<and> snd(usubstp \<sigma> \<L> ?V \<beta>) \<noteq> undefp" using Compose usubstp_compose_conv by simp
  hence "?V \<supseteq> U \<union> BNPout \<L> ?\<sigma>\<alpha>" using Compose by simp
  moreover have "fst(usubstp \<sigma> \<L> ?V \<beta>) \<supseteq> ?V \<union> BNPout \<L> ?\<sigma>\<beta>" using Compose defp by presburger
  ultimately have  "fst(usubstp \<sigma> \<L> ?V \<beta>) \<supseteq> U \<union> BNPout \<L> ?\<sigma>\<alpha> \<union> BNPout \<L> ?\<sigma>\<beta>" using BNP_choice_bound by blast
  hence "fst(usubstp \<sigma> \<L> ?V \<beta>) \<supseteq> U \<union> BNPout \<L> (?\<sigma>\<alpha> ;; ?\<sigma>\<beta>)" 
    using Compose is_sound_stat_sem_def algebraically_sound_BNPout by blast
  thus ?case using defp by auto
next
  case (Loop \<alpha>)
  let ?V = "fst(usubstp \<sigma> \<L> U \<alpha>)"
  let ?\<sigma>\<alpha> = "usubstp \<sigma> \<L> ?V \<alpha>"

  have defp: "snd(usubstp \<sigma> \<L> ?V \<alpha>) \<noteq> undefp" using Loop usubstp_loop_conv by presburger
  hence "?V \<supseteq> U \<union> BNPout \<L> (the(snd ?\<sigma>\<alpha>))" by (metis Loop(1,2) usubst_taboo_pre_fp usubstp_antimon usubstp_det)
  hence "?V \<supseteq> U \<union> BNPout \<L> ((the(snd ?\<sigma>\<alpha>))**)" 
    using Loop is_sound_stat_sem_def algebraically_sound_def by fast
  thus ?case using defp by auto
next
  case (Send ch h \<theta>)
  hence "usubstpp \<sigma> \<L> U (Send ch h \<theta>) = Send ch h (the(rusubst \<sigma> \<L> U \<theta>))" using Sendo_undef by auto
  hence "BNP\<^sub>\<L> \<L> (usubstpp \<sigma> \<L> U (Send ch h \<theta>)) \<subseteq> {Bv (Tv h), Bc h ch}"
    using Send is_sound_stat_sem_def algebraically_sound_def by simp
  thus ?case by auto
next
  case (Receive ch h x)
  hence "BNP\<^sub>\<L> \<L> (usubstpp \<sigma> \<L> U (Receive ch h x)) \<subseteq> {Bv (Tv h), Bc h ch, Bv (Rv x)}" 
    using Receive unfolding is_sound_stat_sem_def algebraically_sound_def by fastforce
  thus ?case by auto
next
  case (Par \<alpha> \<beta>)
  hence defp: "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp \<and> snd(usubstp \<sigma> \<L> U \<beta>) \<noteq> undefp" using usubstp_par_conv by simp

  let ?\<sigma>\<alpha> = "usubstpp \<sigma> \<L> U \<alpha>"
  let ?\<sigma>\<beta> = "usubstpp \<sigma> \<L> U \<beta>"

  have "fst(usubstp \<sigma> \<L> U \<alpha>) \<supseteq> U \<union> BNPout \<L> ?\<sigma>\<alpha>" using Par defp by presburger
  moreover have "fst(usubstp \<sigma> \<L> U \<beta>) \<supseteq> U \<union> BNPout \<L> ?\<sigma>\<beta>" using Par defp by presburger
  ultimately have  "fst(usubstp \<sigma> \<L> U \<alpha>) \<union> fst(usubstp \<sigma> \<L> U \<beta>) \<supseteq> U \<union> BNPout \<L> (?\<sigma>\<alpha> par ?\<sigma>\<beta>)" 
    using Par is_sound_stat_sem_def algebraically_sound_BNPout by fast
  thus ?case using defp by auto
qed

lemma output_taboo_compl [simp]: "is_sound_stat_sem \<L> \<Longrightarrow> snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp 
  \<Longrightarrow> \<sigma>\<alpha> = usubstpp \<sigma> \<L> U \<alpha> \<Longrightarrow> Z = fst(usubstp \<sigma> \<L> U \<alpha>) \<Longrightarrow> -Z \<subseteq> -U \<and> -Z \<subseteq> -BNPout \<L> \<sigma>\<alpha>"
  using output_taboo_correct by blast

lemma output_taboo_compl_pi [simp]: "is_sound_stat_sem \<L> \<Longrightarrow> snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp 
  \<Longrightarrow> \<sigma>\<alpha> = usubstpp \<sigma> \<L> U \<alpha> \<Longrightarrow> Z = fst(usubstp \<sigma> \<L> U \<alpha>) \<Longrightarrow> -Z \<subseteq> -(BNPout \<L> \<sigma>\<alpha>)"
  using output_taboo_compl by auto

lemma output_taboo_fp_remainder: "snd(usubstp \<sigma> \<L> V \<alpha>) \<noteq> undefp \<Longrightarrow> V\<supseteq>U \<Longrightarrow> fst(usubstp \<sigma> \<L> V \<alpha>) = fst(usubstp \<sigma> \<L> U \<alpha>) \<union> (V-U)"
proof (induction \<alpha> arbitrary: V U rule: chp_induct)
  case (Chp a Y X Z)
  then show ?case
    apply (cases "SChps0 \<sigma> a")
    using usubstchp_def by auto
next
  case (Choice \<alpha> \<beta>)
  then show ?case using usubstp_choice_conv by auto
next
  case (Compose \<alpha> \<beta>)
  let ?W = "\<lambda>V. fst(usubstp \<sigma> \<L> V \<alpha>)"
  have betadef: "snd (usubstp \<sigma> \<L> (?W V) \<beta>) \<noteq> undefp" by (meson Compose.prems(1) usubstp_compose_conv)
  have 0: "?W V \<supseteq> ?W U" using Compose.prems(2) usubstp_fst_mono by auto
  have 1: "(?W V) - (?W U) = fst(usubstp \<sigma> \<L> U \<alpha>) \<union> (V-U) - fst(usubstp \<sigma> \<L> U \<alpha>)" 
    using Compose.IH(1) Compose.prems(1) Compose.prems(2) usubstp_compose_conv by blast

  hence "fst(usubstp \<sigma> \<L> V (\<alpha>;;\<beta>)) = fst(usubstp \<sigma> \<L> (?W V) \<beta>)" by auto
  also have "... = (fst(usubstp \<sigma> \<L> (?W U) \<beta>)) \<union> ((?W V) - (?W U))" 
    using 0 Compose.IH betadef by simp
  also have "... = (fst(usubstp \<sigma> \<L> (?W U) \<beta>)) \<union> (V-U)"
    by (metis (no_types, lifting) 1 Diff_partition Un_assoc Un_upper1 sup.orderE usubst_taboo_pre_fp)
  also have "... = (fst(usubstp \<sigma> \<L> U (\<alpha>;;\<beta>)) \<union> (V-U))" by force
   finally show ?case .
next
  case (Loop \<alpha>)
  then show ?case by (metis fst_pair usubst_taboo_pre_fp usubstp_antimon usubstp.simps(8) usubstp_loop_conv)
next
  case (Par \<alpha> \<beta>)
  then show ?case using usubstp_par_conv by auto
qed (auto)

lemma output_taboo_fp: "snd(usubstp \<sigma> \<L> (fst(usubstp \<sigma> \<L> U \<alpha>)) \<alpha>) \<noteq> undefp \<Longrightarrow> fst(usubstp \<sigma> \<L> (fst(usubstp \<sigma> \<L> U \<alpha>)) \<alpha>) = fst(usubstp \<sigma> \<L> U \<alpha>)"
  by (metis Diff_subset sup.absorb1 output_taboo_fp_remainder usubst_taboo_pre_fp)



subsection \<open>One-pass Uniform Substitution for Syntactic Repetition\<close>

text \<open>This section proves that uniform substitution applied to syntactic repetition yields the 
expected result\<close>

lemma usubstp_Repeat_conv: "snd(usubstp \<sigma> \<L> (fst(usubstp \<sigma> \<L> U \<alpha>)) \<alpha>) \<noteq> undefp 
  \<Longrightarrow> snd(usubstp \<sigma> \<L> (fst(usubstp \<sigma> \<L> U \<alpha>)) (Repeat \<alpha> n)) \<noteq> undefp"
proof (induction n arbitrary: U)
  case 0
  then show ?case by (simp add: TT_def)
next
  case (Suc n)
  hence "snd(usubstp \<sigma> \<L> (fst (usubstp \<sigma> \<L> U \<alpha>)) \<alpha>) \<noteq> undefp" by simp
  hence "snd(usubstp \<sigma> \<L> (fst (usubstp \<sigma> \<L> (fst(usubstp \<sigma> \<L> U \<alpha>)) \<alpha>)) \<alpha>) \<noteq> undefp" 
    using output_taboo_fp by auto
  hence "snd(usubstp \<sigma> \<L> (fst(usubstp \<sigma> \<L> (fst(usubstp \<sigma> \<L> U \<alpha>)) \<alpha>)) (Repeat \<alpha> n)) \<noteq> undefp" 
    using Suc by blast
  then show ?case using Suc gr0_conv_Suc by fastforce
qed
  
lemma usubstp_Repeat: "snd(usubstp \<sigma> \<L> (fst(usubstp \<sigma> \<L> U \<alpha>)) \<alpha>) \<noteq> undefp 
  \<Longrightarrow> usubstpp \<sigma> \<L> U (Repeat \<alpha> n) = Repeat (usubstpp \<sigma> \<L> U \<alpha>) n"
proof (induction n arbitrary: U)
  case 0
  then show ?case using usubstpp_test_TT by simp
next
  case (Suc n)
  hence alphadefp: "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp" by (meson usubst_taboo_pre_fp usubstp_antimon)
  let ?V = "fst(usubstp \<sigma> \<L> U \<alpha>)"
  have repeatdefp: "snd(usubstp \<sigma> \<L> ?V (Repeat \<alpha> n)) \<noteq> undefp" by (simp add: Suc.prems usubstp_Repeat_conv)
    
  have "usubstpp \<sigma> \<L> U (Repeat \<alpha> (Suc n)) = ((usubstpp \<sigma> \<L> U \<alpha>) ;; (usubstpp \<sigma> \<L> ?V (Repeat \<alpha> n)))" 
    using alphadefp repeatdefp by force
  also have "... = ((usubstpp \<sigma> \<L> U \<alpha>) ;; (Repeat (usubstpp \<sigma> \<L> ?V \<alpha>) n))" 
    by (simp add: Suc.IH Suc.prems output_taboo_fp)
  also have "... = ((usubstpp \<sigma> \<L> U \<alpha>) ;; (Repeat (usubstpp \<sigma> \<L> U \<alpha>) n))" 
    by (metis Suc.prems alphadefp usubstp_det)
  also have "... = (Repeat (usubstpp \<sigma> \<L> U \<alpha>) (Suc n))" using Suc gr0_conv_Suc by force
  finally show ?case .
qed



subsection \<open>Substitution Adjoints\<close>

paragraph \<open>Modification of Interpretations\<close>

text \<open>Since Rdot is sufficient for real terms and pure real polynomials in dot substitutions, rrepc 
only modifies the interpretation of general real constant symbols.\<close> 
definition rrepc :: "interp \<Rightarrow> ident \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> interp"
  where "rrepc I f n d \<equiv> I \<lparr> AllRConsts := \<lambda>b c m. if \<not>b \<and> c=f \<and> m=n then d else AllRConsts I b c m \<rparr>"
definition trepc :: " interp \<Rightarrow> ident \<Rightarrow> nat \<Rightarrow> trace \<Rightarrow> interp"
  where "trepc I f n \<tau> \<equiv> I \<lparr> TConsts := \<lambda>c m. if c=f \<and> m=n then \<tau> else TConsts I c m \<rparr>"

text \<open>The modified interpretation \<open>repc I c n d\<close> replaces the interpretation of the constant symbol 
\<open>c\<^sub>n\<close> in the interpretation \<open>I\<close> with \<open>d\<close>\<close>
fun repc :: "interp \<Rightarrow> ident \<Rightarrow> nat \<Rightarrow> vals \<Rightarrow> interp"
  where
  "repc I c n (Rp d) = rrepc I c n d"
| "repc I c n (Tp d) = trepc I c n d"

text \<open>\<open>repc_vec I [(c\<^sup>1, 1, d\<^sub>1), \<dots>, (c\<^sup>n, n, d\<^sub>n)]\<close> replaces the interpretation of the constant symbols 
\<open>(c\<^sup>1)\<^sub>1, \<dots>, (c\<^sup>n)\<^sub>n\<close> in the interpretation \<open>I\<close> with the values \<open>d\<^sub>1, \<dots>, d\<^sub>n\<close>\<close>
fun repc_vec :: "interp \<Rightarrow> (ident \<times> nat \<times> vals) list \<Rightarrow> interp"
  where                                     
  "repc_vec I [] = I"
| "repc_vec I (id0 # idl) = (let (f,n,d) = id0 in repc_vec (repc I f n d) idl)"

fun dot_repl_vec_rec :: "nat \<Rightarrow> vals list \<Rightarrow> (ident \<times> nat \<times> vals) list"
  where
  "dot_repl_vec_rec n [] = []"
| "dot_repl_vec_rec n (d # dl) = ((dotid, n, d) # (dot_repl_vec_rec (n+1) dl))"

text \<open>Creates a vector of replacements for the reserved dot constant symbol from a list of values\<close>
definition dot_repl_vec :: "vals list \<Rightarrow> (ident \<times> nat \<times> vals) list"
  where "dot_repl_vec d = dot_repl_vec_rec 0 d"
                                   


paragraph \<open>Substitution Adjoints for Binder Interpretations\<close>

abbreviation badj0_BConsts\<^sub>R\<^sub>V where "badj0_BConsts\<^sub>R\<^sub>V \<sigma> J\<^sub>0 J \<equiv> (\<lambda>Z. (case SVarSpaces \<sigma> Z of 
  None \<Rightarrow> BConsts\<^sub>R\<^sub>V J Z | 
  Some \<sigma>Z \<Rightarrow> \<pi>\<^sub>R (vspace_sem J\<^sub>0 \<sigma>Z)))"

abbreviation badj0_BConsts\<^sub>\<Omega> where "badj0_BConsts\<^sub>\<Omega> \<sigma> J\<^sub>0 J \<equiv> (\<lambda>Y. (case SChanSpaces \<sigma> Y of 
    None \<Rightarrow> (BConsts\<^sub>\<Omega> J) Y | 
    Some \<sigma>Y \<Rightarrow> cspace_sem J\<^sub>0 \<sigma>Y))"

text \<open>The adjoint badj0 of \<open>J\<close> at \<open>J\<^sub>0\<close> changes the interpretation of space symbols by \<open>J\<close> according 
to the substitution \<sigma> evaluating the replacements in \<open>J\<^sub>0\<close>\<close>
definition badj0 :: "busubst \<Rightarrow> binterp \<Rightarrow> (binterp \<Rightarrow> binterp)"
  where "badj0 \<sigma> J\<^sub>0 J \<equiv> mkbinterp (badj0_BConsts\<^sub>\<Omega> \<sigma> J\<^sub>0 J) (badj0_BConsts\<^sub>R\<^sub>V \<sigma> J\<^sub>0 J)"

text \<open>Adjoint interpretation \<open>badjoint \<sigma> I\<close> to \<open>\<sigma>\<close> of interpretation \<open>I\<close>\<close>
definition badjoint :: "busubst \<Rightarrow> binterp \<Rightarrow> binterp"
  where "badjoint \<sigma> J = badj0 \<sigma> J J"

lemma badj0_empty_usubst [simp]: "badj0 empty_busubst J\<^sub>0 J = J"
  apply (rule binterp.equality)
  by (auto simp add: badj0_def empty_busubst_def)

lemma badjoint_empty_usubst [simp]: "badjoint empty_busubst J = J"
  unfolding badjoint_def by simp

lemma SBindrs_usubst_sum_dist [simp, intro]: "SBindrs (\<sigma>\<^sub>1 +++ \<sigma>\<^sub>2) = SBindrs \<sigma>\<^sub>1 ++\<^sub>B SBindrs \<sigma>\<^sub>2"
  unfolding usubst_sum_def by simp

lemma SBindrs_rdotsubst_empty [simp]: "SBindrs (rdotsubst n \<theta>) = empty_busubst"
  by (simp add: rdotsubst_def)

lemma SBindrs_tdotsubst_empty [simp]: "SBindrs (tdotsubst n te) = empty_busubst"
  by (simp add: tdotsubst_def)

lemma SBindrs_dotsubst_empty [simp, intro]: "SBindrs (dotsubst n e) = empty_busubst"
  by (cases e, simp_all)

lemma SBindrs_dotsubst_vec_rec_empty [simp]: "SBindrs (dotsubst_vec_rec n \<Theta>) = empty_busubst"
  by (induction \<Theta> arbitrary: n) (simp_all)

text \<open>A substitution that only replaces the special real-valued or trace-valued constant symbol dot 
does not replace any space constant symbol\<close>
lemma SBindrs_dotsubst_vec_empty [simp]: "SBindrs (dotsubst_vec \<Theta>) = empty_busubst"
  unfolding dotsubst_vec_def by simp



paragraph \<open>General Substitution Adjoints\<close>

text \<open>The adjoint interpretation \<open>adjoint \<sigma> I \<omega>\<close> changes the interpretation of a symbol \<open>f\<close> by \<open>I\<close> 
according to the replacement \<open>\<sigma>f\<close> of \<open>f\<close> by \<open>\<sigma>\<close>. The free variables of the replacement obtain their 
values from the state \<open>\<omega>\<close> that is a variation of the local state \<open>\<nu>\<close> on the variables bound by the 
context. The free variables of arguments of f obtain their value from the local state \<open>\<nu>\<close>.
That is, the free variables of the arguments \<Theta> of a function symbol f(Z)(\<Theta>) are evaluated by the 
local state \<open>\<nu>\<close>. Since the space Z specifies additional free variables of f, the free variables of 
the replacement \<sigma>f obtain their values from \<open>\<omega>\<close> only as far as they are not contained in Z and are
evaluated by the local state otherwise. This is why the following abbreviations merge \<open>\<omega>\<close> with the
local state on Z.\<close>

definition rprdnl :: "interp \<Rightarrow> state \<Rightarrow> rtrm \<Rightarrow> (variable set \<Rightarrow> state \<Rightarrow> vals list \<Rightarrow> real)"
  where "rprdnl I\<^sub>0 \<omega> \<sigma>f \<equiv> (\<lambda>Z \<nu> d. rtrm_sem (repc_vec I\<^sub>0 (dot_repl_vec d)) \<sigma>f (lmerge \<nu> \<omega> Z))"

definition tprdnl :: "interp \<Rightarrow> state \<Rightarrow> ttrm \<Rightarrow> (variable set \<Rightarrow> state \<Rightarrow> vals list \<Rightarrow> trace)"
  where "tprdnl I\<^sub>0 \<omega> \<sigma>f \<equiv> (\<lambda>Z \<nu> d. ttrm_sem (repc_vec I\<^sub>0 (dot_repl_vec d)) \<sigma>f (lmerge \<nu> \<omega> Z))"

definition fprdnl :: "interp \<Rightarrow> state \<Rightarrow> fml \<Rightarrow> (variable set \<Rightarrow> state \<Rightarrow> vals list \<Rightarrow> bool)"
  where "fprdnl I\<^sub>0 \<omega> \<sigma>p \<equiv> (\<lambda>Z \<nu> d. (lmerge \<nu> \<omega> Z) \<in> fml_sem (repc_vec I\<^sub>0 (dot_repl_vec d)) \<sigma>p)"

abbreviation adj0_AllRConsts where "adj0_AllRConsts \<sigma> I\<^sub>0 I \<omega> \<equiv> (\<lambda>b c n. (case SAllRConsts \<sigma> b c n of 
  None \<Rightarrow> AllRConsts I b c n | 
  Some \<sigma>c \<Rightarrow> rtrm_sem I\<^sub>0 \<sigma>c \<omega>))"

text \<open>\<open>adj0_AllRFuncs \<sigma> I\<^sub>0 I \<omega>\<close> changes the interpretation of the function symbol f by \<open>I\<close> to the 
value of the substitution result \<open>\<sigma>f\<close> evaluated in \<open>I\<^sub>0, \<omega>\<close>\<close>
abbreviation adj0_AllRFuncs where "adj0_AllRFuncs \<sigma> I\<^sub>0 I \<omega> \<equiv> (\<lambda>b f. (case SAllRFuncs \<sigma> b f of
  None \<Rightarrow> AllRFuncs I b f | 
  Some \<sigma>f \<Rightarrow> mkpinterp (rprdnl I\<^sub>0 \<omega> \<sigma>f)))"

abbreviation adj0_TConsts where "adj0_TConsts \<sigma> I\<^sub>0 I \<omega> \<equiv> (\<lambda>c n. (case STConsts \<sigma> c n of 
  None \<Rightarrow> TConsts I c n | 
  Some \<sigma>c \<Rightarrow> ttrm_sem I\<^sub>0 \<sigma>c \<omega>))"

abbreviation adj0_TFuncs where "adj0_TFuncs \<sigma> I\<^sub>0 I \<omega> \<equiv> (\<lambda>f. (case STFuncs \<sigma> f of 
  None \<Rightarrow> TFuncs I f | 
  Some \<sigma>f \<Rightarrow> mkpinterp (tprdnl I\<^sub>0 \<omega> \<sigma>f)))"

abbreviation adj0_AllPsymbs where "adj0_AllPsymbs \<sigma> I\<^sub>0 I \<omega> \<equiv> (\<lambda>b p. (case SAllPsymbs \<sigma> b p of 
  None \<Rightarrow> AllPsymbs I b p | 
  Some \<sigma>p \<Rightarrow> mkpinterp (fprdnl I\<^sub>0 \<omega> \<sigma>p)))"


definition sound_chp_subst :: "interp \<Rightarrow> chp \<Rightarrow> variable set \<Rightarrow> chan set \<Rightarrow> bool"
  where "sound_chp_subst I \<sigma>a Z Y = (is_denotation (chp_sem I \<sigma>a) \<and> bound_effect (chp_sem I \<sigma>a) (\<iota>\<^sub>V Z \<union> (\<iota>\<^sub>C (\<pi>\<^sub>T Z \<times> Y))) \<and> FVD (chp_sem I \<sigma>a) \<subseteq> Z)"

abbreviation adj0_Chps_raw :: "(ident \<rightharpoonup> chp) \<Rightarrow> interp \<Rightarrow> chpinterp \<Rightarrow> raw_chpinterp"
  where "adj0_Chps_raw \<sigma> I\<^sub>0 I \<equiv> (\<lambda>a Z Y. (case \<sigma> a of 
    None \<Rightarrow> (Chps_raw I) a Z Y | 
    Some \<sigma>a \<Rightarrow> if sound_chp_subst I\<^sub>0 \<sigma>a Z Y then chp_sem I\<^sub>0 \<sigma>a else leastComp))"

definition adj0_Chps :: "(ident \<rightharpoonup> chp) \<Rightarrow> interp \<Rightarrow> chpinterp \<Rightarrow> chpinterp"
  where "adj0_Chps \<sigma> I\<^sub>0 I = mkchpinterp (adj0_Chps_raw \<sigma> I\<^sub>0 I)"

text \<open>The adjoint adj0 of I at \<open>I\<^sub>0 \<omega>\<close> changes the interpretation of symbols by I according to the 
substitution \<sigma> evaluating the replacements in \<open>I\<^sub>0 \<omega>\<close>\<close>
definition adj0 :: "usubst \<Rightarrow> interp \<Rightarrow> (interp \<Rightarrow> state \<Rightarrow> interp)"  
  where "adj0 \<sigma> I\<^sub>0 I \<omega> = \<lparr>                                       
    AllRConsts = adj0_AllRConsts \<sigma> I\<^sub>0 I \<omega>, 
    AllRFuncs = adj0_AllRFuncs \<sigma> I\<^sub>0 I \<omega>, 
    TConsts = adj0_TConsts \<sigma> I\<^sub>0 I \<omega>, 
    TFuncs = adj0_TFuncs \<sigma> I\<^sub>0 I \<omega>, 
    AllPsymbs = adj0_AllPsymbs \<sigma> I\<^sub>0 I \<omega>,
    Chps0 = adj0_Chps (SChps0 \<sigma>) I\<^sub>0 (Chps0 I),
    Bindrs = badj0 (SBindrs \<sigma>) (\<pi>\<^sub>I I\<^sub>0) (\<pi>\<^sub>I I) \<rparr>"

text \<open>Adjoint interpretation \<open>adjoint \<sigma> I \<omega>\<close> to \<open>\<sigma>\<close> of interpretation \<open>I\<close> in state \<open>\<omega>\<close>\<close>
definition adjoint :: "usubst \<Rightarrow> (interp \<Rightarrow> state \<Rightarrow> interp)"
  where "adjoint \<sigma> I \<omega> = adj0 \<sigma> I I \<omega>"                                       



paragraph \<open>Adjoints for the Empty Substitution\<close>

lemma adj0_AllRConsts_empty_usubst: "adj0_AllRConsts empty_usubst I\<^sub>0 I \<nu> b c n = AllRConsts I b c n"
  apply (cases "SAllRConsts empty_usubst b c n")
   apply (simp_all add: SAllRConsts_def)
  by (metis SQRConsts_empty_usubst option.simps(2) usubst.simps(2))

lemma adj0_AllRFuncs_empty_usubst: "adj0_AllRFuncs empty_usubst I\<^sub>0 I \<nu> b f = AllRFuncs I b f"
  apply (cases "SAllRFuncs empty_usubst b f")
   apply (simp_all add: SAllRFuncs_def)
  by (metis SQRFuncs_empty_usubst option.simps(2) usubst.simps(4))

lemma adj0_SAllPsymbs_empty_usubst: "adj0_AllPsymbs empty_usubst I\<^sub>0 I \<nu> b f = AllPsymbs I b f"
  apply (cases "SAllPsymbs empty_usubst b f")
   apply (simp_all add: SAllRFuncs_def)
  by (metis One_nat_def n_not_Suc_n numeral_2_eq_2 usubstsize_all_psymbs_subst usubstsize_empty_usubst)

lemma adj0_empty_usubst [simp]: "adj0 empty_usubst I\<^sub>0 I \<nu> = I"
  apply (rule interp.equality)
  apply (simp_all add: adj0_def adj0_Chps_def)
  by (auto simp add: adj0_AllRConsts_empty_usubst adj0_AllRFuncs_empty_usubst 
      adj0_SAllPsymbs_empty_usubst Chps_def)

lemma adjoint_empty_usubst [simp]: "adjoint empty_usubst I \<nu> = I"
  by (simp add: adjoint_def)        



paragraph \<open>Simple Observations about Adjoints for Automation\<close>


lemma Vagree_lmerge: "Vagree \<nu> \<omega>' Z \<Longrightarrow> lmerge \<nu> \<omega> Z = lmerge \<omega>' \<omega> Z"
  using lmerge_vagree Vagree_only_trans by blast

lemma is_pinterp_adjoint_rfuncs [simp]: "is_pinterp (rprdnl I\<^sub>0 \<omega> \<sigma>f)"
  unfolding is_pinterp_alt rprdnl_def using Vagree_lmerge by simp

lemma is_pinterp_adjoint_tfuncs [simp]: "is_pinterp (tprdnl I\<^sub>0 \<omega> \<sigma>f)"
  unfolding is_pinterp_alt tprdnl_def using Vagree_lmerge by simp

lemma is_pinterp_adjoint_gpsymbs [simp]: "is_pinterp (fprdnl I\<^sub>0 \<omega> \<sigma>p)"
  unfolding is_pinterp_alt fprdnl_def using Vagree_lmerge by simp

lemma adjoint_rconsts [simp]: "AllRConsts (adjoint \<sigma> I \<omega>) b c n 
    = rtrm_sem I (case SAllRConsts \<sigma> b c n of Some \<sigma>c \<Rightarrow> \<sigma>c | None \<Rightarrow> RConst b c n) \<omega>"
  unfolding adjoint_def adj0_def 
  apply (cases "SAllRConsts \<sigma> b c n = None") 
  by auto

lemma adjoint_rfuncs [simp]: "AllRFuncs (adjoint \<sigma> I \<omega>) b f = (case SAllRFuncs \<sigma> b f of 
    None \<Rightarrow> AllRFuncs I b f                                              
  | Some \<sigma>f \<Rightarrow> mkpinterp (rprdnl I \<omega> \<sigma>f))"
  unfolding adjoint_def adj0_def rprdnl_def by simp

lemma adjoint_tconsts [simp]: "(TConsts (adjoint \<sigma> I \<omega>) c n) 
    = ttrm_sem I (case STConsts \<sigma> c n of Some \<sigma>c \<Rightarrow> \<sigma>c | None \<Rightarrow> TConst c n) \<omega>"
  unfolding adjoint_def adj0_def
  apply (cases "STConsts \<sigma> c n = None") 
   apply simp
  by force

lemma adjoint_tfuncs [simp]: "TFuncs (adjoint \<sigma> I \<omega>) f = (case STFuncs \<sigma> f of 
    None \<Rightarrow> TFuncs I f
  | Some \<sigma>f \<Rightarrow> mkpinterp (tprdnl I \<omega> \<sigma>f))"
  unfolding adjoint_def adj0_def by simp

lemma adjoint_gpsymbs [simp]: "AllPsymbs (adjoint \<sigma> I \<omega>) b p = (case SAllPsymbs \<sigma> b p of 
    None \<Rightarrow> AllPsymbs I b p
  | Some \<sigma>p \<Rightarrow> mkpinterp (fprdnl I \<omega> \<sigma>p))"
  unfolding adjoint_def adj0_def by simp



lemma pi_interp_repc [simp]: "\<pi>\<^sub>I (repc I dotid n d) = \<pi>\<^sub>I I"
  apply (cases d)
  by (simp_all add: rrepc_def trepc_def)

lemma pi_interp_repc_vec_rec [simp]: "\<pi>\<^sub>I (repc_vec I (dot_repl_vec_rec n d)) = \<pi>\<^sub>I I"
  apply (induction d arbitrary: I n)
  by (simp_all add: dot_repl_vec_def)

lemma pi_interp_repc_vec [simp]: "\<pi>\<^sub>I (repc_vec I (dot_repl_vec d)) = \<pi>\<^sub>I I"
  by (simp add: dot_repl_vec_def)



paragraph \<open>Distribution of Substitution Union over Adjoints for Binder Interpretations\<close>



lemma vspace_SVarSpaces_only_rvars [simp, intro]: "SVarSpaces \<sigma> Z = Aterm \<sigma>Z \<Longrightarrow> vspace_sem J \<sigma>Z \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R"
  using SVarSpaces_correct_Some rspace_only_rvars  by auto

(* lemma bspace_SVarSpaces_only_vars [simp, intro]: "SVarSpaces \<sigma> Z = Aterm \<sigma>Z \<Longrightarrow> vspace_sem J \<sigma>Z \<subseteq> \<V>"
proof -
  have "\<iota>\<^sub>V (\<iota>\<^sub>R \<V>\<^sub>R) \<subseteq> \<iota>\<^sub>V \<V>" using iota_vars_mono by simp
  thus "SVarSpaces \<sigma> Z = Aterm \<sigma>Z \<Longrightarrow> vspace_sem J \<sigma>Z \<subseteq> \<iota>\<^sub>V \<V>"
    using SVarSpaces_correct_Some rspace_only_rvars0 by blast
qed *)


lemma badj0_BConsts\<^sub>R\<^sub>V_only_rvars [simp, intro]: "(badj0_BConsts\<^sub>R\<^sub>V \<sigma> J\<^sub>0 J) Z \<subseteq> \<V>\<^sub>R"
  by blast

lemma badj0_BConsts\<^sub>\<Omega>_sum_dist [simp]: "BConsts\<^sub>\<Omega> (badj0 (\<sigma>\<^sub>1 ++\<^sub>B \<sigma>\<^sub>2) J\<^sub>0 J) Y = BConsts\<^sub>\<Omega> (badj0 \<sigma>\<^sub>2 J\<^sub>0 (badj0 \<sigma>\<^sub>1 J\<^sub>0 J)) Y"
  unfolding busubst_sum_def badj0_def
  apply (cases "SChanSpaces \<sigma>\<^sub>2 Y")
  by (simp_all add: map_snd_None)
                           
lemma badj0_BConsts\<^sub>R\<^sub>V_sum_dist_raw: "SVarSpaces \<sigma>\<^sub>2 Z = undeft \<Longrightarrow> (badj0_BConsts\<^sub>R\<^sub>V (\<sigma>\<^sub>1 ++\<^sub>B \<sigma>\<^sub>2) J\<^sub>0 J) Z 
  = (badj0_BConsts\<^sub>R\<^sub>V \<sigma>\<^sub>2 J\<^sub>0 (mkbinterp (badj0_BConsts\<^sub>\<Omega> \<sigma>\<^sub>1 J\<^sub>0 J) (badj0_BConsts\<^sub>R\<^sub>V \<sigma>\<^sub>1 J\<^sub>0 J))) Z"
  apply (simp add: busubst_sum_def)
  by (simp add: map_add_def)

lemma badj0_BConsts\<^sub>R\<^sub>V_sum_dist_raw2: "SVarSpaces \<sigma>\<^sub>2 Z \<noteq> undeft \<Longrightarrow> (badj0_BConsts\<^sub>R\<^sub>V (\<sigma>\<^sub>1 ++\<^sub>B \<sigma>\<^sub>2) J\<^sub>0 J) Z 
  = (badj0_BConsts\<^sub>R\<^sub>V \<sigma>\<^sub>2 J\<^sub>0 (mkbinterp (badj0_BConsts\<^sub>\<Omega> \<sigma>\<^sub>1 J\<^sub>0 J) (badj0_BConsts\<^sub>R\<^sub>V \<sigma>\<^sub>1 J\<^sub>0 J))) Z"
  apply (simp add: busubst_sum_def)
  by force

lemma badj0_BConsts\<^sub>R\<^sub>V_sum_dist [simp]: "BConsts\<^sub>R\<^sub>V0 (badj0 (\<sigma>\<^sub>1 ++\<^sub>B \<sigma>\<^sub>2) J\<^sub>0 J) Z = BConsts\<^sub>R\<^sub>V0 (badj0 \<sigma>\<^sub>2 J\<^sub>0 (badj0 \<sigma>\<^sub>1 J\<^sub>0 J)) Z"
  unfolding badj0_def
  apply simp
  using badj0_BConsts\<^sub>R\<^sub>V_sum_dist_raw badj0_BConsts\<^sub>R\<^sub>V_sum_dist_raw2 by fast

(* not simp to prevent simplification within raw_adj0 *)
lemma badj0_usubst_sum_dist: "badj0 (\<sigma>\<^sub>1 ++\<^sub>B \<sigma>\<^sub>2) J\<^sub>0 J = badj0 \<sigma>\<^sub>2 J\<^sub>0 (badj0 \<sigma>\<^sub>1 J\<^sub>0 J)"
  by (rule binterp.equality) (auto)



paragraph \<open>Distribution of Substitution Union over Substitution Adjoints\<close>

lemma SAllRConsts_ussum_snd_None: "SAllRConsts \<sigma>\<^sub>2 b c n = undeft \<Longrightarrow> SAllRConsts (\<sigma>\<^sub>1 +++ \<sigma>\<^sub>2) b c n = SAllRConsts \<sigma>\<^sub>1 b c n"
  apply (simp add: usubst_sum_def SAllRConsts_def SQRConsts_def)
  apply (cases b)
  by (simp_all add: SQRConsts_conv map_snd_None)

lemma SAllRConsts_ussum_snd_Some: "SAllRConsts \<sigma>\<^sub>2 b c n \<noteq> undeft \<Longrightarrow> SAllRConsts (\<sigma>\<^sub>1 +++ \<sigma>\<^sub>2) b c n = SAllRConsts \<sigma>\<^sub>2 b c n"
  apply (simp add: usubst_sum_def SAllRConsts_def SQRConsts_def)
  apply (cases b)
   apply (auto simp add: SQRConsts_def)
  by (metis map_snd_Some option.distinct(1) option.simps(4))

lemma adj0_AllRConsts_ussum_dist [simp]: 
  "AllRConsts (adj0 (\<sigma>\<^sub>1 +++ \<sigma>\<^sub>2) I\<^sub>0 I \<nu>) b c n = AllRConsts (adj0 \<sigma>\<^sub>2 I\<^sub>0 (adj0 \<sigma>\<^sub>1 I\<^sub>0 I \<nu>) \<nu>) b c n"
    apply (simp add: adj0_def)
  apply (cases "SAllRConsts \<sigma>\<^sub>2 b c n")
   apply (simp_all add: SAllRConsts_ussum_snd_None)
  by (simp add: SAllRConsts_ussum_snd_Some)

lemma SAllRFuncs_ussum_snd_None: "SAllRFuncs \<sigma>\<^sub>2 b f = undeft \<Longrightarrow> SAllRFuncs (\<sigma>\<^sub>1 +++ \<sigma>\<^sub>2) b f = SAllRFuncs \<sigma>\<^sub>1 b f"
  apply (simp add: usubst_sum_def SAllRFuncs_def SQRFuncs_def)
  apply (cases b)
  by (simp_all add: SQRFuncs_conv map_snd_None)

lemma SAllRFuncs_ussum_snd_Some: "SAllRFuncs \<sigma>\<^sub>2 b f \<noteq> undeft \<Longrightarrow> SAllRFuncs (\<sigma>\<^sub>1 +++ \<sigma>\<^sub>2) b f = SAllRFuncs \<sigma>\<^sub>2 b f"
  apply (simp add: usubst_sum_def SAllRFuncs_def SQRFuncs_def)
  apply (cases b)
   apply (auto simp add: SQRFuncs_def)
  by (metis map_snd_Some option.distinct(1) option.simps(4))

lemma adj0_AllRFuncs_ussum_dist [simp]: 
  "AllRFuncs (adj0 (\<sigma>\<^sub>1 +++ \<sigma>\<^sub>2) I\<^sub>0 I \<nu>) b f = AllRFuncs (adj0 \<sigma>\<^sub>2 I\<^sub>0 (adj0 \<sigma>\<^sub>1 I\<^sub>0 I \<nu>) \<nu>) b f"
  apply (simp add: adj0_def)
  apply (cases "SAllRFuncs \<sigma>\<^sub>2 b f")
   apply (simp_all add: SAllRFuncs_ussum_snd_None)
  by (simp add: SAllRFuncs_ussum_snd_Some)

lemma adj0_TConsts_ussum_dist [simp]: 
  "TConsts (adj0 (\<sigma>\<^sub>1 +++ \<sigma>\<^sub>2) I\<^sub>0 I \<nu>) c n = TConsts (adj0 \<sigma>\<^sub>2 I\<^sub>0 (adj0 \<sigma>\<^sub>1 I\<^sub>0 I \<nu>) \<nu>) c n"
  unfolding adj0_def usubst_sum_def
  apply (cases "STConsts \<sigma>\<^sub>2 c n")
  by (auto simp add: map_snd_None)

lemma adj0_TFuncs_ussum_dist [simp]: 
  "TFuncs (adj0 (\<sigma>\<^sub>1 +++ \<sigma>\<^sub>2) I\<^sub>0 I \<nu>) f = TFuncs (adj0 \<sigma>\<^sub>2 I\<^sub>0 (adj0 \<sigma>\<^sub>1 I\<^sub>0 I \<nu>) \<nu>) f"
  unfolding adj0_def usubst_sum_def
  apply (cases "STFuncs \<sigma>\<^sub>2 f")
  by (auto simp add: map_snd_None)

lemma SPsymbs_ussum_snd_None: "SPsymbs \<sigma>\<^sub>2 p = undeft \<Longrightarrow> SPsymbs (\<sigma>\<^sub>1 +++ \<sigma>\<^sub>2) p = SPsymbs \<sigma>\<^sub>1 p"
  by (simp add: usubst_sum_def map_snd_None)
  
lemma SAllPsymbs_ussum_snd_None: "SAllPsymbs \<sigma>\<^sub>2 b p = undeft \<Longrightarrow> SAllPsymbs (\<sigma>\<^sub>1 +++ \<sigma>\<^sub>2) b p = SAllPsymbs \<sigma>\<^sub>1 b p"
  apply (simp add: SAllPsymbs_def SFOL\<^sub>RPsymbs_def)
  apply (cases b)
  by (simp_all add: usubst_sum_def SFOL\<^sub>RPsymbs_conv map_snd_None)
  
lemma SAllPsymbs_ussum_snd_Some: "SAllPsymbs \<sigma>\<^sub>2 b p \<noteq> undeft \<Longrightarrow> SAllPsymbs (\<sigma>\<^sub>1 +++ \<sigma>\<^sub>2) b p = SAllPsymbs \<sigma>\<^sub>2 b p"
  apply (simp add: usubst_sum_def SAllPsymbs_def SFOL\<^sub>RPsymbs_def)
  apply (cases b)
   apply (metis SFOL\<^sub>RPsymbs_def map_snd_Some option.distinct(1) option.simps(4))
  by auto
 
lemma adj0_AllPsymbs_ussum_dist [simp]: 
  "AllPsymbs (adj0 (\<sigma>\<^sub>1 +++ \<sigma>\<^sub>2) I\<^sub>0 I \<nu>) b p = AllPsymbs (adj0 \<sigma>\<^sub>2 I\<^sub>0 (adj0 \<sigma>\<^sub>1 I\<^sub>0 I \<nu>) \<nu>) b p"
  unfolding adj0_def     
  apply (cases "SAllPsymbs \<sigma>\<^sub>2 b p")
   apply (simp add: SAllPsymbs_ussum_snd_None)
  by (simp add: SAllPsymbs_ussum_snd_Some)

lemma SFOL\<^sub>RPsymbs0_usubst_sum_dist: "SFOL\<^sub>RPsymbs0 (\<sigma>\<^sub>1 +++ \<sigma>\<^sub>2) = SFOL\<^sub>RPsymbs0 \<sigma>\<^sub>1 ++ SFOL\<^sub>RPsymbs0 \<sigma>\<^sub>2"
  by (simp add: usubst_sum_def)

lemma SPsymbs_usubst_sum_dist: "SPsymbs (\<sigma>\<^sub>1 +++ \<sigma>\<^sub>2) = SPsymbs \<sigma>\<^sub>1 ++ SPsymbs \<sigma>\<^sub>2"
  by (simp add: usubst_sum_def)



lemma mk_Vagree_singleton_Tv: "Vagree \<nu>\<^sub>1 \<nu>\<^sub>2 (-{Tv h}) \<Longrightarrow> \<nu>\<^sub>2 = trepv \<nu>\<^sub>1 h (stT \<nu>\<^sub>2 h)"
  apply (rule state_eq_by_sortI)
   apply (drule Vagree_stR_E) apply (auto simp: pi_rvars_def eqon_def)
  apply (drule Vagree_stT_E) by (auto simp add: pi_tvars_def eqon_def)


lemma chp_sem_history_independent [simp, intro]: "wf_chp \<L> \<alpha> \<Longrightarrow> FVD (chp_sem I \<alpha>) \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R"
proof - 
  assume 0: "wf_chp \<L> \<alpha>"
  show "FVD (chp_sem I \<alpha>) \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R"
  proof (rule ccontr)
    assume "\<not>(FVD (chp_sem I \<alpha>) \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R)"
    then obtain h where "Tv h \<in> FVD (chp_sem I \<alpha>)"
      by (metis UNIV_I in_iota_rvars is_Rv_def subsetI variable.collapse(2))
    then obtain \<nu>\<^sub>1 \<tau>\<^sub>1 \<omega>\<^sub>1 \<nu>\<^sub>2 where 1: "(Vagree \<nu>\<^sub>1 \<nu>\<^sub>2 (-{Tv h})) \<and> (\<nu>\<^sub>1, \<tau>\<^sub>1, \<omega>\<^sub>1) \<in> (chp_sem I \<alpha>) 
      \<and> \<not>(\<exists>\<tau>\<^sub>2 \<omega>\<^sub>2. (\<nu>\<^sub>2, \<tau>\<^sub>2, \<omega>\<^sub>2) \<in> (chp_sem I \<alpha>) \<and> \<tau>\<^sub>1 = \<tau>\<^sub>2 \<and> (Vagreebot \<omega>\<^sub>1 \<omega>\<^sub>2 (-{Tv h})))" 
      unfolding FVD_def by blast
    hence "(trepv \<nu>\<^sub>1 h (stT \<nu>\<^sub>2 h), \<tau>\<^sub>1, trepvbot \<omega>\<^sub>1 h (stT \<nu>\<^sub>2 h)) \<in> (chp_sem I \<alpha>)"
      using history_independence 0 by blast
    moreover have "\<nu>\<^sub>2 = trepv \<nu>\<^sub>1 h (stT \<nu>\<^sub>2 h)" using 1 mk_Vagree_singleton_Tv by auto
    moreover have "Vagreebot \<omega>\<^sub>1 (trepvbot \<omega>\<^sub>1 h (stT \<nu>\<^sub>2 h)) (-{Tv h})"
      apply (cases \<omega>\<^sub>1) apply (simp_all add: Vagreebot_def)
      using Vagree_trepv by simp
    ultimately show False using 1 by metis
  qed
qed
          
lemma chp_sem_is_denotation [simp, intro]: "wf_chp \<L> \<alpha> \<Longrightarrow> is_denotation (chp_sem I \<alpha>)"
  unfolding is_denotation_def by simp 



lemma CNP_overapprox: "CNP J \<alpha> \<subseteq> UNIV \<times> CN J \<alpha>"
proof (induction \<alpha> rule: chp_induct)
  case (Chp a Z Y)
  then show ?case by (simp add: CNP_Chp_bound)
next
  case (Choice \<alpha> \<beta>)
  then show ?case unfolding CNP_def by fastforce
next
  case (Compose \<alpha> \<beta>)                                             
  then show ?case using CN.simps(7) CNP_compose_bound by blast
next
  case (Loop \<alpha>)
  then show ?case using CNP_loop_bound by fastforce
next
  case (Par \<alpha> \<beta>)
  then show ?case using CN.simps(11) CNP_par_bound by blast
qed (simp_all)

lemma adj0_Chps_raw_is_chp_denotation [simp]: "is_chp_denotation (adj0_Chps_raw \<sigma> I\<^sub>0 I) a Z Y"
  apply (cases "\<sigma> a")
  using Chps_raw_correct is_chpinterp_def leastComp_is_chpinterp sound_chp_subst_def by auto
  
lemma adj0_Chps_raw_is_chpinterp [simp]: "is_chpinterp (adj0_Chps_raw \<sigma> I\<^sub>0 I)"
  unfolding is_chpinterp_def using adj0_Chps_raw_is_chp_denotation by simp

lemma adj0_Chps_usum_dist_raw: "Chps_raw (adj0_Chps (\<sigma>\<^sub>1 ++ \<sigma>\<^sub>2) I\<^sub>0 I) a Z = Chps_raw (adj0_Chps \<sigma>\<^sub>2 I\<^sub>0 (adj0_Chps \<sigma>\<^sub>1 I\<^sub>0 I)) a Z"
    apply (cases "\<sigma>\<^sub>2 a")
   apply (simp add: adj0_Chps_def is_chpinterp_def map_snd_None)
  using adj0_Chps_def is_chpinterp_def by force



lemma SChps0_usubst_sum_dist: "SChps0 (\<sigma>\<^sub>1 +++ \<sigma>\<^sub>2) = SChps0 \<sigma>\<^sub>1 ++ SChps0 \<sigma>\<^sub>2"
  by (simp add: usubst_sum_def)

lemma Chps0_adj0_ussum_dist: "Chps0 (adj0 (\<sigma>\<^sub>1 +++ \<sigma>\<^sub>2) I\<^sub>0 I \<nu>) = Chps0 (adj0 \<sigma>\<^sub>2 I\<^sub>0 (adj0 \<sigma>\<^sub>1 I\<^sub>0 I \<nu>) \<nu>)"
  unfolding adj0_def apply simp
  apply (rule chpinterp_eqI)
  apply (simp add: SChps0_usubst_sum_dist )
  using adj0_Chps_usum_dist_raw by blast

lemma adj0_usubst_sum_dist [simp]: "adj0 (\<sigma>\<^sub>1 +++ \<sigma>\<^sub>2) I\<^sub>0 I \<nu> = adj0 \<sigma>\<^sub>2 I\<^sub>0 (adj0 \<sigma>\<^sub>1 I\<^sub>0 I \<nu>) \<nu>"
  apply (rule interp.equality)
  apply fastforce+
  using Chps0_adj0_ussum_dist by (simp_all add: adj0_def badj0_usubst_sum_dist) 



paragraph \<open>Substitution Adjoint for dotsubst\<close>

lemma badj0_rdotsubst_inv: "badj0 (SBindrs (rdotsubst n \<theta>)) J\<^sub>0 J = J"
  using badj0_def badj0_empty_usubst SBindrs_rdotsubst_empty by presburger

lemma badj0_tdotsubst_inv: "badj0 (SBindrs (tdotsubst n te)) J\<^sub>0 J = J"
  using badj0_def badj0_empty_usubst SBindrs_tdotsubst_empty by presburger

lemma adj0_AllRConsts_rdotsubst: "adj0_AllRConsts (rdotsubst n \<theta>) I\<^sub>0 I \<omega> =
    (\<lambda>b c m. if \<not>b \<and> c = dotid \<and> m = n then rtrm_sem I\<^sub>0 \<theta> \<omega> else AllRConsts I b c m)"
  apply rule+ unfolding rdotsubst_def
  by (simp_all add: SAllRConsts_def SQRConsts_def)









lemma SAllRFuncs_rdostsubst_inv [simp]: "SAllRFuncs (rdotsubst n \<theta>) b f = None"
  by (simp add: SAllRFuncs_def rdotsubst_def SQRFuncs_def)

lemma SAllPsymbs_rdostsubst_inv [simp]: "SAllPsymbs (rdotsubst n \<theta>) b p = None"
  by (simp add: SAllPsymbs_def rdotsubst_def SFOL\<^sub>RPsymbs_def)

lemma SAllRFuncs_tdostsubst_inv [simp]: "SAllRFuncs (tdotsubst n \<theta>) b f = None"
  by (simp add: SAllRFuncs_def tdotsubst_def SQRFuncs_def)

lemma SAllPsymbs_tdostsubst_inv [simp]: "SAllPsymbs (tdotsubst n \<theta>) b p = None"
  by (simp add: SAllPsymbs_def tdotsubst_def SFOL\<^sub>RPsymbs_def)





(* lemma adj0_AllRFuncs_rdotsubst_inv [simp, intro]: "adj0_AllRFuncs (rdotsubst n \<theta>) I\<^sub>0 I \<nu> = AllRFuncs I"
  using SAllRFuncs_rdostsubst_inv by simp

lemma adj0_AllPsymbs_rdotsubst_inv [simp, intro]: "adj0_AllPsymbs (rdotsubst n \<theta>) I\<^sub>0 I \<nu> = AllPsymbs I"
  using SAllPsymbs_rdostsubst_inv by simp *)

lemma adj0_rdotsubst: "adj0 (rdotsubst n \<theta>) I\<^sub>0 I \<nu> = repc I dotid n (arg_sem I\<^sub>0 (RArg \<theta>) \<nu>)"
  apply (simp add: adj0_def rrepc_def)
  apply (rule interp.equality)
  apply (simp_all add: adj0_AllRConsts_rdotsubst)
  by (simp_all add: rdotsubst_def adj0_Chps_def)

lemma SAllRConsts_tdotsubst [simp, intro]: "SAllRConsts (tdotsubst n \<theta>) b c n = None"
  by (simp add: SAllRConsts_def SQRConsts_def tdotsubst_def)

lemma adj0_AllRConsts_tdotsubst [simp, intro]: "adj0_AllRConsts (tdotsubst n \<theta>) I\<^sub>0 I \<nu> = AllRConsts I"
  apply rule+
  by (simp add: SAllRConsts_def SQRConsts_def tdotsubst_def)

lemma adj0_TConsts_tdotsubst: "adj0_TConsts (tdotsubst n \<theta>) I\<^sub>0 I \<nu> =
    (\<lambda>c m. if c = dotid \<and> m = n then ttrm_sem I\<^sub>0 \<theta> \<nu> else TConsts I c m)"
  apply rule+ by (simp add: tdotsubst_def)

lemma adj0_tdotsubst: "adj0 (tdotsubst n te) I\<^sub>0 I \<nu> = repc I dotid n (arg_sem I\<^sub>0 (TArg te) \<nu>)"
  apply (simp add: adj0_def trepc_def)
  apply (rule interp.equality)
           apply (simp_all add: adj0_TConsts_tdotsubst)
  by (simp_all add: adj0_Chps_def tdotsubst_def)

text \<open>The adjoint of I under the substition {. ~> e} at \<open>I\<^sub>0 \<nu>\<close> equals I except that . is evaluated
according to the sematnics of e at \<open>I\<^sub>0 \<nu>\<close>\<close> 
lemma adj0_dotsubst: "adj0 (dotsubst n e) I\<^sub>0 I \<nu> = repc I dotid n (arg_sem I\<^sub>0 e \<nu>)"
  apply (cases e)
  using adj0_rdotsubst adj0_tdotsubst by simp_all

lemma dotsubst_adj_eq_dotted_interp_rec [simp]: 
  "adj0 (dotsubst_vec_rec n \<Theta>) I\<^sub>0 I \<nu> = repc_vec I (dot_repl_vec_rec n (args_sem I\<^sub>0 \<Theta> \<nu>))"
proof (induction \<Theta> arbitrary: n I)
  case Nil
  then show ?case by (simp add: args_sem_def)
next
  case (Cons e \<Theta>)  
  let ?ie = "(dotid, n, (arg_sem I\<^sub>0 e \<nu>))"
  let ?i\<Theta> = "dot_repl_vec_rec (n+1) (args_sem I\<^sub>0 \<Theta> \<nu>)"

  have "adj0 (dotsubst_vec_rec n (e # \<Theta>)) I\<^sub>0 I \<nu> 
    = adj0 (dotsubst_vec_rec (n+1) \<Theta>) I\<^sub>0 (adj0 (dotsubst n e) I\<^sub>0 I \<nu>) \<nu>" by simp
  also have "... = adj0 (dotsubst_vec_rec (n+1) \<Theta>) I\<^sub>0 (repc I dotid n (arg_sem I\<^sub>0 e  \<nu>)) \<nu>" 
    using adj0_dotsubst by simp
  also have "... = repc_vec (repc I dotid n (arg_sem I\<^sub>0 e \<nu>)) ?i\<Theta>" using Cons.IH by simp
  also have "... = repc_vec I (?ie # ?i\<Theta>)" by simp
  also have "... = repc_vec I (dot_repl_vec_rec n (args_sem I\<^sub>0 (e # \<Theta>) \<nu>))" by (simp add: args_sem_def)
  finally show ?case .
qed

lemma dotsubst_adj_eq_dotted_interp: 
  "adjoint (dotsubst_vec \<Theta>) I \<nu> = repc_vec I (dot_repl_vec (args_sem I \<Theta> \<nu>))"
  unfolding adjoint_def dotsubst_vec_def dot_repl_vec_def by simp


  
subsection \<open>Uniform Substitution for Terms\<close>

lemma usubst_symbch_CConst: "cspace_sem J (cusubst \<sigma> (CConst i)) = cspace_sem (badjoint \<sigma> J) (CConst i)"
proof -
  have "cspace_sem J (cusubst \<sigma> (CConst i)) = cspace_sem (badjoint \<sigma> J) (CConst i)"
    apply (cases "SChanSpaces \<sigma> i")
    by (simp add: badjoint_def badj0_def)+
  thus ?thesis by blast
qed

lemma usubst_cspace: "cspace_sem J (cusubst \<sigma> Y) = cspace_sem (badjoint \<sigma> J) Y"
  apply (induction Y)
  using usubst_symbch_CConst by auto
                                                                                  
lemma args_sem_append_dist [simp]: "args_sem I (\<Theta>\<^sub>1 @ \<Theta>\<^sub>2) \<nu> = (args_sem I \<Theta>\<^sub>1 \<nu>) @ (args_sem I \<Theta>\<^sub>2 \<nu>)"
  apply (induction \<Theta>\<^sub>1)
  by (simp add: args_sem_def)+



lemma alusubst_const_conv: "alusubst \<sigma> \<L> U (e # \<Theta>) \<noteq> undeft \<Longrightarrow> ausubst \<sigma> \<L> U e \<noteq> undeft \<and> alusubst \<sigma> \<L> U \<Theta> \<noteq> undeft"
  by (metis Binaryo.simps(2) Binaryo.simps(3) alusubst_pre.simps(2))

lemma alusubst_cons_dist [simp]: "alusubst \<sigma> \<L> U (e # \<Theta>) \<noteq> undeft 
  \<Longrightarrow> the(alusubst \<sigma> \<L> U (e # \<Theta>)) = (the(ausubst \<sigma> \<L> U e)) # (the(alusubst \<sigma> \<L> U \<Theta>))"
proof -
  assume "alusubst \<sigma> \<L> U (e # \<Theta>) \<noteq> undeft"
  hence "ausubst \<sigma> \<L> U e \<noteq> undeft \<and> alusubst \<sigma> \<L> U \<Theta> \<noteq> undeft" using alusubst_const_conv by simp
  thus "the(alusubst \<sigma> \<L> U (e # \<Theta>)) = (the(ausubst \<sigma> \<L> U e)) # (the(alusubst \<sigma> \<L> U \<Theta>))" by force
qed

lemma usubst_arglist:
  assumes "alusubst \<sigma> \<L> U \<Theta> \<noteq> undeft"
  assumes "\<And>e. e \<in> set \<Theta> \<Longrightarrow> arg_sem I (the(ausubst \<sigma> \<L> U e)) \<nu> = arg_sem (adjoint \<sigma> I \<omega>) e \<nu>"
  shows "args_sem I (the(alusubst \<sigma> \<L> U \<Theta>)) \<nu> = args_sem (adjoint \<sigma> I \<omega>) \<Theta> \<nu>"
using assms proof (induction \<Theta>)
  case Nil
  then show ?case by (simp add: args_sem_def)
next
  case (Cons e \<Theta>)
  hence "the(alusubst \<sigma> \<L> U (e # \<Theta>)) = (the(ausubst \<sigma> \<L> U e)) # (the(alusubst \<sigma> \<L> U \<Theta>))"
    using alusubst_cons_dist by presburger
  then show ?case using Cons.IH Cons.prems(2) args_sem_def by force
qed





             




(* lemma Vagree_lermge0: "Vagree \<nu> \<omega> (V - X) \<Longrightarrow> Vagree \<nu> (lmerge \<nu> \<omega> X) V"
  by (metis Un_Diff_cancel2 Vagree_and Vagree_lmerge) *)


lemma BConsts\<^sub>R\<^sub>V_on_undeft [simp]: "(SVarSpaces \<sigma>) x = undeft \<Longrightarrow> (BConsts\<^sub>R\<^sub>V (badjoint \<sigma> J)) x = (BConsts\<^sub>R\<^sub>V J) x"
  using badj0_BConsts\<^sub>R\<^sub>V_only_rvars by (simp add: badj0_def badjoint_def)
                            
lemma BConsts\<^sub>\<Omega>_on_undeft [simp]: "(SChanSpaces \<sigma>) Y = undeft \<Longrightarrow> (BConsts\<^sub>\<Omega> (badjoint \<sigma> J)) Y = (BConsts\<^sub>\<Omega> J) Y"
  by (simp add: badj0_def badjoint_def)



lemma SVarSpaces_vspace: "SVarSpaces \<sigma> X = Aterm \<sigma>X \<Longrightarrow> \<iota>\<^sub>R (\<pi>\<^sub>R (vspace_sem J \<sigma>X)) = vspace_sem J \<sigma>X"
  using vspace_SVarSpaces_only_rvars by simp



theorem vusubst_space: "vspace_sem J (vusubst \<sigma> Z) = vspace_sem (badjoint \<sigma> J) Z"
proof (induction Z)
  case (VRConst X)
  then show ?case
  proof (cases "(SVarSpaces \<sigma>) X")
    case None
    then show ?thesis by simp
  next
    case (Some \<sigma>X)
    then show ?thesis by (simp add: badjoint_def badj0_def)
  qed
qed (simp_all)




lemma Bindrs_adjoint_commute [simp]: "\<pi>\<^sub>I (adjoint \<sigma> I \<omega>) = badjoint (SBindrs \<sigma>) (\<pi>\<^sub>I I)"
  by (simp add: adjoint_def adj0_def badjoint_def)

lemma VCagree_bindr_cong [intro]: "V = W \<Longrightarrow> VCagree \<nu> \<omega> V \<Longrightarrow> VCagree \<nu> \<omega> W"
  by force

lemma uvaruvari_taboo_vcagreei_taboo_vcagree: "Uvariation \<nu> \<omega> U \<Longrightarrow> (FNE\<^sub>\<L> \<L> e)\<inter>U={} \<Longrightarrow> VCagree \<nu> \<omega> (FNE\<^sub>\<L> \<L> e)"
  by (meson Uvariation_def VCagree_antimon disjoint_eq_subset_Compl)


lemma iota_vars_comtar_mono: "X \<subseteq> Z \<Longrightarrow> Y \<subseteq> C \<Longrightarrow> \<iota>\<^sub>V X \<union> \<iota>\<^sub>C Y \<subseteq> \<iota>\<^sub>V Z \<union> \<iota>\<^sub>C C"
  apply (simp add: iota_vars_def iota_comtar_def) by blast







lemma FVV_sound_stat_sem: "is_sound_stat_sem \<L> \<Longrightarrow> FVV\<^sub>\<L> \<L> Z \<subseteq> FVV J Z"
  unfolding is_sound_stat_sem_def stat_sem_porder_def sem_stat_sem_def by simp

lemma CNV_sound_stat_sem: "is_sound_stat_sem \<L> \<Longrightarrow> CNV\<^sub>\<L> \<L> Z \<subseteq> CNV J Z"
  unfolding is_sound_stat_sem_def stat_sem_porder_def sem_stat_sem_def CNV\<^sub>\<L>_def CNV_def FVV_def by force 

lemma FNV_sound_stat_sem: "is_sound_stat_sem \<L> \<Longrightarrow> FVN\<^sub>\<L> \<L> Z \<subseteq> FNV J Z"
  unfolding FVN\<^sub>\<L>_def FNV_def using FVV_sound_stat_sem CNV_sound_stat_sem
  apply (rule iota_vars_comtar_mono) by simp_all

lemma FNE_expr_sound_stat_sem [simp, intro]:
  shows "is_sound_stat_sem \<L> \<Longrightarrow> FNE J \<theta> \<subseteq> FNE\<^sub>\<L> \<L> (Ertrm \<theta>)"
    and "is_sound_stat_sem \<L> \<Longrightarrow> FNE J te \<subseteq> FNE\<^sub>\<L> \<L> (Ettrm te)"
    and "is_sound_stat_sem \<L> \<Longrightarrow> FNE J \<phi> \<subseteq> FNE\<^sub>\<L> \<L> (Efml \<phi>)"
  unfolding is_sound_stat_sem_def stat_sem_porder_def by fastforce+

lemma BNP_sound_stat_sem: "is_sound_stat_sem \<L> \<Longrightarrow> BNP J \<alpha> \<subseteq> BNP\<^sub>\<L> \<L> \<alpha>"
  unfolding is_sound_stat_sem_def stat_sem_porder_def by simp

lemma BVP_sound_stat_sem: "is_sound_stat_sem \<L> \<Longrightarrow> BVP J \<alpha> \<subseteq> BVP\<^sub>\<L> \<L> \<alpha>"
  using BNP_sound_stat_sem unfolding BNP_partition BVP\<^sub>\<L>_def by (simp add: iota_pi_vars_alternate)

lemma FVP_sound_stat_sem: "is_sound_stat_sem \<L> \<Longrightarrow> FVP J \<alpha> \<subseteq> FVP\<^sub>\<L> \<L> \<alpha>"
  unfolding is_sound_stat_sem_def stat_sem_porder_def by simp

lemma CNP_sound_stat_sem: "is_sound_stat_sem \<L> \<Longrightarrow> CNP J \<alpha> \<subseteq> CNP\<^sub>\<L> \<L> \<alpha>"
  using BNP_sound_stat_sem unfolding BNP_partition CNP\<^sub>\<L>_def by (simp add: iota_pi_comtar_alternate) 

lemma UAV\<^sub>\<L>_sound_stat_sem: "is_sound_stat_sem \<L> \<Longrightarrow> UAV\<^sub>\<L> \<L> Z \<subseteq> FVV J Z"
  unfolding is_sound_stat_sem_def stat_sem_porder_def by simp



lemma VCagree_lmerge: "VCagree \<nu> \<omega> U \<Longrightarrow> VCagree \<nu> (lmerge \<nu> \<omega> X) (U \<union> (\<iota>\<^sub>V X \<union> \<iota>\<^sub>C (\<pi>\<^sub>T X \<times> \<Omega>)))"
  unfolding VCagree_def apply (rule Vagree_by_sortI)
   apply (drule Vagree_stR_E)
   apply (simp add: eqon_def lmerge_def)
  apply (drule Vagree_stT_E)
  by (simp add: eqon_def lmerge_def tsfilter_access Image_def)







text \<open>Lemma 15 of \<^url>\<open>http://arxiv.org/abs/1902.07230\<close>\<close>
theorem usubst_term:
  assumes sound_stat: "is_sound_stat_sem \<L>"
  assumes vaouter: "Uvariation \<nu> \<omega> U"
  assumes bindrI: "J = \<pi>\<^sub>I I"
  shows rusubst_term: "rusubst \<sigma> \<L> U \<theta>\<noteq>undeft \<Longrightarrow> rtrm_sem I (the(rusubst \<sigma> \<L> U \<theta>)) \<nu> = rtrm_sem (adjoint \<sigma> I \<omega>) \<theta> \<nu>"
    and tusubst_term: "tusubst \<sigma> \<L> U te\<noteq>undeft \<Longrightarrow> ttrm_sem I (the(tusubst \<sigma> \<L> U te)) \<nu> = ttrm_sem (adjoint \<sigma> I \<omega>) te \<nu>"
    and ausubst_term: "ausubst \<sigma> \<L> U e\<noteq>undeft \<Longrightarrow> arg_sem I (the(ausubst \<sigma> \<L> U e)) \<nu> = arg_sem (adjoint \<sigma> I \<omega>) e \<nu>"
using sound_stat vaouter bindrI proof (induction \<theta> and te and e arbitrary: \<nu> \<omega> and \<nu> \<omega> and \<nu> \<omega> rule: usubstappt_rta_induct)
  case (RVar \<sigma> \<L> U x)
  then show ?case by simp
next
  case (RConst \<sigma> \<L> U b c n)
  then show ?case
  proof (cases "SAllRConsts \<sigma> b c n")
    case None
    then show ?thesis by (simp add: SAllRConsts_def rusappconst_def)
  next
    case (Some \<sigma>c)
    hence noclash: "(FNE\<^sub>\<L> \<L> (Ertrm \<sigma>c))\<inter>U={}" 
      by (metis RConst.prems(1) rusappconst_simp(3) rusubst.simps(2))
    hence "VCagree \<nu> \<omega> (FNE\<^sub>\<L> \<L> (Ertrm \<sigma>c))" 
      using RConst uvaruvari_taboo_vcagreei_taboo_vcagree by metis
    hence agree: "VCagree \<nu> \<omega> (FNE (\<pi>\<^sub>I I) \<sigma>c)" 
      using FNE_expr_sound_stat_sem(1) RConst(2) VCagree_antimon by presburger

    from Some have "rtrm_sem I (the(rusubst \<sigma> \<L> U (RConst b c n))) \<nu> = rtrm_sem I \<sigma>c \<nu>" 
      using noclash by auto
    also have "... = rtrm_sem I \<sigma>c \<omega>" using RConst.prems(3) agree coincidence_rtrm by presburger
    also have "... = AllRConsts (adjoint \<sigma> I \<omega>) b c n" using Some by simp 
    also have "... = rtrm_sem (adjoint \<sigma> I \<omega>) (RConst b c n) \<nu>" by simp
    finally show "rtrm_sem I (the(rusubst \<sigma> \<L> U (RConst b c n))) \<nu> 
      = rtrm_sem (adjoint \<sigma> I \<omega>) (RConst b c n) \<nu>" by auto
  qed
next 
  case (RFunc \<sigma> \<L> U b f Z \<Theta>)

  let ?\<sigma>I = "adjoint \<sigma> I \<omega>"
  let ?\<sigma>Z = "vusubst (SBindrs \<sigma>) Z" 
  let ?\<sigma>\<Theta> = "the(alusubst \<sigma> \<L> U \<Theta>)"

  have argsdeft: "alusubst \<sigma> \<L> U \<Theta> \<noteq> undeft" using RFunc.prems salusubst_undeft by fastforce+
  hence saldeft: "salusubst \<sigma> \<L> U Z \<Theta> = Aterm (?\<sigma>Z, ?\<sigma>\<Theta>)" using salusubst_simp by force

  have usspace: "vspace_sem (\<pi>\<^sub>I I) ?\<sigma>Z = vspace_sem (\<pi>\<^sub>I ?\<sigma>I) Z"
    using vusubst_space Bindrs_adjoint_commute by presburger
  have IHargs: "\<And>e. e \<in> set \<Theta> \<Longrightarrow> arg_sem I (the(ausubst \<sigma> \<L> U e)) \<nu> = arg_sem ?\<sigma>I e \<nu>"
    using alusubst_conv RFunc argsdeft by simp
  
  show ?case
  proof (cases "SAllRFuncs \<sigma> b f")
    case None
    hence "rtrm_sem I (the(rusubst \<sigma> \<L> U (RFunc b f Z \<Theta>))) \<nu> = rtrm_sem I (RFunc b f ?\<sigma>Z ?\<sigma>\<Theta>) \<nu>" 
      using saldeft by fastforce
    also have "... = PInterp (AllRFuncs I b f) (vspace_sem (badjoint (SBindrs \<sigma>) (\<pi>\<^sub>I I)) Z) \<nu> (args_sem (adjoint \<sigma> I \<omega>) \<Theta> \<nu>)"
      using usspace IHargs by (simp add: argsdeft usubst_arglist)
    also have "... = rtrm_sem (adjoint \<sigma> I \<omega>) (RFunc b f Z \<Theta>) \<nu>" 
      unfolding adjoint_def adj0_def badjoint_def using None by simp   
    finally show ?thesis .
  next
    case (Some \<sigma>f)
    hence noclash: "((FNE\<^sub>\<L> \<L> (Ertrm \<sigma>f)) - (FVN\<^sub>\<L> \<L> ?\<sigma>Z)) \<inter> U = {}" 
      using RFunc.prems(1) rusubst_func_conv by fastforce
    
    let ?\<sigma>\<^sub>0 = "dotsubst_vec ?\<sigma>\<Theta>"
    let ?X = "vspace_sem (\<pi>\<^sub>I (adjoint \<sigma> I \<nu>)) Z" 
    let ?d = "args_sem I ?\<sigma>\<Theta> \<nu>"

    have "VCagree \<nu> \<omega> (-U)" using RFunc Uvariation_def by simp
    hence "VCagree \<nu> (lmerge \<nu> \<omega> ?X) (-U\<union>(\<iota>\<^sub>V ?X \<union> \<iota>\<^sub>C (\<pi>\<^sub>T ?X \<times> \<Omega>)))" using VCagree_lmerge by simp
    moreover have "FNE (\<pi>\<^sub>I (adjoint ?\<sigma>\<^sub>0 I \<nu>)) \<sigma>f \<subseteq> -U\<union>(\<iota>\<^sub>V ?X \<union> \<iota>\<^sub>C (\<pi>\<^sub>T ?X \<times> \<Omega>))"
    proof -
      have "FVN\<^sub>\<L> \<L> ?\<sigma>Z \<subseteq> \<iota>\<^sub>V ?X \<union> \<iota>\<^sub>C (\<pi>\<^sub>T ?X \<times> \<Omega>)"
        by (metis Bindrs_adjoint_commute CNV_def FNV_def FNV_sound_stat_sem FVV_def RFunc(4) vusubst_space)
      moreover have "FNE\<^sub>\<L> \<L> (Ertrm \<sigma>f) \<subseteq> -U \<union> (FVN\<^sub>\<L> \<L> ?\<sigma>Z)" using noclash by auto      
      moreover have "FNE (\<pi>\<^sub>I (adjoint ?\<sigma>\<^sub>0 I \<nu>)) \<sigma>f \<subseteq> FNE\<^sub>\<L> \<L> (Ertrm \<sigma>f)" 
        using FNE_expr_sound_stat_sem RFunc(4) by presburger
      ultimately show ?thesis by auto
    qed
    ultimately have agree: "VCagree \<nu> (lmerge \<nu> \<omega> ?X) (FNE (\<pi>\<^sub>I (adjoint ?\<sigma>\<^sub>0 I \<nu>)) \<sigma>f)"
      using VCagree_antimon by simp 

      (* unfold usubst definition *)
    have "rtrm_sem I (the(rusubst \<sigma> \<L> U (RFunc b f Z \<Theta>))) \<nu> = rtrm_sem I (the(rusubst ?\<sigma>\<^sub>0 \<L> {} \<sigma>f)) \<nu>" 
      using Some noclash saldeft by auto
      (* transfer \<sigma>f from \<nu> to its U-variation \<omega> *)      
    also have "... = rtrm_sem (adjoint ?\<sigma>\<^sub>0 I \<nu>) \<sigma>f \<nu>"
      using saldeft Some RFunc.IH(2) noclash RFunc.prems by simp
      (* apply IH on the dotsubst, which is smaller than \<sigma> as it only replaces dotsymbols *)
    also have "... = rtrm_sem (adjoint ?\<sigma>\<^sub>0 I \<nu>) \<sigma>f (lmerge \<nu> \<omega> ?X)"
      by (metis agree coincidence_rtrm)
      (* evaluate adjoint of I under dotsubst \<sigma>\<^sub>0 *)
    also have "... = rtrm_sem (repc_vec I (dot_repl_vec ?d)) \<sigma>f (lmerge \<nu> \<omega> ?X)" 
      using dotsubst_adj_eq_dotted_interp by simp
      (* definition of adjoint *)
    also have "... = PInterp (AllRFuncs ?\<sigma>I b f) ?X \<nu> ?d"
      using Some is_pinterp_adjoint_rfuncs rprdnl_def by simp 
      (* apply IH to the argument list \<Theta>, which is smaller than f(Z)(\<Theta>) *)
    also have "... = PInterp (AllRFuncs ?\<sigma>I b f) ?X \<nu> (args_sem ?\<sigma>I \<Theta> \<nu>)" 
      using argsdeft IHargs usubst_arglist by auto
      (* unfold the semantics of the function symbol f(Z)(\<Theta>) *)
    also have "... = rtrm_sem ?\<sigma>I (RFunc b f Z \<Theta>) \<nu>" by auto
    finally show "rtrm_sem I (the(rusubst \<sigma> \<L> U (RFunc b f Z \<Theta>))) \<nu> = rtrm_sem ?\<sigma>I (RFunc b f Z \<Theta>) \<nu>" .
  qed
next
  case (Number \<sigma> \<L> U r)
  then show ?case by simp
next
  case (Plus \<sigma> \<L> U \<theta> \<eta>)
  then show ?case using Pluso_undef by auto
next
  case (Times \<sigma> \<L> U \<theta> \<eta>)
  then show ?case using Timeso_undef by auto
next
  case (ChanOf \<sigma> \<L> U te)
  then show ?case using ChanOfo_undef by auto
next
  case (ValOf \<sigma> \<L> U te)
  then show ?case using ValOfo_undef by auto
next
  case (TimeOf \<sigma> \<L> U te)
  then show ?case using TimeOfo_undef by auto
next
  case (LenT \<sigma> \<L> U te)
  then show ?case using LenTo_undef by auto
next
  case (TVar \<sigma> \<L> U h)
  then show ?case by simp 
next
  case (TConst \<sigma> \<L> U c n)
  then show ?case
  proof (cases "STConsts \<sigma> c n")
    case None
    then show ?thesis by (simp add: tusappconst_def)
  next                                  
    case (Some \<sigma>c)
    hence noclash: "(FNE\<^sub>\<L> \<L> (Ettrm \<sigma>c))\<inter>U={}" by (metis TConst.prems(1) tusappconst_simp(3) tusubst.simps(2))
    hence "VCagree \<nu> \<omega> (FNE\<^sub>\<L> \<L> (Ettrm \<sigma>c))" using TConst uvaruvari_taboo_vcagreei_taboo_vcagree by metis
    hence agree: "VCagree \<nu> \<omega> (FNE (\<pi>\<^sub>I I) \<sigma>c)" using FNE_expr_sound_stat_sem(2) TConst(2) VCagree_antimon by presburger

    from Some have "ttrm_sem I (the(tusubst \<sigma> \<L> U (TConst c n))) \<nu> = ttrm_sem I \<sigma>c \<nu>" using noclash by auto
    also have "... = ttrm_sem I \<sigma>c \<omega>" using TConst agree coincidence_ttrm by presburger
    also have "... = TConsts (adjoint \<sigma> I \<omega>) c n" using Some by simp 
    also have "... = ttrm_sem (adjoint \<sigma> I \<omega>) (TConst c n) \<nu>" by simp
    finally show "ttrm_sem I (the(tusubst \<sigma> \<L> U (TConst c n))) \<nu> = ttrm_sem (adjoint \<sigma> I \<omega>) (TConst c n) \<nu>" by auto
  qed
next
  case (TFunc \<sigma> \<L> U f Z \<Theta>)

  let ?\<sigma>I = "adjoint \<sigma> I \<omega>"
  let ?\<sigma>Z = "vusubst (SBindrs \<sigma>) Z" 
  let ?\<sigma>\<Theta> = "the(alusubst \<sigma> \<L> U \<Theta>)"

  have argsdeft: "alusubst \<sigma> \<L> U \<Theta> \<noteq> undeft" using TFunc.prems salusubst_undeft by fastforce+
  hence saldeft: "salusubst \<sigma> \<L> U Z \<Theta> = Aterm (?\<sigma>Z, ?\<sigma>\<Theta>)" using salusubst_simp by force

  have usspace: "vspace_sem (\<pi>\<^sub>I I) ?\<sigma>Z = vspace_sem (\<pi>\<^sub>I ?\<sigma>I) Z"
    using vusubst_space Bindrs_adjoint_commute by presburger
  have IHargs: "\<And>e. e \<in> set \<Theta> \<Longrightarrow> arg_sem I (the(ausubst \<sigma> \<L> U e)) \<nu> = arg_sem ?\<sigma>I e \<nu>"
    using alusubst_conv TFunc argsdeft by simp

  show ?case
  proof (cases "STFuncs \<sigma> f")
    case None
    hence "ttrm_sem I (the(tusubst \<sigma> \<L> U (TFunc f Z \<Theta>))) \<nu> = ttrm_sem I (TFunc f ?\<sigma>Z ?\<sigma>\<Theta>) \<nu>" 
      using saldeft by fastforce
    also have "... = PInterp (TFuncs I f) (vspace_sem (badjoint (SBindrs \<sigma>) (\<pi>\<^sub>I I)) Z) \<nu> (args_sem (adjoint \<sigma> I \<omega>) \<Theta> \<nu>)"
      using usspace IHargs by (simp add: argsdeft usubst_arglist)
    also have "... = ttrm_sem (adjoint \<sigma> I \<omega>) (TFunc f Z \<Theta>) \<nu>" 
      unfolding adjoint_def adj0_def badjoint_def using None by simp   
    finally show ?thesis .
  next
    case (Some \<sigma>f)
    hence noclash: "((FNE\<^sub>\<L> \<L> (Ettrm \<sigma>f)) - (FVN\<^sub>\<L> \<L> ?\<sigma>Z)) \<inter> U = {}" 
      using TFunc.prems(1) tusubst_func_conv by fastforce
    
    let ?\<sigma>\<^sub>0 = "dotsubst_vec ?\<sigma>\<Theta>"
    let ?X = "vspace_sem (\<pi>\<^sub>I (adjoint \<sigma> I \<nu>)) Z" 
    let ?d = "args_sem I ?\<sigma>\<Theta> \<nu>"

    have "VCagree \<nu> \<omega> (-U)" using TFunc Uvariation_def by simp
    hence "VCagree \<nu> (lmerge \<nu> \<omega> ?X) (-U\<union>(\<iota>\<^sub>V ?X \<union> \<iota>\<^sub>C (\<pi>\<^sub>T ?X \<times> \<Omega>)))" using VCagree_lmerge by simp
    moreover have "FNE (\<pi>\<^sub>I (adjoint ?\<sigma>\<^sub>0 I \<nu>)) \<sigma>f \<subseteq> -U\<union>(\<iota>\<^sub>V ?X \<union> \<iota>\<^sub>C (\<pi>\<^sub>T ?X \<times> \<Omega>))"
    proof -
      have "FVN\<^sub>\<L> \<L> ?\<sigma>Z \<subseteq> \<iota>\<^sub>V ?X \<union> \<iota>\<^sub>C (\<pi>\<^sub>T ?X \<times> \<Omega>)"
        by (metis Bindrs_adjoint_commute CNV_def FNV_def FNV_sound_stat_sem FVV_def TFunc(4) vusubst_space)
      moreover have "FNE\<^sub>\<L> \<L> (Ettrm \<sigma>f) \<subseteq> -U \<union> (FVN\<^sub>\<L> \<L> ?\<sigma>Z)" using noclash by auto      
      moreover have "FNE (\<pi>\<^sub>I (adjoint ?\<sigma>\<^sub>0 I \<nu>)) \<sigma>f \<subseteq> FNE\<^sub>\<L> \<L> (Ettrm \<sigma>f)" 
        using FNE_expr_sound_stat_sem TFunc(4) by presburger
      ultimately show ?thesis by auto
    qed
    ultimately have agree: "VCagree \<nu> (lmerge \<nu> \<omega> ?X) (FNE (\<pi>\<^sub>I (adjoint ?\<sigma>\<^sub>0 I \<nu>)) \<sigma>f)"
      using VCagree_antimon by simp 

      (* unfold usubst definition *)
    have "ttrm_sem I (the(tusubst \<sigma> \<L> U (TFunc f Z \<Theta>))) \<nu> = ttrm_sem I (the(tusubst ?\<sigma>\<^sub>0 \<L> {} \<sigma>f)) \<nu>" 
      using Some noclash saldeft by auto
      (* transfer \<sigma>f from \<nu> to its U-variation \<omega> *)      
    also have "... = ttrm_sem (adjoint ?\<sigma>\<^sub>0 I \<nu>) \<sigma>f \<nu>"
      using saldeft Some TFunc.IH(2) noclash TFunc.prems by simp
      (* apply IH on the dotsubst, which is smaller than \<sigma> as it only replaces dotsymbols *)
    also have "... = ttrm_sem (adjoint ?\<sigma>\<^sub>0 I \<nu>) \<sigma>f (lmerge \<nu> \<omega> ?X)"
      by (metis agree coincidence_ttrm)
      (* evaluate adjoint of I under dotsubst \<sigma>\<^sub>0 *)
    also have "... = ttrm_sem (repc_vec I (dot_repl_vec ?d)) \<sigma>f (lmerge \<nu> \<omega> ?X)" 
      using dotsubst_adj_eq_dotted_interp by simp
      (* definition of adjoint *)
    also have "... = PInterp (TFuncs ?\<sigma>I f) ?X \<nu> ?d"
      using Some is_pinterp_adjoint_tfuncs tprdnl_def by simp 
      (* apply IH to the argument list \<Theta>, which is smaller than f(Z)(\<Theta>) *)
    also have "... = PInterp (TFuncs ?\<sigma>I f) ?X \<nu> (args_sem ?\<sigma>I \<Theta> \<nu>)" 
      using argsdeft IHargs usubst_arglist by auto
      (* unfold the semantics of the function symbol f(Z)(\<Theta>) *)
    also have "... = ttrm_sem ?\<sigma>I (TFunc f Z \<Theta>) \<nu>" by auto
    finally show "ttrm_sem I (the(tusubst \<sigma> \<L> U (TFunc f Z \<Theta>))) \<nu> = ttrm_sem ?\<sigma>I (TFunc f Z \<Theta>) \<nu>" .
  qed
next
  case (Empty \<sigma> \<L> U)
  then show ?case by simp
next
  case (ComItm \<sigma> \<L> U ch \<theta>\<^sub>1 \<theta>\<^sub>2)
  then show ?case using ComItmo_undef by auto
next
  case (Concat \<sigma> \<L> U te\<^sub>1 te\<^sub>2)
  then show ?case using Concato_undef by auto
next
  case (Proj \<sigma> \<L> U te Y)
  then show ?case using Projo_undef usubst_cspace by auto
next
  case (Access \<sigma> \<L> U te \<theta>)
  then show ?case using Accesso_undef by auto
next
  case (RArg \<sigma> \<L> U \<theta>)
  then show ?case using RArgo_undef by auto
next
  case (TArg \<sigma> \<L> U te)
  then show ?case using TArgo_undef by auto
qed



subsection \<open>Uniform Substitution Preserves Synchronization\<close>


lemma concrete_Chp_CN: "concrete_vspace_chp \<alpha> \<Longrightarrow> CN J \<alpha> = CN\<^sub>P \<alpha>"
  apply (induction \<alpha> rule: chp_induct)
  using CN\<^sub>C_concrete_cspace by auto

lemma CN_usubst_eq: "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp \<Longrightarrow> CN J (usubstpp \<sigma> \<L> U \<alpha>) = CN (badjoint (SBindrs \<sigma>) J) \<alpha>"
proof (induction \<alpha> arbitrary: U rule: chp_induct)
  case (Chp a Z Y)
  then show ?case
  proof (cases "SChps0 \<sigma> a")
    case None
    then show ?thesis by (simp add: usubst_cspace usubstchp_def)
  next
    case (Some \<sigma>a)

    let ?\<sigma>X = "vusubst (SBindrs \<sigma>) Z"
    let ?\<sigma>Y = "cusubst (SBindrs \<sigma>) Y"
    
    have conv: "concrete_cspace ?\<sigma>Y \<and> concrete_vspace_chp \<sigma>a \<and> CN\<^sub>P \<sigma>a = UCN\<^sub>C ?\<sigma>Y"
      using Some Chp usubstapp_chp_conv by fastforce

    have res: "the(snd(usubstchp \<sigma> \<L> U a ?\<sigma>X ?\<sigma>Y)) = \<sigma>a"
      unfolding usubstchp_def using Some Chp.prems usubstapp_chp_conv by fastforce

    hence "CN J (usubstpp \<sigma> \<L> U (Chp a Z Y)) = CN J \<sigma>a" by simp
      (* semantical channel space equals syntactical space as the replacement is constant-free *)
    also have "... = CN\<^sub>P \<sigma>a" using conv concrete_Chp_CN by simp
      (* replacement has same concrete channel set than the channel space by the usubst condition *)
    also have "... = UCN\<^sub>C ?\<sigma>Y" using conv by simp
      (* the channel space equals its semantics as it is constant-free *)
    also have "... = (cspace_sem J ?\<sigma>Y)" 
      using CN\<^sub>C_concrete_cspace conv by simp
      (* the result of substitution for the space equals its adjoint bindr interpretation *)
    also have "... = CN (badjoint (SBindrs \<sigma>) J) (Chp a Z Y)"  by (simp add: usubst_cspace)
    finally show ?thesis .
  qed
next
  case (Assign x \<theta>)
  hence "usubstpp \<sigma> \<L> U (x := \<theta>) = Assign x (the(rusubst \<sigma> \<L> U \<theta>))" using Unaryo.elims by force
  then show ?case by simp
next
  case (Nondet x)
  then show ?case by simp
next
  case (Test \<phi>)
  then show ?case using Unaryo.elims by force
next
  case (Evolution x \<theta> \<phi>)
  then show ?case using Binaryo.elims by force 
next
  case (Choice \<alpha> \<beta>)
  hence "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp \<and> snd(usubstp \<sigma> \<L> U \<beta>) \<noteq> undefp" 
    using usubstp_choice_conv by blast
  thus ?case using Choice.IH by force
next
  case (Compose \<alpha> \<beta>)
  let ?V = "fst(usubstp \<sigma> \<L> U \<alpha>)"
  have deft: "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp \<and> snd(usubstp \<sigma> \<L> ?V \<beta>) \<noteq> undefp"
    by (meson Compose.prems usubstp_compose_conv)
  hence "CN (badjoint (SBindrs \<sigma>) J) \<beta> = CN J (usubstpp \<sigma> \<L> ?V \<beta>)" 
    using Compose.IH by auto
  thus ?case using Compose.IH deft by force
next
  case (Loop \<alpha>)
  have "snd(usubstp \<sigma> \<L> (fst(usubstp \<sigma> \<L> U \<alpha>)) \<alpha>) \<noteq> undefp" 
    using Loop.prems usubstp_loop_conv by presburger
  then show ?case using Loop.IH Loop.prems Loop.prems by force
next
  case (Send ch h \<theta>)
  hence "usubstpp \<sigma> \<L> U (Send ch h \<theta>) = Send ch h (the(rusubst \<sigma> \<L> U \<theta>))" 
    using Unaryo.elims by force
  then show ?case by simp
next
  case (Receive ch h x)
  then show ?case by simp
next
  case (Par \<alpha> \<beta>)
  hence "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp \<and> snd(usubstp \<sigma> \<L> U \<beta>) \<noteq> undefp" 
    using usubstp_par_conv by blast
  then show ?case using Par.IH by force
qed



subsection \<open>Uniform Substitution for Formulas and Programs\<close>

paragraph \<open>Uvariation in Reachable Worlds\<close>

lemma Vagree_upds: "Vagree \<nu> \<omega> X \<Longrightarrow> sorteq z d \<Longrightarrow> Vagree (upds \<nu> z d) \<omega> (X \<inter> -{z})"
  unfolding Vagree_def by auto

lemma Bv_in_cproj: "\<pi>\<^sub>C (-(U \<union> {Bv z})) = \<pi>\<^sub>C (-U)" by simp

lemma stR_trepv: "stR (trepv \<nu> h \<tau>) = stR \<nu>" by (simp add: trepv_def_correct)

lemma sfilter_rrepv_commute: "sfilter (rrepv \<nu> x r) C = rrepv (sfilter \<nu> C) x r"
  apply (rule state_eq_by_sortI)
   apply (simp add: rrepv_def sfilter_def)
  using rrepv_def stT_sfilterI by fastforce


lemma sfilter_trepv_commute: "sfilter (trepv \<nu> h \<tau>) C = trepv (sfilter \<nu> C) h (\<tau> \<down> (C `` {h}))"
  apply (rule state_eq_by_sortI)
   apply (simp add: sfilter_def stR_trepv)
  using tsfilter_def by fastforce

lemma sorteq_P_I: "sorteq z d \<Longrightarrow> P (Rv (getrv z)) (Rp (rval d)) \<Longrightarrow> P (Tv (gettv z)) (Tp (tval d)) \<Longrightarrow> P z d"
  using sorteq_def by force

lemma Uvariation_upds: "Uvariation \<nu> \<omega> U \<Longrightarrow> sorteq z d \<Longrightarrow> Uvariation (upds \<nu> z d) \<omega> (U \<union> {Bv z})"
  unfolding Uvariation_def VCagree_def
  apply (rule sorteq_P_I)
  apply (simp_all add: sfilter_rrepv_commute sfilter_trepv_commute)
  by (simp_all add: Vagree_def)



lemma VCagree_sttconc_cong: "VCagree \<nu> \<kappa> U \<Longrightarrow> VCagree (\<nu> @@ \<tau>) (\<kappa> @@ \<tau>) U"
  unfolding VCagree_def using Vagree_sttconc_cong sfilter_dist_sttconc by presburger
                                                         








lemma bound_effect_inifin0: "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> Vagree \<nu> \<omega> (-BVP (\<pi>\<^sub>I I) \<alpha> \<union> (\<iota>\<^sub>T \<V>\<^sub>T))"
  using bound_effect_property_short Vagree_union bound_effect_on_state(2) by blast

lemma bound_effect_inifin: "is_sound_stat_sem \<L> \<Longrightarrow> (\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> Vagree \<nu> \<omega> (-BVP\<^sub>\<L> \<L> \<alpha> \<union> (\<iota>\<^sub>T \<V>\<^sub>T))"
proof -
  assume "is_sound_stat_sem \<L>"
  hence "-BVP\<^sub>\<L> \<L> \<alpha> \<union> (\<iota>\<^sub>T \<V>\<^sub>T) \<subseteq> -BVP (\<pi>\<^sub>I I) \<alpha> \<union> (\<iota>\<^sub>T \<V>\<^sub>T)" using BVP_sound_stat_sem by blast
  thus "(\<nu>, \<tau>, Fin \<omega>) \<in> chp_sem I \<alpha> \<Longrightarrow> Vagree \<nu> \<omega> (-BVP\<^sub>\<L> \<L> \<alpha> \<union> (\<iota>\<^sub>T \<V>\<^sub>T))" 
    using bound_effect_inifin0 Vagree_antimon by blast
qed





text \<open>Initial and final state of a run of a substitution result at most vary on the output taboo.\<close>
lemma uvari_of_run: 
  assumes sound_stat: "is_sound_stat_sem \<L>"
  assumes defp: "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp"
  assumes run: "(\<nu>, \<tau>, Fin \<o>) \<in> chp_sem I (usubstpp \<sigma> \<L> U \<alpha>)"
  shows "Uvariation \<nu> \<o> (fst(usubstp \<sigma> \<L> U \<alpha>))"
proof -
  let ?\<sigma>\<alpha> = "usubstpp \<sigma> \<L> U \<alpha>"
  have "Vagree \<nu> \<o> (-BVP\<^sub>\<L> \<L> ?\<sigma>\<alpha> \<union> (\<iota>\<^sub>T \<V>\<^sub>T))" using run bound_effect_inifin sound_stat by simp
  hence "VCagree \<nu> \<o> (-\<iota>\<^sub>V ((BVP\<^sub>\<L> \<L> ?\<sigma>\<alpha>) - (\<iota>\<^sub>T \<V>\<^sub>T)))"
    by (metis Compl_Diff_eq VCagree_def Vagree_sfilter_cong \<pi>\<^sub>V_compl \<pi>\<^sub>V_inverse)
  moreover have "-\<iota>\<^sub>V (BVP\<^sub>\<L> \<L> ?\<sigma>\<alpha> - (\<iota>\<^sub>T \<V>\<^sub>T)) \<supseteq> -(fst(usubstp \<sigma> \<L> U \<alpha>))"
    using sound_stat defp output_taboo_compl_pi 
    unfolding BVP\<^sub>\<L>_def apply (simp add: iota_vars_def pi_vars_def) by blast
  ultimately show "Uvariation \<nu> \<o> (fst(usubstp \<sigma> \<L> U \<alpha>))" 
    by (meson Compl_anti_mono Uvariation_def VCagree_antimon inf.boundedI usubst_taboo_pre_fp)
qed

(* used for sequential composition *)
lemma transfer_uvari_over_run: "is_sound_stat_sem \<L> \<Longrightarrow> snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp 
  \<Longrightarrow> (\<nu>, \<tau>, Fin \<o>) \<in> chp_sem I (usubstpp \<sigma> \<L> U \<alpha>) \<Longrightarrow> Uvariation \<nu> \<omega> U \<Longrightarrow> Uvariation \<o> \<omega> (fst(usubstp \<sigma> \<L> U \<alpha>))"
  using uvari_of_run unfolding Uvariation_def
  by (meson VCagree_antimon VCagree_sym_rel VCagree_trans output_taboo_compl)





lemma BNP\<^sub>\<L>_sem_stat_sem [simp]: "BNP\<^sub>\<L> (\<L>\<^sub>0 J) \<alpha> = BNP J \<alpha>" by (simp add: sem_stat_sem_def)


lemma BNP\<^sub>\<L>_sound: "is_sound_stat_sem \<L> \<Longrightarrow> BNP J \<alpha> \<subseteq> BNP\<^sub>\<L> \<L> \<alpha>"
  unfolding is_sound_stat_sem_def stat_sem_porder_def by simp


lemma CNP\<^sub>\<L>_sound: "is_sound_stat_sem \<L> \<Longrightarrow> CNP J \<alpha> \<subseteq> CNP\<^sub>\<L> \<L> \<alpha>"
  using BNP\<^sub>\<L>_sound unfolding BNP_partition CNP\<^sub>\<L>_def using comtar_mono by auto  



text \<open>Initial state and intermediate worlds of a run of a substitution result vary at most on the 
output taboo.\<close>
lemma uvari_of_run_com: 
  assumes sound_stat: "is_sound_stat_sem \<L>"
  assumes defp: "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp"
  assumes run: "(\<nu>, \<tau>, \<o>) \<in> chp_sem I (usubstpp \<sigma> \<L> U \<alpha>)"
  shows "\<tau>' \<preceq> \<tau> \<Longrightarrow> Uvariation (\<nu> @@ \<tau>') \<nu> (fst(usubstp \<sigma> \<L> U \<alpha>))" 
proof -
  let ?Z = "fst(usubstp \<sigma> \<L> U \<alpha>)"
  have "\<And>h. byrec \<tau> h \<down> (-CNP (\<pi>\<^sub>I I) (usubstpp \<sigma> \<L> U \<alpha>)) `` {h} = []" 
    using bound_effect_on_com2 run by blast
  moreover have "\<pi>\<^sub>C (-?Z) \<subseteq> -(CNP\<^sub>\<L> \<L> (usubstpp \<sigma> \<L> U \<alpha>))" 
    using sound_stat defp output_taboo_compl_pi 
    unfolding CNP\<^sub>\<L>_def by (fastforce simp add: iota_comtar_def pi_comtar_def)
  moreover have "-(CNP\<^sub>\<L> \<L> (usubstpp \<sigma> \<L> U \<alpha>)) \<subseteq> -(CNP (\<pi>\<^sub>I I) (usubstpp \<sigma> \<L> U \<alpha>))"
    using sound_stat CNP\<^sub>\<L>_sound by simp
  ultimately have empty: "\<And>h.  byrec \<tau> h \<down> (\<pi>\<^sub>C (-?Z) `` {h}) = []" 
    by (meson Image_mono subset_iff tfilter_empty_antimon)
   
  hence empty2: "\<And>h. \<tau>' \<preceq> \<tau> \<Longrightarrow> byrec \<tau>' h \<down> (\<pi>\<^sub>C (-?Z) `` {h}) = []"
    using byrec_mono_prefix tfilter_mono_prefix by (metis prefix_Nil)
  assume 0: "\<tau>' \<preceq> \<tau>"
  show ?thesis unfolding Uvariation_def VCagree_def
    apply (rule Vagree_by_sortI)
     apply (metis eqon_def Vagree_allrvars Vagree_sfilter_cong Vagree_self_sttconc_on_rvars)
    using 0 empty2 tsfilter_def apply (simp add: sfilter_dist_sttconc del: stT_sfilter)
    using rec_tfilter_empty_byrecI by simp 
qed

lemma transfer_uvari_over_run2:
  assumes sound_stat: "is_sound_stat_sem \<L>"
  assumes defp: "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp"
  assumes run: "(\<nu>, \<tau>, \<o>) \<in> chp_sem I (usubstpp \<sigma> \<L> U \<alpha>)"
  assumes uvari: "Uvariation \<nu> \<omega> U"
  shows "\<tau>' \<preceq> \<tau> \<Longrightarrow> Uvariation (\<nu> @@ \<tau>') \<omega> (fst(usubstp \<sigma> \<L> U \<alpha>))"
  using assms 
  by (meson Uvariation_def VCagree_antimon VCagree_trans output_taboo_compl uvari_of_run_com)

lemma Uvariation_sttconc_cong: "Uvariation \<nu> \<o> U \<Longrightarrow> (Uvariation (\<nu> @@ \<tau>) (\<o> @@ \<tau>) U)"
  unfolding Uvariation_def using VCagree_sttconc_cong by simp

lemma uvari_fin_state:
  assumes sound_stat: "is_sound_stat_sem \<L>"
  assumes defp: "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp"  
  assumes run: "(\<nu>, \<tau>, Fin \<o>) \<in> chp_sem I (usubstpp \<sigma> \<L> U \<alpha>)"
  assumes uvari: "Uvariation \<nu> \<omega> U"
  shows "Uvariation (\<o> @@ \<tau>) \<omega> (fst(usubstp \<sigma> \<L> U \<alpha>))"
proof -
  have "Uvariation (\<nu> @@ \<tau>) \<omega> (fst(usubstp \<sigma> \<L> U \<alpha>))" using assms transfer_uvari_over_run2 by simp
  thus ?thesis using assms by (meson Uvariation_def Uvariation_sym VCagree_sttconc_cong VCagree_trans uvari_of_run)
qed

(* TODO unused ?
lemma transfer_uvari_over_run3:
  assumes defp: "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp"
  assumes run: "(\<nu>, \<tau>, Fin \<o>) \<in> chp_sem I (usubstpp \<sigma> \<L> U \<alpha>)"
  assumes uvari: "Uvariation \<nu> \<omega> U"
  shows "\<tau>' \<preceq> \<tau> \<Longrightarrow> Uvariation (\<o> @@ \<tau>') \<omega> (fst(usubstp \<sigma> \<L> U \<alpha>))"
proof -
  let ?Z = "fst(usubstp \<sigma> \<L> U \<alpha>)"
  assume 0: "\<tau>' \<preceq> \<tau>"
  have "VCagree \<o> \<nu> (-?Z)" using Uvariation_def Uvariation_sym_rel defp run uvari_of_run by metis
  hence "VCagree (\<o> @@ \<tau>') (\<nu> @@ \<tau>') (-?Z)" using VCagree_sttconc_cong by presburger
  moreover have "VCagree (\<nu> @@ \<tau>') \<nu> (-?Z)" 
    using 0 by (meson Uvariation_def Uvariation_sym_rel defp run uvari_of_run_com)
  moreover have "VCagree \<nu> \<omega> (-?Z)"
    using Uvariation_def VCagree_antimon defp output_taboo_compl uvari by presburger
  ultimately show "Uvariation (\<o> @@ \<tau>') \<omega> ?Z" by (meson Uvariation_def VCagree_trans)
qed *)





abbreviation usubstIH
  where "usubstIH \<sigma> \<L> I U \<alpha> \<omega> \<equiv> (\<forall>\<nu> \<tau> \<o>. snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp \<longrightarrow> Uvariation \<nu> \<omega> U 
    \<longrightarrow> ((\<nu>, \<tau>, \<o>) \<in> chp_sem I (usubstpp \<sigma> \<L> U \<alpha>)) = ((\<nu>, \<tau>, \<o>) \<in> chp_sem (adjoint \<sigma> I \<omega>) \<alpha>))"

lemma usubst_chp_compose:
  assumes sound_stat: "is_sound_stat_sem \<L>"
  assumes alphaIH: "usubstIH \<sigma> \<L> I U \<alpha> \<omega>"
  assumes betaIH: "usubstIH \<sigma> \<L> I (fst(usubstp \<sigma> \<L> U \<alpha>)) \<beta> \<omega>"
  assumes defp: "snd(usubstp \<sigma> \<L> U (\<alpha> ;; \<beta>)) \<noteq> undefp"
  assumes uvari: "Uvariation \<nu> \<omega> U"
  shows "((\<nu>, \<tau>, \<o>) \<in> chp_sem I (usubstpp \<sigma> \<L> U (\<alpha> ;; \<beta>))) =
       ((\<nu>, \<tau>, \<o>) \<in> chp_sem (adjoint \<sigma> I \<omega>) (\<alpha> ;; \<beta>))"
proof -
  let ?V = "fst(usubstp \<sigma> \<L> U \<alpha>)"
  let ?\<sigma>\<alpha> = "usubstpp \<sigma> \<L> U \<alpha>"
  let ?\<sigma>\<beta> = "usubstpp \<sigma> \<L> ?V \<beta>"
  let ?\<sigma>I = "adjoint \<sigma> I \<omega>"

  have adeft: "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp" and bdeft: "snd(usubstp \<sigma> \<L> ?V \<beta>) \<noteq> undefp"
    using defp usubstp_compose_conv by auto

  hence "\<And>\<tau> \<kappa>. (\<nu>, \<tau>, Fin \<kappa>) \<in> chp_sem I (usubstpp \<sigma> \<L> U \<alpha>) \<Longrightarrow> Uvariation \<kappa> \<omega> ?V"
    using transfer_uvari_over_run uvari sound_stat by simp

  hence "\<And>\<tau>\<^sub>1 \<kappa> \<tau>\<^sub>2. ((\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> chp_sem I ?\<sigma>\<alpha> \<and> (\<kappa>, \<tau>\<^sub>2, \<o>) \<in> (chp_sem I (usubstpp \<sigma> \<L> ?V \<beta>))) 
    = ((\<nu>, \<tau>\<^sub>1, Fin \<kappa>) \<in> chp_sem ?\<sigma>I \<alpha> \<and> (\<kappa>, \<tau>\<^sub>2, \<o>) \<in> (chp_sem ?\<sigma>I \<beta>))"
    using adeft alphaIH betaIH bdeft uvari by blast
  hence cont: "(\<nu>, \<tau>, \<o>) \<in> (chp_sem I ?\<sigma>\<alpha> \<triangleright> (chp_sem I ?\<sigma>\<beta>))
     = ((\<nu>, \<tau>, \<o>) \<in> (chp_sem ?\<sigma>I \<alpha> \<triangleright> chp_sem ?\<sigma>I \<beta>))" by auto

  have "\<And>\<kappa>. (\<nu>, \<tau>, \<kappa>) \<in> chp_sem I ?\<sigma>\<alpha> = ((\<nu>, \<tau>, \<kappa>) \<in> chp_sem ?\<sigma>I \<alpha>)" 
    using adeft alphaIH uvari by presburger

  then show ?thesis using cont adeft bdeft by force
qed  

lemma Chps_fail: "(SChps0 \<sigma>) a = undefp \<Longrightarrow> (Chps (adjoint \<sigma> I \<omega>)) a Z Y = (Chps I) a Z Y"
  by (simp add: adjoint_def adj0_def Chps_def adj0_Chps_def)
  
lemma Chps_match: "(SChps0 \<sigma>) a = Achp \<sigma>a \<Longrightarrow> sound_chp_subst I \<sigma>a Z Y 
    \<Longrightarrow> (Chps (adjoint \<sigma> I \<omega>)) a Z Y = chp_sem I \<sigma>a"
  by (simp add: adjoint_def adj0_def Chps_def adj0_Chps_def)





paragraph \<open>Parallel Semantics with Parametric Merging\<close>

text \<open>Semantics for parallel CHPs parameterized in the notion of bound variables used for merging 
the final states.\<close>
definition chp_alt_sem_par :: "stat_sem \<Rightarrow> interp \<Rightarrow> chp \<Rightarrow> chp \<Rightarrow> chp_domain set"
  where "chp_alt_sem_par \<L> I \<alpha> \<beta> = {(\<nu>, \<tau>, \<omega>) | \<nu> \<tau> \<omega>. \<exists>\<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta>. 
    (\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha>), \<omega>\<^sub>\<alpha>) \<in> chp_sem I \<alpha> \<and> (\<nu>, \<tau> \<down> (CN (\<pi>\<^sub>I I) \<beta>), \<omega>\<^sub>\<beta>) \<in> chp_sem I \<beta> \<and>
    (Vagreebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> \<V>\<^sub>\<mu>) \<and> (\<omega> = lmergebot \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> (BVP\<^sub>\<L> \<L> \<alpha>)) \<and> \<tau> \<down> (CN (\<pi>\<^sub>I I) \<alpha> \<union> CN (\<pi>\<^sub>I I) \<beta>) = \<tau>}"

(* TODO remove doubled 

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
      hence "Rv x \<notin> BVP (\<pi>\<^sub>I I) \<beta> \<or> Rv x \<in> \<V>\<^sub>\<mu>" using soundBV assms by force
      moreover have "stR \<nu> x = stR \<omega>\<^sub>\<alpha> x" using False BVP_elem alpha by force
      ultimately show ?thesis
        apply (cases "Rv x \<in> \<V>\<^sub>\<mu>")
        using Vagree_def beta BVP_elem False gtime lmerge_def apply auto[1]
        by (metis assms(1,2,3,4,5) lmerge_BVP_cong_soundBV)
    qed
  qed
next
  case stT  
  have "Vagree \<omega>\<^sub>\<alpha> \<omega>\<^sub>\<beta> (\<iota>\<^sub>T \<V>\<^sub>T)" 
    by (meson Vagree_sym Vagree_only_trans alpha beta bound_effect_on_state(2))
  hence "stT \<omega>\<^sub>\<alpha> = stT \<omega>\<^sub>\<beta>" using Vagree_alltvars by blast
  thus ?case unfolding lmerge_def by auto
qed      *) 

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



paragraph \<open>Uniform Substitution Lemmas\<close>


definition wf_chpsubs :: "stat_sem \<Rightarrow> (ident \<rightharpoonup> chp) \<Rightarrow> bool"
  where "wf_chpsubs \<L> \<sigma> = (\<forall>a. case \<sigma> a of
      None \<Rightarrow> True
    | Some \<sigma>a \<Rightarrow> wf_chp \<L> \<sigma>a)"

definition wf_folr_subs :: "stat_sem \<Rightarrow> (ident \<rightharpoonup> FOL\<^sub>R) \<Rightarrow> bool"
  where "wf_folr_subs \<L> \<sigma> = (\<forall>p. case \<sigma> p of      
      None \<Rightarrow> True
    | Some \<sigma>p \<Rightarrow> wf_fml \<L> (FOL\<^sub>R_raw \<sigma>p))"

definition wf_fmlsubs :: "stat_sem \<Rightarrow> (ident \<rightharpoonup> fml) \<Rightarrow> bool"
  where "wf_fmlsubs \<L> \<sigma> = (\<forall>p. case \<sigma> p of
      None \<Rightarrow> True
    | Some \<sigma>p \<Rightarrow> wf_fml \<L> \<sigma>p)"

definition wf_usubs :: "stat_sem \<Rightarrow> usubst \<Rightarrow> bool"
  where "wf_usubs \<L> \<sigma> \<equiv> wf_folr_subs \<L> (SFOL\<^sub>RPsymbs0 \<sigma>) \<and> wf_fmlsubs \<L> (SPsymbs \<sigma>) \<and> wf_chpsubs \<L> (SChps0 \<sigma>)"

lemma SFOL\<^sub>RPsymbs0_dotsubst_vec_empty [simp]: "SFOL\<^sub>RPsymbs0 (dotsubst_vec []) p = None"
  by (simp add: dotsubst_vec_def)

lemma SFOL\<^sub>RPsymbs0_dotsubst [simp]: "SFOL\<^sub>RPsymbs0 (dotsubst n e) p = None"
  apply (cases "e")
  by (simp_all add: rdotsubst_def tdotsubst_def)

lemma SFOL\<^sub>RPsymbs0_dotsubst_vec [simp]: "SFOL\<^sub>RPsymbs0 (dotsubst_vec_rec n \<Theta>) a = None"
  apply (induction \<Theta> arbitrary: n)
  by (simp_all add: SFOL\<^sub>RPsymbs0_usubst_sum_dist)

lemma SPsymbs_dotsubst_vec_empty [simp]: "SPsymbs (dotsubst_vec []) p = None"
  by (simp add: dotsubst_vec_def)

lemma SPsymbs_dotsubst [simp]: "SPsymbs (dotsubst n e) p = undeff"
  apply (cases "e")
  by (simp_all add: rdotsubst_def tdotsubst_def)

lemma SPsymbs_dotsubst_vec [simp]: "SPsymbs (dotsubst_vec_rec n \<Theta>) a = undeff"
  apply (induction \<Theta> arbitrary: n)
  by (simp_all add: SPsymbs_usubst_sum_dist)

lemma SChps0_dotsubst_vec_empty [simp]: "SChps0 (dotsubst_vec []) a = None"
  by (simp add: dotsubst_vec_def)

lemma SChps0_dotsubst [simp]: "SChps0 (dotsubst n e) a = undefp"
  apply (cases "e")
  by (simp_all add: rdotsubst_def tdotsubst_def)

lemma SChps0_dotsubst_vec [simp]: "SChps0 (dotsubst_vec_rec n \<Theta>) a = undefp"
  apply (induction \<Theta> arbitrary: n)
  by (simp_all add: SChps0_usubst_sum_dist)
  
lemma wf_repl_dotsubst_vec [simp]: "wf_usubs \<L> (dotsubst_vec \<Theta>)"
  by (simp add: wf_usubs_def wf_folr_subs_def wf_fmlsubs_def wf_chpsubs_def dotsubst_vec_def)


lemma Domain_CND_tvars_BVD: "\<And>D. DiffD D \<subseteq> \<iota>\<^sub>R \<V>\<^sub>R \<Longrightarrow> Domain (CND D) \<subseteq> \<pi>\<^sub>T (BVD D)"
  unfolding CND_def BVD_def pi_tvars_def by (fastforce simp add: stT_sttconc_dist)


lemma TCN\<^sub>P_overapprox_CN\<^sub>P: "TCN\<^sub>P Z \<subseteq> \<V>\<^sub>T \<times> CN\<^sub>P Z" by (induction Z) (auto)

lemma Uvariation_Vagree_extend: "Uvariation \<nu> \<omega> U \<Longrightarrow> Vagree \<nu> \<nu>' (-X) \<Longrightarrow> Uvariation \<nu>' \<omega> (U\<union>\<iota>\<^sub>V X)"
  unfolding Uvariation_def VCagree_def apply simp  
  by (meson Vagree_sfilter_cong Vagree_sym Vagree_trans) 

lemma Vagree_solves_ODE: "Vagree \<nu> (F(0)) (-{Rv (DVarName x)}) \<Longrightarrow> solves_ODE I F x \<theta> \<Longrightarrow> Vagree \<nu> (F(\<zeta>)) (-bvrident x)"
proof - 
  assume "Vagree \<nu> (F(0)) (-{Rv (DVarName x)})"
  hence "Vagree \<nu> (F(0)) (-bvrident x)" by auto
  moreover assume "solves_ODE I F x \<theta>"
  ultimately show "Vagree \<nu> (F(\<zeta>)) (-bvrident x)" unfolding solves_ODE_def using Vagree_only_trans by blast
qed

lemma Uvariation_solves_ODE: "Uvariation \<nu> \<omega> U \<Longrightarrow> Vagree \<nu> (F(0)) (-{Rv (DVarName x)}) \<Longrightarrow> solves_ODE I F x \<theta> 
    \<Longrightarrow> Uvariation (F(\<zeta>)) \<omega> (U\<union>\<iota>\<^sub>V(bvrident x))"
  using Uvariation_Vagree_extend Vagree_solves_ODE by blast


lemma solves_Vagree: "solves_ODE I F x \<theta> \<Longrightarrow> (\<And>\<zeta>. Vagree (F(\<zeta>)) (F(0)) (-(bvrident x)))"
  using solves_ODE_def Vagree_sym_rel by blast 

lemma solves_VCagree: "solves_ODE I F x \<theta> \<Longrightarrow> (\<And>\<zeta>. VCagree (F(\<zeta>)) (F(0)) (-\<iota>\<^sub>V(bvrident x)))"
  unfolding VCagree_def using solves_Vagree by simp

lemma Uvariation_trans [trans]: "Uvariation \<omega> \<nu> U \<Longrightarrow> Uvariation \<nu> \<kappa> (\<iota>\<^sub>V (\<iota>\<^sub>R X)) \<Longrightarrow> Uvariation \<omega> \<kappa> (U \<union> \<iota>\<^sub>V (\<iota>\<^sub>R X))"
  unfolding Uvariation_def
  by (metis Uvariation_VCagree Uvariation_Vagree_extend VCagree_def VCagree_sym \<pi>\<^sub>C_anyvars \<pi>\<^sub>C_compl \<pi>\<^sub>V_compl \<pi>\<^sub>V_inverse
      allcomtar_def compl_bot_eq double_complement sfilter_all)

lemma Uvariation_mon [simp]: "V \<supseteq> U \<Longrightarrow> Uvariation \<omega> \<nu> U \<Longrightarrow> Uvariation \<omega> \<nu> V"
  unfolding Uvariation_def by auto

lemma solves_Vagree_trans: "Uvariation (F(0)) \<omega> U \<Longrightarrow> solves_ODE I F x \<theta> \<Longrightarrow> Uvariation (F(\<zeta>)) \<omega> (U\<union>\<iota>\<^sub>V(bvrident x))"
  using solves_VCagree Uvariation_VCagree solves_ODE_def
  
  by (meson Uvariation_solves_ODE Vagree_refl)


paragraph \<open>Lemmas for Uniform Substitution of Evolutions\<close>

text \<open>The lemmas in this section are adapted from the formalization of Differential Game Logic.\<close>

lemma same_ODE_same_sol:
  "(\<And>\<nu>. Uvariation \<nu> (F(0)) (\<iota>\<^sub>V(bvrident x)) \<Longrightarrow> rtrm_sem I \<theta> \<nu> = rtrm_sem J \<eta> \<nu>)
  \<Longrightarrow> solves_ODE I F x \<theta> = solves_ODE J F x \<eta>"
  using Uvariation_Vagree Vagree_def solves_ODE_def
proof -
  assume va: "\<And>\<nu>. Uvariation \<nu> (F(0)) (\<iota>\<^sub>V(bvrident x)) \<Longrightarrow> rtrm_sem I \<theta> \<nu> = rtrm_sem J \<eta> \<nu>"
  then have va2: "\<And>\<nu>. Uvariation \<nu> (F(0)) (\<iota>\<^sub>V(bvrident x)) \<Longrightarrow> rtrm_sem J \<eta> \<nu> = rtrm_sem I \<theta> \<nu>" by simp
  have one: "\<And>I J \<theta> \<eta>. (\<And>\<nu>. Uvariation \<nu> (F(0)) (\<iota>\<^sub>V(bvrident x)) \<Longrightarrow> rtrm_sem I \<theta> \<nu> = rtrm_sem J \<eta> \<nu>)
   \<Longrightarrow> solves_ODE I F x \<theta> \<Longrightarrow> solves_ODE J F x \<eta>"
   proof-
     fix I J \<theta> \<eta>
     assume vaflow: "\<And>\<nu>. Uvariation \<nu> (F(0)) (\<iota>\<^sub>V(bvrident x)) \<Longrightarrow> rtrm_sem I \<theta> \<nu> = rtrm_sem J \<eta> \<nu>"
     assume sol: "solves_ODE I F x \<theta>"
     from vaflow and sol show "solves_ODE J F x \<eta>" unfolding solves_ODE_def using Uvariation_Vagree coincidence_rtrm
     by (metis double_complement solves_Vagree sol)
  qed
  show "solves_ODE I F x \<theta> = solves_ODE J F x \<eta>" using one[where \<theta>=\<theta> and \<eta>=\<eta>, OF va] one[where \<theta>=\<eta> and \<eta>=\<theta>, OF va2] 
  by force
qed

lemma usubst_ode:
  assumes sound_stat_sem: "is_sound_stat_sem \<L>"
  assumes subdef: "rusubst \<sigma> \<L> (\<iota>\<^sub>V(bvrident x)) \<theta> \<noteq> undeft"
  shows "solves_ODE I F x (the (rusubst \<sigma> \<L> (\<iota>\<^sub>V(bvrident x)) \<theta>)) = solves_ODE (adjoint \<sigma> I (F(0))) F x \<theta>"
proof-
  have vaflow: "\<And>F \<theta> \<zeta>. solves_ODE I F x \<theta> \<Longrightarrow> Uvariation (F(\<zeta>)) (F(0)) (\<iota>\<^sub>V(bvrident x))" 
    unfolding Uvariation_def by (simp add: solves_VCagree)
  from subdef have IH: "\<And>\<nu>. Uvariation \<nu> (F(0)) (\<iota>\<^sub>V(bvrident x)) \<Longrightarrow> rtrm_sem I (the (rusubst \<sigma> \<L> (\<iota>\<^sub>V(bvrident x)) \<theta>)) \<nu> 
    = rtrm_sem (adjoint \<sigma> I (F(0))) \<theta> \<nu>" using sound_stat_sem by (simp add: usubst_term)
  then show ?thesis using IH vaflow solves_ODE_def Uvariation_Vagree same_ODE_same_sol by blast  
qed

lemma usubst_ode_ext:
  assumes sound_stat_sem: "is_sound_stat_sem \<L>"
  assumes uv: "Uvariation (F(0)) \<omega> (U\<union>\<iota>\<^sub>V(bvrident x))"
  assumes subdef: "rusubst \<sigma> \<L> (U\<union>\<iota>\<^sub>V(bvrident x)) \<theta> \<noteq> undeft"
  shows "solves_ODE I F x (the (rusubst \<sigma> \<L> (U\<union>\<iota>\<^sub>V(bvrident x)) \<theta>)) = solves_ODE (adjoint \<sigma> I \<omega>) F x \<theta>"
proof-
  have vaflow1: "\<And>F \<theta> \<zeta>. solves_ODE I F x (the (rusubst \<sigma> \<L> (U\<union>\<iota>\<^sub>V(bvrident x)) \<theta>)) \<Longrightarrow> Uvariation (F(\<zeta>)) (F(0)) (\<iota>\<^sub>V(bvrident x))" 
    unfolding Uvariation_def by (simp add: solves_VCagree)
  have vaflow2: "\<And>F \<theta> \<zeta>. solves_ODE (adjoint \<sigma> I \<omega>) F x \<theta> \<Longrightarrow> Uvariation (F(\<zeta>)) (F(0)) (\<iota>\<^sub>V(bvrident x))" 
    unfolding Uvariation_def by (simp add: solves_VCagree)
  from subdef have IH: "\<And>\<nu>. Uvariation \<nu> (F(0)) (U\<union>\<iota>\<^sub>V(bvrident x)) \<Longrightarrow> rtrm_sem I (the (rusubst \<sigma> \<L> (U\<union>\<iota>\<^sub>V(bvrident x)) \<theta>)) \<nu> = rtrm_sem (adjoint \<sigma> I (F(0))) \<theta> \<nu>" 
    using Uvariation_refl Uvariation_trans usubst_term sound_stat_sem by blast
  have l2r: "solves_ODE I F x (the (rusubst \<sigma> \<L> (U\<union>\<iota>\<^sub>V(bvrident x)) \<theta> )) \<Longrightarrow> solves_ODE (adjoint \<sigma> I \<omega>) F x \<theta>"
    using vaflow1 subdef same_ODE_same_sol Uvariation_trans usubst_term uv
    by (smt (verit, ccfv_threshold) Un_absorb Un_assoc assms(1) solves_ODE_def solves_Vagree_trans)
  have r2l: "solves_ODE (adjoint \<sigma> I \<omega>) F x \<theta> \<Longrightarrow> solves_ODE I F x (the (rusubst \<sigma> \<L> (U\<union>\<iota>\<^sub>V(bvrident x)) \<theta>))"
    using vaflow2 subdef same_ODE_same_sol Uvariation_trans usubst_term uv
    by (smt (verit, ccfv_threshold) Un_absorb Un_assoc assms(1) solves_ODE_def solves_Vagree_trans)
  from l2r and r2l show ?thesis by auto
qed

lemma usubst_ode_ext2:
  assumes sound_stat_sem: "is_sound_stat_sem \<L>"
  assumes subdef: "rusubst \<sigma> \<L> (U\<union>\<iota>\<^sub>V(bvrident x)) \<theta> \<noteq> undeft"
  assumes uv: "Uvariation (F(0)) \<omega> (U\<union>\<iota>\<^sub>V(bvrident x))"
  shows "solves_ODE I F x (the (rusubst \<sigma> \<L> (U\<union>\<iota>\<^sub>V(bvrident x)) \<theta>)) = solves_ODE (adjoint \<sigma> I \<omega>) F x \<theta>"
  using usubst_ode_ext sound_stat_sem subdef uv by blast 



paragraph \<open>Uniform Substitution Lemmas for Programs and Formulas\<close>

lemma usubst_fml_chp:
  assumes sound_stat: "is_sound_stat_sem \<L>"
  assumes wf_usubs: "wf_usubs \<L> \<sigma>"
  assumes vaouter: "Uvariation \<nu> \<omega> U"
  assumes bindrI: "J = \<pi>\<^sub>I I"
    shows "usubstf \<sigma> \<L> U \<phi>\<noteq>undeff \<Longrightarrow> wf_fml \<L> \<phi> \<Longrightarrow> (\<nu> \<in> fml_sem I (the(usubstf \<sigma> \<L> U \<phi>))) = (\<nu> \<in> fml_sem (adjoint \<sigma> I \<omega>) \<phi>)"
      and "snd(usubstp \<sigma> \<L> U \<alpha>)\<noteq>undefp \<Longrightarrow> wf_chp \<L> \<alpha> \<Longrightarrow> ((\<nu>, \<tau>, \<o>) \<in> chp_sem I (usubstpp \<sigma> \<L> U \<alpha>)) = ((\<nu>, \<tau>, \<o>) \<in> chp_sem (adjoint \<sigma> I \<omega>) \<alpha>)"
using sound_stat wf_usubs vaouter bindrI proof (induction \<phi> and \<alpha> arbitrary: I \<nu> \<omega> and I \<nu> \<tau> \<omega> \<o> rule: usubstfp_induct)
  case (GPsymb \<sigma> \<L> U b p Z \<Theta>)
  hence uvari: "Uvariation \<nu> \<omega> U" by blast

  let ?\<sigma>I = "adjoint \<sigma> I \<omega>"
  let ?\<sigma>Z = "vusubst (SBindrs \<sigma>) Z" 
  let ?\<sigma>\<Theta> = "the(alusubst \<sigma> \<L> U \<Theta>)"

  have argsdeft: "alusubst \<sigma> \<L> U \<Theta> \<noteq> undeft" using GPsymb.prems salusubst_undeft by fastforce+
  hence saldeft: "salusubst \<sigma> \<L> U Z \<Theta> = Aterm (?\<sigma>Z, ?\<sigma>\<Theta>)" using salusubst_simp by force

  have usspace: "vspace_sem (\<pi>\<^sub>I I) ?\<sigma>Z = vspace_sem (\<pi>\<^sub>I ?\<sigma>I) Z"
    using GPsymb.prems(3) vusubst_space GPsymb.prems(4) Bindrs_adjoint_commute by metis
  have usargs: "\<And>e. e \<in> set \<Theta> \<Longrightarrow> arg_sem I (the(ausubst \<sigma> \<L> U e)) \<nu> = arg_sem ?\<sigma>I e \<nu>"
    using GPsymb.prems(3) alusubst_conv argsdeft ausubst_term uvari GPsymb.prems(4) by blast

  show ?case
  proof (cases "SAllPsymbs \<sigma> b p")
    case None
    hence "fml_sem I (the(usubstf \<sigma> \<L> U (GPsymb b p Z \<Theta>))) = fml_sem I (GPsymb b p ?\<sigma>Z ?\<sigma>\<Theta>)"
      using saldeft by force
    then show ?thesis using usspace usargs None argsdeft usubst_arglist by auto
  next
    case (Some \<sigma>p)
    hence noclash: "((FNE\<^sub>\<L> \<L> (Efml \<sigma>p)) - FVN\<^sub>\<L> \<L> ?\<sigma>Z) \<inter> U = {}" 
      using GPsymb.prems(1) usubstf_gpsymb_conv by fastforce

    let ?\<sigma>\<^sub>0 = "dotsubst_vec ?\<sigma>\<Theta>"
    let ?X = "vspace_sem (\<pi>\<^sub>I (adjoint \<sigma> I \<nu>)) Z" 
    let ?d = "args_sem I ?\<sigma>\<Theta> \<nu>"

    have "VCagree \<nu> \<omega> (-U)" using GPsymb Uvariation_def by simp
    hence "VCagree \<nu> (lmerge \<nu> \<omega> ?X) (-U\<union>(\<iota>\<^sub>V ?X \<union> \<iota>\<^sub>C (\<pi>\<^sub>T ?X \<times> \<Omega>)))" using VCagree_lmerge by simp
    moreover have "FNE (\<pi>\<^sub>I (adjoint ?\<sigma>\<^sub>0 I \<nu>)) \<sigma>p \<subseteq> -U\<union>(\<iota>\<^sub>V ?X \<union> \<iota>\<^sub>C (\<pi>\<^sub>T ?X \<times> \<Omega>))"
    proof -
      have "FVN\<^sub>\<L> \<L> ?\<sigma>Z \<subseteq> \<iota>\<^sub>V ?X \<union> \<iota>\<^sub>C (\<pi>\<^sub>T ?X \<times> \<Omega>)"
        by (metis Bindrs_adjoint_commute CNV_def FNV_def FNV_sound_stat_sem FVV_def GPsymb(4) vusubst_space)
      moreover have "FNE\<^sub>\<L> \<L> (Efml \<sigma>p) \<subseteq> -U \<union> (FVN\<^sub>\<L> \<L> ?\<sigma>Z)" using noclash by auto      
      moreover have "FNE (\<pi>\<^sub>I (adjoint ?\<sigma>\<^sub>0 I \<nu>)) \<sigma>p \<subseteq> FNE\<^sub>\<L> \<L> (Efml \<sigma>p)" 
        using FNE_expr_sound_stat_sem GPsymb(4) by presburger
      ultimately show ?thesis by auto
    qed
    ultimately have agree: "VCagree \<nu> (lmerge \<nu> \<omega> ?X) (FNE (\<pi>\<^sub>I (adjoint ?\<sigma>\<^sub>0 I \<nu>)) \<sigma>p)"
      using VCagree_antimon by simp 

    have usubst_wf: "wf_fml \<L> \<sigma>p"
      using GPsymb(5) Some unfolding wf_usubs_def wf_folr_subs_def wf_fmlsubs_def
      apply (cases b)
      apply (metis SAllPsymbs_def SFOL\<^sub>RPsymbs_def option.case_eq_if option.distinct(1) option.sel)
      by (metis SAllPsymbs_def option.case_eq_if option.distinct(1) option.sel)

      (* unfold usubst definition *)
    have "\<nu> \<in> fml_sem I (the(usubstf \<sigma> \<L> U (GPsymb b p Z \<Theta>))) = (\<nu> \<in> fml_sem I (the(usubstf ?\<sigma>\<^sub>0 \<L> {} \<sigma>p)))" 
      using Some noclash saldeft by force
      (* apply IH on the dotsubst, which is smaller than \<sigma> as it only replaces dotsymbols *)
    also have "... = (\<nu> \<in> fml_sem (adjoint ?\<sigma>\<^sub>0 I \<nu>) \<sigma>p)"
      using GPsymb.IH GPsymb.prems Some noclash saldeft usubst_wf by simp
      (* transfer \<sigma>f from \<nu> to its U-variation \<omega> *)
    also have "... = ((lmerge \<nu> \<omega> ?X) \<in> fml_sem (adjoint ?\<sigma>\<^sub>0 I \<nu>) \<sigma>p)" 
      using agree coincidence_fml by blast
      (* evaluate adjoint of I under dotsubst \<sigma>\<^sub>0 *)
    also have "... = ((lmerge \<nu> \<omega> ?X) \<in> fml_sem (repc_vec I (dot_repl_vec ?d)) \<sigma>p)" 
      using dotsubst_adj_eq_dotted_interp by simp
      (* definition of adjoint *)
    also have "... = PInterp (AllPsymbs (adjoint \<sigma> I \<omega>) b p) ?X \<nu> ?d" 
      using Some is_pinterp_adjoint_gpsymbs fprdnl_def by simp 
      (* apply IH to the argument list \<Theta>, which is smaller than p(Z)(\<Theta>) *)
    also have "... = PInterp (AllPsymbs (adjoint \<sigma> I \<omega>) b p) ?X \<nu> (args_sem (adjoint \<sigma> I \<omega>) \<Theta> \<nu>)"
      using argsdeft usargs usubst_arglist by auto
      (* unfold the semantics of the predicate symbol p(Z)(\<Theta>) *)
    also have "... = (\<nu> \<in> fml_sem (adjoint \<sigma> I \<omega>) (GPsymb b p Z \<Theta>))" by auto
    finally show "\<nu> \<in> fml_sem I (the(usubstf \<sigma> \<L> U (GPsymb b p Z \<Theta>))) = (\<nu> \<in> fml_sem (adjoint \<sigma> I \<omega>) (GPsymb b p Z \<Theta>))" .
  qed
next
  case (Geq \<sigma> \<L> U \<theta> \<eta>)
  hence def1: "rusubst \<sigma> \<L> U \<theta> \<noteq> undeft" using usubstf_geq_conv by simp 
  moreover have def2: "rusubst \<sigma> \<L> U \<eta> \<noteq> undeft" using usubstf_geq_conv Geq.prems(1) by blast
  ultimately show ?case using rusubst_term[OF \<open>is_sound_stat_sem \<L>\<close>, OF \<open>Uvariation \<nu> \<omega> U\<close>, OF \<open>J = \<pi>\<^sub>I I\<close>, OF def1] 
      rusubst_term[OF \<open>is_sound_stat_sem \<L>\<close>, OF \<open>Uvariation \<nu> \<omega> U\<close>, OF \<open>J = \<pi>\<^sub>I I\<close>, OF def2] Geq(3) by auto
next
  case (Pref \<sigma> \<L> U te\<^sub>1 te\<^sub>2)
  hence def1: "tusubst \<sigma> \<L> U te\<^sub>1 \<noteq> undeft" using usubstf_pref_conv by simp 
  moreover have def2: "tusubst \<sigma> \<L> U te\<^sub>2 \<noteq> undeft" using usubstf_pref_conv Pref.prems(1) by blast
  ultimately show ?case using tusubst_term[OF \<open>is_sound_stat_sem \<L>\<close>, OF \<open>Uvariation \<nu> \<omega> U\<close>, OF \<open>J = \<pi>\<^sub>I I\<close>, OF def1] 
      tusubst_term[OF \<open>is_sound_stat_sem \<L>\<close>, OF \<open>Uvariation \<nu> \<omega> U\<close>, OF \<open>J = \<pi>\<^sub>I I\<close>, OF def2] by auto
next
  case (Not \<sigma> \<L> U \<phi>)
  have "(\<nu> \<in> fml_sem I (the(usubstf \<sigma> \<L> U (! \<phi>)))) = (\<nu> \<notin> fml_sem I (the(usubstf \<sigma> \<L> U \<phi>)))"
    using Not.prems(1) Noto_undef Unaryo.elims by auto
  also have "... = (\<nu> \<in> fml_sem (adjoint \<sigma> I \<omega>) (! \<phi>))" using Not.IH Not.prems Noto_undef by auto
  finally show ?case .
next
  case (And \<sigma> \<L> U \<phi> \<psi>)
  have "(\<nu> \<in> fml_sem I (the(usubstf \<sigma> \<L> U (\<phi> && \<psi>)))) 
    = (\<nu> \<in> fml_sem I (the(usubstf \<sigma> \<L> U \<phi>)) \<and> (\<nu> \<in> fml_sem I (the(usubstf \<sigma> \<L> U \<psi>))))"
    using And.prems(1) Ando_undef Binaryo.elims by auto
  also have "... = ((\<nu> \<in> fml_sem (adjoint \<sigma> I \<omega>) \<phi>) \<and> (\<nu> \<in> fml_sem (adjoint \<sigma> I \<omega>) \<psi>))"
    using And.IH And.prems by fastforce
  also have "... = (\<nu> \<in> fml_sem (adjoint \<sigma> I \<omega>) (\<phi> && \<psi>))" by simp
  finally show ?case .
next
  case (Exists \<sigma> \<L> U z \<phi>)
  hence uvari: "\<And>d. sorteq z d \<longrightarrow> Uvariation (upds \<nu> z d) \<omega> (U \<union> {Bv z})" 
    using Uvariation_upds by presburger
  hence deft: "usubstf \<sigma> \<L> (U\<union>{Bv z}) \<phi> \<noteq> undeff" using Exists by (simp add: Existso_undef)

  have "\<nu> \<in> fml_sem I (the (usubstf \<sigma> \<L> U (Exists z \<phi>)))
    = (\<nu> \<in> fml_sem I (Exists z (the(usubstf \<sigma> \<L> (U\<union>{Bv z}) \<phi>))))" using deft by force
  also have "... = (\<exists>d. sorteq z d \<and> upds \<nu> z d \<in> fml_sem I (the(usubstf \<sigma> \<L> (U\<union>{Bv z}) \<phi>)))" 
    by (simp add: fml_sem.simps(6))
  also have "... = (\<exists>d. sorteq z d \<and> upds \<nu> z d \<in> fml_sem (adjoint \<sigma> I \<omega>) \<phi>)" 
    using uvari Exists.IH Exists.prems deft wf_fml.simps(6) by blast
  also have "... = (\<nu> \<in> fml_sem (adjoint \<sigma> I \<omega>) (Exists z \<phi>))" by (simp add: fml_sem.simps(6))
  finally show "\<nu> \<in> fml_sem I (the (usubstf \<sigma> \<L> U (Exists z \<phi>))) 
    = (\<nu> \<in> fml_sem (adjoint \<sigma> I \<omega>) (Exists z \<phi>))" .
next
  case (Box \<sigma> \<L> U \<alpha> \<psi>)
  let  ?\<sigma>\<alpha> = "usubstpp \<sigma> \<L> U \<alpha>"
  let ?Z = "fst(usubstp \<sigma> \<L> U \<alpha>)"
  let ?\<sigma>\<psi> = "the(usubstf \<sigma> \<L> ?Z \<psi>)"
  let ?\<sigma>I = "adjoint \<sigma> I \<omega>"

  have defp: "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp" and deff: "usubstf \<sigma> \<L> ?Z \<psi> \<noteq> undeff"
    using Box.prems(1) Boxo_undef by auto

  have "\<forall>\<tau> \<o>. (\<nu>, \<tau>, Fin \<o>) \<in> chp_sem I ?\<sigma>\<alpha> \<longrightarrow> Uvariation (\<o> @@ \<tau>) \<omega> ?Z"
    using Box.prems(3) defp uvari_fin_state by (simp add: Box.prems(5))
  hence pvari: "\<forall>\<tau> \<o>. (\<nu>, \<tau>, Fin \<o>) \<in> chp_sem ?\<sigma>I \<alpha> \<longrightarrow> Uvariation (\<o> @@ \<tau>) \<omega> ?Z"
    using Box.IH(1) Box.prems defp by auto

  have "(\<nu> \<in> fml_sem I (the(usubstf \<sigma> \<L> U ([[ \<alpha> ]] \<psi>)))) = (\<nu> \<in> fml_sem I ([[ ?\<sigma>\<alpha> ]] ?\<sigma>\<psi>))" using deff defp by force
  also have "... = (\<forall>\<tau> \<o>. (\<nu>, \<tau>, Fin \<o>) \<in> chp_sem I ?\<sigma>\<alpha> \<longrightarrow> \<o> @@ \<tau> \<in> fml_sem I ?\<sigma>\<psi>)" by simp
  also have "... = (\<forall>\<tau> \<o>. (\<nu>, \<tau>, Fin \<o>) \<in> chp_sem ?\<sigma>I \<alpha> \<longrightarrow> \<o> @@ \<tau> \<in> fml_sem I ?\<sigma>\<psi>)"
    using Box.IH(1) Box.prems defp wf_fml.simps(8) by simp
  also have "... = (\<forall>\<tau> \<o>. (\<nu>, \<tau>, Fin \<o>) \<in> chp_sem ?\<sigma>I \<alpha> \<longrightarrow> \<o> @@ \<tau> \<in> fml_sem ?\<sigma>I \<psi>)"
    using Box.IH(2) Box.prems deff pvari wf_fml.simps(7) by blast
  also have "... = (\<nu> \<in> fml_sem ?\<sigma>I ([[ \<alpha> ]] \<psi>))" by simp
  finally show ?case .
next
  case (AcBox \<sigma> \<L> U \<alpha> A C \<psi>)
  let  ?\<sigma>\<alpha> = "usubstpp \<sigma> \<L> U \<alpha>"
  let ?Z = "fst(usubstp \<sigma> \<L> U \<alpha>)"
  let ?\<sigma>A = "the(usubstf \<sigma> \<L> ?Z A)"
  let ?\<sigma>C = "the(usubstf \<sigma> \<L> ?Z C)"
  let ?\<sigma>\<psi> = "the(usubstf \<sigma> \<L> ?Z \<psi>)"
  let ?\<sigma>I = "adjoint \<sigma> I \<omega>"

  have defp: "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp" and adeff: "usubstf \<sigma> \<L> ?Z A \<noteq> undeff"
    and cdeff: "usubstf \<sigma> \<L> ?Z C \<noteq> undeff" and deff: "usubstf \<sigma> \<L> ?Z \<psi> \<noteq> undeff"
    using AcBox.prems(1) AcBoxo_undef by auto

  hence acvari: "\<forall>\<tau> \<o> \<tau>'. (\<nu>, \<tau>, \<o>) \<in> chp_sem ?\<sigma>I \<alpha> \<longrightarrow> \<tau>' \<preceq> \<tau> \<longrightarrow> Uvariation (\<nu> @@ \<tau>') \<omega> ?Z" 
    using AcBox.IH(1) AcBox.prems transfer_uvari_over_run2 wf_fml.simps(9) by fastforce
  
  have pvari: "\<forall>\<tau> \<o>. (\<nu>, \<tau>, Fin \<o>) \<in> chp_sem I ?\<sigma>\<alpha> \<longrightarrow> Uvariation (\<o> @@ \<tau>) \<omega> ?Z" 
    using AcBox.prems defp uvari_fin_state by auto
  hence pvari: "\<forall>\<tau> \<o>. (\<nu>, \<tau>, Fin \<o>) \<in> chp_sem ?\<sigma>I \<alpha> \<longrightarrow> Uvariation (\<o> @@ \<tau>) \<omega> ?Z"
    using AcBox.IH(1) AcBox.prems defp by auto

  have "\<forall>rel. prefrel rel \<longrightarrow> (\<forall>\<tau> \<o>. (\<nu>, \<tau>, \<o>) \<in> chp_sem ?\<sigma>I \<alpha>
    \<longrightarrow> (\<forall>\<tau>'. rel \<tau>' \<tau> \<longrightarrow> (\<nu> @@ \<tau>' \<in> fml_sem I ?\<sigma>A) = (\<nu> @@ \<tau>' \<in> fml_sem ?\<sigma>I A)))"
    using AcBox.IH(2) AcBox.prems acvari adeff wf_fml.simps(5) by auto
  hence usA: "\<forall>rel. prefrel rel \<longrightarrow> (\<forall>\<tau> \<o>. (\<nu>, \<tau>, \<o>) \<in> chp_sem ?\<sigma>I \<alpha> 
    \<longrightarrow> (g_assm_set rel \<nu> \<tau> \<subseteq> fml_sem I ?\<sigma>A) = (g_assm_set rel \<nu> \<tau> \<subseteq> fml_sem ?\<sigma>I A))"
    unfolding g_assm_set_def by blast

  have usC: "\<forall>\<tau> \<o>. (\<nu>, \<tau>, \<o>) \<in> chp_sem ?\<sigma>I \<alpha> \<longrightarrow> ((\<nu> @@ \<tau>) \<in> fml_sem I ?\<sigma>C) = ((\<nu> @@ \<tau>) \<in> fml_sem ?\<sigma>I C)"
    using AcBox.IH(3) AcBox.prems acvari cdeff by auto
  have usP: "\<forall>\<tau> \<o>. (\<nu>, \<tau>, \<o>) \<in> chp_sem ?\<sigma>I \<alpha> \<longrightarrow> \<o> \<noteq> NonFin \<longrightarrow> ((gets \<o>) @@ \<tau> \<in> fml_sem I ?\<sigma>\<psi>) = ((gets \<o>) @@ \<tau> \<in> fml_sem ?\<sigma>I \<psi>)"
    using AcBox.IH(4) AcBox.prems deff pvari by auto

  have  "(\<nu> \<in> fml_sem I (the(usubstf \<sigma> \<L> U (AcBox \<alpha> A C \<psi>)))) 
      = (\<nu> \<in> fml_sem I (AcBox ?\<sigma>\<alpha> ?\<sigma>A ?\<sigma>C ?\<sigma>\<psi>))" using adeff cdeff deff defp by force
  also have "... = (\<forall>\<tau> \<o>. (\<nu>, \<tau>, \<o>) \<in> chp_sem I ?\<sigma>\<alpha>
        \<longrightarrow> (strict_assm_set \<nu> \<tau> \<subseteq> fml_sem I ?\<sigma>A \<longrightarrow> \<nu> @@ \<tau> \<in> fml_sem I ?\<sigma>C)
            \<and> (\<o> \<noteq> NonFin \<and> assm_set \<nu> \<tau> \<subseteq> fml_sem I ?\<sigma>A \<longrightarrow> (gets \<o>) @@ \<tau> \<in> fml_sem I ?\<sigma>\<psi>))" by simp
  also have "... = (\<forall>\<tau> \<o>. (\<nu>, \<tau>, \<o>) \<in> chp_sem ?\<sigma>I \<alpha>
        \<longrightarrow> (strict_assm_set \<nu> \<tau> \<subseteq> fml_sem I ?\<sigma>A \<longrightarrow> \<nu> @@ \<tau> \<in> fml_sem I ?\<sigma>C)
            \<and> (\<o> \<noteq> NonFin \<and> assm_set \<nu> \<tau> \<subseteq> fml_sem I ?\<sigma>A \<longrightarrow> (gets \<o>) @@ \<tau> \<in> fml_sem I ?\<sigma>\<psi>))"
    using AcBox.IH(1) AcBox.prems defp wf_fml.simps(5) by simp
  also have "... = (\<forall>\<tau> \<o>. (\<nu>, \<tau>, \<o>) \<in> chp_sem ?\<sigma>I \<alpha>
        \<longrightarrow> (strict_assm_set \<nu> \<tau> \<subseteq> fml_sem ?\<sigma>I A \<longrightarrow> \<nu> @@ \<tau> \<in> fml_sem ?\<sigma>I C)
            \<and> (\<o> \<noteq> NonFin \<and> assm_set \<nu> \<tau> \<subseteq> fml_sem ?\<sigma>I A \<longrightarrow> (gets \<o>) @@ \<tau> \<in> fml_sem ?\<sigma>I \<psi>))"
    using usA usC usP by metis
  also have "... = (\<nu> \<in> fml_sem ?\<sigma>I (AcBox \<alpha> A C \<psi>))" by simp
  finally show ?case .
next
  case (ChanIn \<sigma> \<L> U ch Y)
  hence def: "rusubst \<sigma> \<L> U ch \<noteq> undeft" using usubstf_chan_in_conv by simp
  hence "rtrm_sem I (the (rusubst \<sigma> \<L> U ch)) \<nu> = rtrm_sem (adjoint \<sigma> I \<omega>) ch \<nu>"   
    using ChanIn(3,5) rusubst_term by blast
  then show ?case using def usubst_cspace by auto
next
  case (Chp \<sigma> \<L> U a Z Y)
  then show ?case
  proof (cases "(SChps0 \<sigma>) a")
    case None
    then show ?thesis using Chp.prems(4) Chps_fail vusubst_space usubst_cspace usubstchp_def by force
  next
    case (Some \<sigma>a)
    
    let ?\<sigma>Z = "vusubst (SBindrs \<sigma>) Z"
    let ?\<sigma>Y = "cusubst (SBindrs \<sigma>) Y"

    have "wf_chp \<L> \<sigma>a" using Chp Some unfolding wf_usubs_def wf_chpsubs_def by (metis option.case(2))
    hence deno: "is_denotation (chp_sem I \<sigma>a)" using chp_sem_is_denotation by simp

    have noclash: "concrete_cspace ?\<sigma>Y \<and> CN\<^sub>P \<sigma>a = UCN\<^sub>C ?\<sigma>Y \<and> BVP\<^sub>\<L> \<L> \<sigma>a \<subseteq> UAV\<^sub>\<L> \<L> ?\<sigma>Z \<and> FVP\<^sub>\<L> \<L> \<sigma>a \<subseteq> UAV\<^sub>\<L> \<L> ?\<sigma>Z"
      using usubstapp_chp_conv Chp(1) Some by fastforce

    have BVD: "BVD (chp_sem I \<sigma>a) \<subseteq> vspace_sem (\<pi>\<^sub>I I) ?\<sigma>Z"
      using noclash Chp(3) UAV\<^sub>\<L>_sound_stat_sem BVP_sound_stat_sem FVV_def BVP_BVD by blast

    moreover have "CND (chp_sem I \<sigma>a) \<subseteq> \<pi>\<^sub>T (vspace_sem (\<pi>\<^sub>I I) ?\<sigma>Z) \<times> cspace_sem (\<pi>\<^sub>I I) ?\<sigma>Y"
    proof - 
      have eqCN: "CN\<^sub>P \<sigma>a = cspace_sem (\<pi>\<^sub>I I) ?\<sigma>Y" 
        using CN\<^sub>C_concrete_cspace noclash by simp

      have "CNP (\<pi>\<^sub>I I) \<sigma>a \<subseteq> TCN\<^sub>P \<sigma>a" by (simp add: Computable_Static_Semantics.CNP_overapprox)
      hence "CNP (\<pi>\<^sub>I I) \<sigma>a \<subseteq> UNIV \<times> CN\<^sub>P \<sigma>a" using TCN\<^sub>P_overapprox_CN\<^sub>P by blast
      hence flat_over: "flatten_comtar (CND (chp_sem I \<sigma>a)) \<subseteq> CN\<^sub>P \<sigma>a" 
        using CNP_CND by auto
      hence "Domain (CND (chp_sem I \<sigma>a)) \<subseteq> \<pi>\<^sub>T (vspace_sem (\<pi>\<^sub>I I) ?\<sigma>Z)"
        using Domain_CND_tvars_BVD DiffD_chp_sem BVD by fastforce 

      moreover have "flatten_comtar (CND (chp_sem I \<sigma>a)) \<subseteq> cspace_sem (\<pi>\<^sub>I I) ?\<sigma>Y"
        using eqCN flat_over by simp
      ultimately show "CND (chp_sem I \<sigma>a) \<subseteq> \<pi>\<^sub>T (vspace_sem (\<pi>\<^sub>I I) ?\<sigma>Z) \<times> cspace_sem (\<pi>\<^sub>I I) ?\<sigma>Y"
        by auto  
    qed

    ultimately have beffect: "bound_effect (chp_sem I \<sigma>a) (chpspace_sem (\<pi>\<^sub>I I) ?\<sigma>Z ?\<sigma>Y)"
      unfolding bound_effect_def using DiffD_chp_sem BND_partition iota_vars_comtar_mono by simp

    moreover have FVD: "FVD (chp_sem I \<sigma>a) \<subseteq> vspace_sem (\<pi>\<^sub>I I) ?\<sigma>Z"
      using noclash Chp(3) UAV\<^sub>\<L>_sound_stat_sem FVP_sound_stat_sem FVV_def FVP_FVD by blast

    have "sound_chp_subst I \<sigma>a (vspace_sem (\<pi>\<^sub>I I) ?\<sigma>Z) (cspace_sem (\<pi>\<^sub>I I) ?\<sigma>Y)"
      unfolding sound_chp_subst_def using deno beffect FVD by simp

    hence "(Chps (adjoint \<sigma> I \<omega>)) a (vspace_sem (\<pi>\<^sub>I I) ?\<sigma>Z) (cspace_sem (\<pi>\<^sub>I I) ?\<sigma>Y) = chp_sem I \<sigma>a"
      using Some Chps_match by simp
    moreover have "usubstpp \<sigma> \<L> U (Chp a Z Y) = \<sigma>a"
      by (metis Chp(1) Some option.distinct(1) option.sel snd_conv usubstapp_chp_conv usubstp_chp)
    ultimately show ?thesis using vusubst_space usubst_cspace by simp
  qed
next
  case (Assign \<sigma> \<L> U x \<theta>)
  hence deft: "rusubst \<sigma> \<L> U \<theta> \<noteq> undeft" by (simp add: Assigno_undef)
  show ?case
  proof (cases \<o>)
    case (Fin \<o>)
    have "(\<nu>, \<tau>, Fin \<o>) \<in> chp_sem I (the (snd (usubstp \<sigma> \<L> U (x := \<theta>))))
      = ((\<nu>, \<tau>, Fin \<o>) \<in> chp_sem I (x := (the(rusubst \<sigma> \<L> U \<theta>))))" using deft by auto
    also have "...  = (\<tau> = [] \<and> \<o> = rrepv \<nu> x (rtrm_sem I (the(rusubst \<sigma> \<L> U \<theta>)) \<nu>))" by simp
    also have "... = (\<tau> = [] \<and> \<o> = rrepv \<nu> x (rtrm_sem (adjoint \<sigma> I \<omega>) \<theta> \<nu>))"
      using Assign.prems deft rusubst_term by simp
    also have "... = ((\<nu>, \<tau>, Fin \<o>) \<in> chp_sem (adjoint \<sigma> I \<omega>) (x := \<theta>))" by simp
    finally have "(\<nu>, \<tau>, Fin \<o>) \<in> chp_sem I (the (snd (usubstp \<sigma> \<L> U (x := \<theta>))))
      = ((\<nu>, \<tau>, Fin \<o>) \<in> chp_sem (adjoint \<sigma> I \<omega>) (x := \<theta>))" .
    then show ?thesis using Fin by auto
  next
    case NonFin
    then show ?thesis using CN.simps(2) chp_sem_least_computations deft by fastforce
  qed
next
  case (Nondet \<sigma> \<L> U x)
  show ?case by auto (* way easier than assign since there is no recursive substitution *)
next
  case (Test \<sigma> \<L> U \<phi>)
  hence deft: "usubstf \<sigma> \<L> U \<phi> \<noteq> undeff" by (simp add: Testo_undef)
  show ?case
  proof (cases \<o>)
    case (Fin \<o>)
    have "(\<nu>, \<tau>, Fin \<o>) \<in> chp_sem I (the (snd (usubstp \<sigma> \<L> U (Test \<phi>))))
      = ((\<nu>, \<tau>, Fin \<o>) \<in> chp_sem I (Test (the(usubstf \<sigma> \<L> U \<phi>))))" using deft by auto
    also have "...  = (\<tau> = [] \<and> \<o> = \<nu> \<and> \<nu> \<in> (fml_sem I (the(usubstf \<sigma> \<L> U \<phi>))))" by auto
    also have "...  = (\<tau> = [] \<and> \<o> = \<nu> \<and> \<nu> \<in> (fml_sem (adjoint \<sigma> I \<omega>) \<phi>))"
      using Test.IH Test.prems deft FOL\<^sub>R_is_wf_fml by fastforce
    also have "... = ((\<nu>, \<tau>, Fin \<o>) \<in> chp_sem (adjoint \<sigma> I \<omega>) (Test \<phi>))" by auto
    finally have "(\<nu>, \<tau>, Fin \<o>) \<in> chp_sem I (the (snd (usubstp \<sigma> \<L> U (Test \<phi>))))
      = ((\<nu>, \<tau>, Fin \<o>) \<in> chp_sem (adjoint \<sigma> I \<omega>) (Test \<phi>))" .
    then show ?thesis using Fin by auto
  next
    case NonFin
    then show ?thesis using CN.simps(4) chp_sem_least_computations deft by force
  qed
next
  case (Evolution \<sigma> \<L> U x \<theta> \<phi>)
  hence deft: "rusubst \<sigma> \<L> (U\<union>\<iota>\<^sub>V(bvrident x)) \<theta> \<noteq> undeft" "usubstf \<sigma> \<L> (U\<union>\<iota>\<^sub>V(bvrident x)) \<phi> \<noteq> undeff" 
    by (auto simp add: Evolutiono_undef)
                  
  have wf_rtrm: "wf_rtrm \<theta>" using Evolution QRpolynom_is_wf_rtrm by simp
  have wf_fml: "wf_fml \<L> \<phi>" using Evolution FOL\<^sub>R_is_wf_fml by fastforce

  let ?\<sigma>\<theta> = "the(rusubst \<sigma> \<L> (U\<union>\<iota>\<^sub>V(bvrident x)) \<theta>)"
  let ?\<sigma>\<phi> = "the(usubstf \<sigma> \<L> (U\<union>\<iota>\<^sub>V(bvrident x)) \<phi>)"

  show ?case
  proof (cases \<o>)
    case (Fin \<o>)
    have "(\<nu>, \<tau>, Fin \<o>) \<in> chp_sem I (the (snd (usubstp \<sigma> \<L> U (Evolution x \<theta> \<phi>))))
      = ((\<nu>, \<tau>, Fin \<o>) \<in> chp_sem I (Evolution x ?\<sigma>\<theta> ?\<sigma>\<phi>))" 
      using deft by force
    also have "...  = (\<tau> = [] \<and> (\<exists>F T. Vagree \<nu> (F(0)) (-{Rv (DVarName x)}) \<and> F(T) = \<o> 
      \<and> solves_ODE I F x ?\<sigma>\<theta> \<and> (\<forall>\<zeta>. F(\<zeta>) \<in> fml_sem I ?\<sigma>\<phi>)))" by simp
    also have "...  = (\<tau> = [] \<and> (\<exists>F T. Vagree \<nu> (F(0)) (-{Rv (DVarName x)}) \<and> F(T) = \<o> 
      \<and> solves_ODE I F x ?\<sigma>\<theta> \<and> (\<forall>\<zeta>. F(\<zeta>) \<in> fml_sem (adjoint \<sigma> I \<omega>) \<phi>)))"
      using Evolution deft wf_fml Uvariation_solves_ODE by metis
    also have "...  = (\<tau> = [] \<and> (\<exists>F T. Vagree \<nu> (F(0)) (-{Rv (DVarName x)}) \<and> F(T) = \<o> 
      \<and> solves_ODE (adjoint \<sigma> I \<omega>) F x \<theta> \<and> (\<forall>\<zeta>. F(\<zeta>) \<in> fml_sem (adjoint \<sigma> I \<omega>) \<phi>)))"
      using Evolution(4,6) Uvariation_solves_ODE deft usubst_ode_ext2 by blast
    also have "...  = ((\<nu>, \<tau>, Fin \<o>) \<in> chp_sem (adjoint \<sigma> I \<omega>) (Evolution x \<theta> \<phi> ))" by simp
    finally have "(\<nu>, \<tau>, Fin \<o>) \<in> chp_sem I (the (snd (usubstp \<sigma> \<L> U (Evolution x \<theta> \<phi>)))) 
      = ((\<nu>, \<tau>, Fin \<o>) \<in> chp_sem (adjoint \<sigma> I \<omega>) (Evolution x \<theta> \<phi> ))" by simp
    then show ?thesis using Fin by blast
  next
    case NonFin
    then show ?thesis using CN.simps(2) chp_sem_least_computations deft by fastforce
  qed
next
  case (Choice \<sigma> \<L> U \<alpha> \<beta>)
  hence "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp" and "snd(usubstp \<sigma> \<L> U \<beta>) \<noteq> undefp"
    using usubstp_choice_conv by auto
  then show ?case using Choice.IH Choice.prems by fastforce
next                                              
  case (Compose \<sigma> \<L> U \<alpha> \<beta>)
  then show ?case using usubst_chp_compose by simp
next                                   
  case (Loop \<sigma> \<L> U \<alpha>)    
  let ?V = "fst(usubstp \<sigma> \<L> U \<alpha>)"
  have Vdef: "snd(usubstp \<sigma> \<L> ?V \<alpha>) \<noteq> undefp" using Loop.prems(1) usubstp_loop_conv by presburger
  moreover have taboomon: "?V \<supseteq> U" using usubst_taboo_pre_fp by presburger
  ultimately have Udef: "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp"
    using usubstp_antimon by blast
  
  hence uvari: "Uvariation \<nu> \<omega> ?V" by (meson taboomon Compl_iff Loop.prems Uvariation_def VCagree_antimon in_mono subsetI)
  
  let ?\<sigma>I = "adjoint \<sigma> I \<omega>"
 
  have "\<And>n. (\<nu>, \<tau>, \<o>) \<in> chp_sem I (usubstpp \<sigma> \<L> ?V (Repeat \<alpha> n))
    = ((\<nu>, \<tau>, \<o>) \<in> chp_sem ?\<sigma>I (Repeat \<alpha> n))"
  proof - 
    fix n
    have "Uvariation \<nu> \<omega> ?V \<Longrightarrow> ((\<nu>, \<tau>, \<o>) \<in> chp_sem I (usubstpp \<sigma> \<L> ?V (Repeat \<alpha> n))
      = ((\<nu>, \<tau>, \<o>) \<in> chp_sem ?\<sigma>I (Repeat \<alpha> n)))"
    proof (induction n arbitrary: \<nu> \<tau> \<o>)
      case 0
      then show ?case using usubstpp_test_TT by auto
    next
      case (Suc n)       
      hence RepeatIH: "usubstIH \<sigma> \<L> I (fst(usubstp \<sigma> \<L> ?V \<alpha>)) (Repeat \<alpha> n) \<omega>" 
        using Loop.prems Vdef output_taboo_fp by auto
      have alphaIH: "usubstIH \<sigma> \<L> I ?V \<alpha> \<omega>" using Loop.IH(2) Loop.prems by simp
           
      have deft: "snd(usubstp \<sigma> \<L> ?V (\<alpha> ;; (Repeat \<alpha> n))) \<noteq> undefp"
        by (simp add: Composeo_undef Vdef output_taboo_fp usubstp_Repeat_conv)

      have "(\<nu>, \<tau>, \<o>) \<in> chp_sem I (usubstpp \<sigma> \<L> ?V (Repeat \<alpha> (Suc n)))
        = ((\<nu>, \<tau>, \<o>) \<in> chp_sem I (usubstpp \<sigma> \<L> ?V (\<alpha> ;; (Repeat \<alpha> n))))" by auto
      also have "... = ((\<nu>, \<tau>, \<o>) \<in> chp_sem ?\<sigma>I (\<alpha> ;; (Repeat \<alpha> n)))" 
        using alphaIH RepeatIH deft Loop.prems usubst_chp_compose Suc.prems by blast
      also have "... = ((\<nu>, \<tau>, \<o>) \<in> chp_sem ?\<sigma>I (Repeat \<alpha> (Suc n)))" by auto
      finally show "(\<nu>, \<tau>, \<o>) \<in> chp_sem I (usubstpp \<sigma> \<L> ?V (Repeat \<alpha> (Suc n))) 
        = ((\<nu>, \<tau>, \<o>) \<in> chp_sem (adjoint \<sigma> I \<omega>) (Repeat \<alpha> (Suc n)))" .
    qed
    thus "(\<nu>, \<tau>, \<o>) \<in> chp_sem I (usubstpp \<sigma> \<L> ?V (Repeat \<alpha> n))
      = ((\<nu>, \<tau>, \<o>) \<in> chp_sem ?\<sigma>I (Repeat \<alpha> n))" using uvari by blast
  qed  
  hence  "\<And>n. (\<nu>, \<tau>, \<o>) \<in> chp_sem I (Repeat (usubstpp \<sigma> \<L> ?V \<alpha>) n)
    = ((\<nu>, \<tau>, \<o>) \<in> chp_sem ?\<sigma>I (Repeat \<alpha> n))"
    by (simp add: Vdef output_taboo_fp usubstp_Repeat)
  hence "(\<nu>, \<tau>, \<o>) \<in> rtcl_linhis (chp_sem I (usubstpp \<sigma> \<L> ?V \<alpha>))
    = ((\<nu>, \<tau>, \<o>) \<in> rtcl_linhis (chp_sem ?\<sigma>I \<alpha>))" by (simp add: chp_sem_Repeat linhis_rtcl_eq_iteration)
  moreover have "usubstpp \<sigma> \<L> U (Loop \<alpha>) = Loop (usubstpp \<sigma> \<L> ?V \<alpha>)" using Vdef by fastforce
  ultimately show ?case using chp_sem.simps(8) by presburger
next
  case (Send \<sigma> \<L> U ch h \<theta>)

  let ?\<sigma>\<alpha> = "usubstpp \<sigma> \<L> U (Send ch h \<theta>)"
  let ?\<sigma>\<theta> = "the(rusubst \<sigma> \<L> U \<theta>)"
  let ?\<sigma>I = "adjoint \<sigma> I \<omega>"

  have siga: "?\<sigma>\<alpha> = Send ch h ?\<sigma>\<theta>" using Send.prems(1) Unaryo.elims by force

  have  "((\<nu>, \<tau>, \<o>) \<in> chp_sem I ?\<sigma>\<alpha>) = ((\<tau>, \<o>) \<sqsubseteq> ([mkrecevent h ch (rtrm_sem I ?\<sigma>\<theta> \<nu>) (rval (\<nu> $$ (Rv \<mu>)))], Fin \<nu>))"
    using siga by auto
  also have "... = ((\<tau>, \<o>) \<sqsubseteq> ([mkrecevent h ch (rtrm_sem ?\<sigma>I \<theta> \<nu>) (rval (\<nu> $$ (Rv \<mu>)))], Fin \<nu>))" 
    using Send Sendo_undef usubst_term(1) by auto
  also have "... = ((\<nu>, \<tau>, \<o>) \<in> chp_sem ?\<sigma>I (Send ch h \<theta>))" by simp
  finally show "((\<nu>, \<tau>, \<o>) \<in> chp_sem I ?\<sigma>\<alpha>) = ((\<nu>, \<tau>, \<o>) \<in> chp_sem ?\<sigma>I (Send ch h \<theta>))" .
next
  case (Receive \<sigma> \<L> U ch h x)
  then show ?case by simp (* easier than send since there is no usubst on a subterm *)
next
  case (Par \<sigma> \<L> U \<alpha> \<beta>)
  hence adefp: "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp" and bundef: "snd(usubstp \<sigma> \<L> U \<beta>) \<noteq> undefp" 
    using usubstp_par_conv by blast+

  let ?\<sigma>\<alpha> = "usubstpp \<sigma> \<L> U \<alpha>"
  let ?\<sigma>\<beta> = "usubstpp \<sigma> \<L> U \<beta>"
  let ?\<sigma>I = "adjoint \<sigma> I \<omega>"
  let ?\<sigma>J = "\<lambda>J. badjoint (SBindrs \<sigma>) J"

  have usubst_BVP: "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp \<Longrightarrow> BVP (\<pi>\<^sub>I I) ?\<sigma>\<alpha> \<subseteq> BVP (?\<sigma>J (\<pi>\<^sub>I I)) \<alpha>"
  proof
    fix z
    assume defp: "snd(usubstp \<sigma> \<L> U \<alpha>) \<noteq> undefp"
    assume 0: "z \<in> BVP (\<pi>\<^sub>I I) ?\<sigma>\<alpha>"
    then obtain I\<^sub>0 \<nu> \<tau> \<o> where eqJ: "\<pi>\<^sub>I I = \<pi>\<^sub>I I\<^sub>0" and "(\<nu>, \<tau>, \<o>) \<in> chp_sem I\<^sub>0 (usubstpp \<sigma> \<L> U \<alpha>)"
      and neq: "((\<o> \<squnion> \<nu>) @@ \<tau>) $$ z \<noteq> \<nu> $$ z" using BVP_def Par.prems by auto
    hence "(\<nu>, \<tau>, \<o>) \<in> chp_sem (adjoint \<sigma> I\<^sub>0 \<nu>) \<alpha>" 
      using Par.IH(1) Par.prems Uvariation_refl adefp wf_chp.simps(11) by blast
    moreover have "\<pi>\<^sub>I (adjoint \<sigma> I\<^sub>0 \<nu>) = \<pi>\<^sub>I (adjoint \<sigma> I \<nu>)" by (simp add: eqJ)
    ultimately have "z \<in> BVP (\<pi>\<^sub>I (adjoint \<sigma> I \<nu>)) \<alpha>" by (metis BVP_elem neq)
    thus "z \<in> BVP (?\<sigma>J (\<pi>\<^sub>I I)) \<alpha>" by simp
  qed

  have merge: "\<And>\<o>\<^sub>\<alpha> \<o>\<^sub>\<beta>. (\<nu>, \<tau> \<down> (CN J ?\<sigma>\<alpha>), Fin \<o>\<^sub>\<alpha>) \<in> chp_sem I ?\<sigma>\<alpha> \<and> (\<nu>, \<tau> \<down> (CN J ?\<sigma>\<beta>), Fin \<o>\<^sub>\<beta>) \<in> chp_sem I ?\<sigma>\<beta>
    \<and> Vagree \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> \<V>\<^sub>\<mu> \<longrightarrow> lmerge \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP J ?\<sigma>\<alpha>) = lmerge \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP (?\<sigma>J J) \<alpha>)"
  proof
    fix \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta>
    assume runs: "(\<nu>, \<tau> \<down> (CN J ?\<sigma>\<alpha>), Fin \<o>\<^sub>\<alpha>) \<in> chp_sem I ?\<sigma>\<alpha> \<and> (\<nu>, \<tau> \<down> (CN J ?\<sigma>\<beta>), Fin \<o>\<^sub>\<beta>) \<in> chp_sem I ?\<sigma>\<beta> \<and> Vagree \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> \<V>\<^sub>\<mu>"
    hence adjbeta: "(\<nu>, \<tau> \<down> (CN J ?\<sigma>\<beta>), Fin \<o>\<^sub>\<beta>) \<in> chp_sem ?\<sigma>I \<beta>" 
      using Par.IH(2) Par.prems bundef by simp

    let ?V = "BVP J ?\<sigma>\<alpha> \<union> -BVP (?\<sigma>J J) \<alpha>"
    let ?X = "{ z. \<nu> $$ z \<noteq> \<o>\<^sub>\<alpha> $$ z \<or> \<nu> $$ z \<noteq> \<o>\<^sub>\<beta> $$ z }"

    have "Vagree (lmerge \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP J ?\<sigma>\<alpha>)) (lmerge \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP (?\<sigma>J J) \<alpha>)) \<V>\<^sub>\<mu>"
      using Vagree_def lmerge_access runs by presburger
    moreover have "Vagree (lmerge \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP J ?\<sigma>\<alpha>)) (lmerge \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP (?\<sigma>J J) \<alpha>)) (-?V \<inter> ?X \<inter> -\<V>\<^sub>\<mu>)"
    unfolding Vagree_def proof (rule, rule)
      fix z (* case leads to a contradiction; z must not be in -?V \<inter> ?X unless in \<V>\<^sub>\<mu> *)
      assume 0: "z \<in> -?V \<inter> ?X \<inter> -\<V>\<^sub>\<mu>"
      moreover have "Vagree \<nu> \<o>\<^sub>\<alpha> (\<iota>\<^sub>T \<V>\<^sub>T)" and "Vagree \<nu> \<o>\<^sub>\<beta> (\<iota>\<^sub>T \<V>\<^sub>T)" using runs bound_effect_on_state(2) by auto
      ultimately have notVT: "z \<in> -(\<iota>\<^sub>T \<V>\<^sub>T)" using Vagree_def by force
     
      hence "z \<in> BVP\<^sub>\<L> \<L> \<alpha>" using 0 BVP_sound_stat_sem Par(5) by blast
      hence "z \<notin> BVP\<^sub>\<L> \<L> \<beta>" using 0 notVT Par by fastforce
      hence "z \<notin> BVP (badjoint (SBindrs \<sigma>) (\<pi>\<^sub>I I)) \<beta>" using BVP_sound_stat_sem Par(5) by auto
      hence "\<nu> $$ z = \<o>\<^sub>\<beta> $$ z" using BVP_def notVT adjbeta
        by (metis (mono_tags, lifting) Bindrs_adjoint_commute Compl_iff Vagree_def bound_effect_property_short)
      hence "\<nu> $$ z \<noteq> \<o>\<^sub>\<alpha> $$ z" using 0 by simp
      hence "z \<in> BVP (\<pi>\<^sub>I I) ?\<sigma>\<alpha>" by (meson ComplI Vagree_def bound_effect_property_short runs)
      then show "lmerge \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP J (usubstpp \<sigma> \<L> U \<alpha>)) $$ z = lmerge \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP (?\<sigma>J J) \<alpha>) $$ z" 
        using 0 BVP_def Par.prems by force
    qed
    ultimately have "Vagree (lmerge \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP J ?\<sigma>\<alpha>)) (lmerge \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP (?\<sigma>J J) \<alpha>)) (-?V \<inter> ?X)" 
      by (meson Compl_iff IntI Vagree_def)
    moreover have "Vagree (lmerge \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP J ?\<sigma>\<alpha>)) (lmerge \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP (?\<sigma>J J) \<alpha>)) (-?V \<inter> -?X)"
      by (simp add: Vagree_def)
    ultimately have "Vagree (lmerge \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP J ?\<sigma>\<alpha>)) (lmerge \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP (?\<sigma>J J) \<alpha>)) (-?V)"
      using Vagree_def by auto  
    moreover have "Vagree (lmerge \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP J ?\<sigma>\<alpha>)) (lmerge \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP (?\<sigma>J J) \<alpha>)) ?V"
      unfolding Vagree_def using Par.prems adefp usubst_BVP by auto
    ultimately show "lmerge \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP J ?\<sigma>\<alpha>) = lmerge \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP (?\<sigma>J J) \<alpha>)"
      by (metis Vagree_refl lmerge_vagree)
  qed
  
  have merge: "\<forall>\<o>\<^sub>\<alpha> \<o>\<^sub>\<beta>. (\<nu>, \<tau> \<down> (CN J ?\<sigma>\<alpha>), \<o>\<^sub>\<alpha>) \<in> chp_sem I ?\<sigma>\<alpha> \<and> (\<nu>, \<tau> \<down> (CN J ?\<sigma>\<beta>), \<o>\<^sub>\<beta>) \<in> chp_sem I ?\<sigma>\<beta>
    \<and> Vagreebot \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> \<V>\<^sub>\<mu> \<longrightarrow> ((\<o> = lmergebot \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP J ?\<sigma>\<alpha>)) = (\<o> = lmergebot \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP (\<pi>\<^sub>I ?\<sigma>I) \<alpha>)))"
  proof (rule, rule, rule)
    fix \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta>
    assume 0: "(\<nu>, \<tau> \<down> (CN J ?\<sigma>\<alpha>), \<o>\<^sub>\<alpha>) \<in> chp_sem I ?\<sigma>\<alpha> \<and> (\<nu>, \<tau> \<down> (CN J ?\<sigma>\<beta>), \<o>\<^sub>\<beta>) \<in> chp_sem I ?\<sigma>\<beta> \<and> Vagreebot \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> \<V>\<^sub>\<mu>"
    show "(\<o> = lmergebot \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP J ?\<sigma>\<alpha>)) = (\<o> = lmergebot \<o>\<^sub>\<alpha> \<o>\<^sub>\<beta> (BVP (\<pi>\<^sub>I ?\<sigma>I) \<alpha>))"
    proof (cases \<o>)
      case (Fin \<kappa>)
      show ?thesis 
      proof (rule, goal_cases)
        case 1
        then obtain \<kappa>\<^sub>\<alpha> \<kappa>\<^sub>\<beta> where fin: "\<o>\<^sub>\<alpha> = Fin \<kappa>\<^sub>\<alpha> \<and> \<o>\<^sub>\<beta> = Fin \<kappa>\<^sub>\<beta>" by (metis Fin lmergebot_Exists_Fin)
        hence "Vagree \<kappa>\<^sub>\<alpha> \<kappa>\<^sub>\<beta> \<V>\<^sub>\<mu>" using 0 Vagreebot_only_Fin by blast
        then show ?case using 0 1 fin Par.prems(6) merge by auto
      next
        case 2
        then obtain \<kappa>\<^sub>\<alpha> \<kappa>\<^sub>\<beta> where fin: "\<o>\<^sub>\<alpha> = Fin \<kappa>\<^sub>\<alpha> \<and> \<o>\<^sub>\<beta> = Fin \<kappa>\<^sub>\<beta>" by (metis Fin lmergebot_Exists_Fin)
        hence "Vagree \<kappa>\<^sub>\<alpha> \<kappa>\<^sub>\<beta> \<V>\<^sub>\<mu>" using 0 Vagreebot_only_Fin by blast
        then show ?case using 0 2 fin Par.prems(6) merge by auto
      qed 
    next
      case NonFin
      then show ?thesis by (metis lmergebot.elims reachedstate.distinct(1))
    qed
  qed

  have nojunk: "(\<tau> \<down> ((CN J ?\<sigma>\<alpha>) \<union> (CN J ?\<sigma>\<beta>)) = \<tau>) = (\<tau> \<down> ((CN (\<pi>\<^sub>I ?\<sigma>I) \<alpha>) \<union> (CN (\<pi>\<^sub>I ?\<sigma>I) \<beta>)) = \<tau>)"
      using CN_usubst_eq Par.prems adefp bundef by auto

  have "((\<nu>, \<tau>, \<o>) \<in> chp_sem I ((usubstpp \<sigma> \<L> U \<alpha>) par (usubstpp \<sigma> \<L> U \<beta>)))
    = ((\<nu>, \<tau>, \<o>) \<in> chp_sem (adjoint \<sigma> I \<omega>) (\<alpha> par \<beta>))"
    apply simp
    by (metis (no_types, lifting) Bindrs_adjoint_commute CN_usubst_eq Par.IH Par.prems(2,3,4,5,6) adefp bundef wf_chp.simps(11) merge)
  
  thus "((\<nu>, \<tau>, \<o>) \<in> chp_sem I (usubstpp \<sigma> \<L> U (\<alpha> par \<beta>))) = ((\<nu>, \<tau>, \<o>) \<in> chp_sem (adjoint \<sigma> I \<omega>) (\<alpha> par \<beta>))"
    using adefp bundef by force
qed



text \<open>Lemma 16 of \<^url>\<open>http://arxiv.org/abs/1902.07230\<close>\<close>
theorem usubst_fml: "is_sound_stat_sem \<L> \<Longrightarrow> Uvariation \<nu> \<omega> U \<Longrightarrow> usubstf \<sigma> \<L> U \<phi> \<noteq> undeff 
    \<Longrightarrow> wf_fml \<L> \<phi> \<Longrightarrow> wf_usubs \<L> \<sigma>
    \<Longrightarrow> (\<nu> \<in> fml_sem I (the(usubstf \<sigma> \<L> U \<phi>))) = (\<nu> \<in> fml_sem (adjoint \<sigma> I \<omega>) \<phi>)"
  using usubst_fml_chp by simp


text \<open>Lemma 17 of \<^url>\<open>http://arxiv.org/abs/1902.07230\<close>\<close>
theorem usubst_chp: "is_sound_stat_sem \<L> \<Longrightarrow> Uvariation \<nu> \<omega> U \<Longrightarrow> snd(usubstp \<sigma> \<L> U \<alpha>)\<noteq>undefp 
    \<Longrightarrow> wf_chp \<L> \<alpha> \<Longrightarrow> wf_usubs \<L> \<sigma>
    \<Longrightarrow> ((\<nu>, \<tau>, \<o>) \<in> chp_sem I (usubstpp \<sigma> \<L> U \<alpha>)) = ((\<nu>, \<tau>, \<o>) \<in> chp_sem (adjoint \<sigma> I \<omega>) \<alpha>)"
  using usubst_fml_chp by auto



subsection \<open>Soundness of Uniform Substitution of Formulas\<close>

abbreviation usubsta :: "usubst \<Rightarrow> stat_sem \<Rightarrow> fml \<Rightarrow> fmlo"
  where "usubsta \<sigma> \<L> \<phi> \<equiv> usubstf \<sigma> \<L> {} \<phi>"


text \<open>Theorem 18 of \<^url>\<open>http://arxiv.org/abs/1902.07230\<close>\<close>
theorem usubst_sound:
  assumes sound_stat: "is_sound_stat_sem \<L>"
  assumes def: "usubsta \<sigma> \<L> \<phi> \<noteq> undeff"
  assumes wf_fml: "wf_fml \<L> \<phi>"
  assumes wf_usubs: "wf_usubs \<L> \<sigma>"
  shows "valid \<phi> \<Longrightarrow> valid (the(usubsta \<sigma> \<L> \<phi>))"
proof -  
  assume prem: "valid \<phi>"
  hence premc: "\<And>I \<omega>. \<omega> \<in> fml_sem I \<phi>" using valid_def by auto
  show "valid (the(usubsta \<sigma> \<L> \<phi>))" 
  unfolding valid_def proof (rule, rule)
    fix I::interp
    fix \<omega>
    have "(\<omega> \<in> fml_sem I (the(usubsta \<sigma> \<L> \<phi>))) = (\<omega> \<in> fml_sem (adjoint \<sigma> I \<omega>) \<phi>)"
      using usubst_fml def wf_fml Uvariation_refl sound_stat wf_usubs by blast
    also have "... = True" using premc by simp
    finally have "(\<omega> \<in> fml_sem I (the(usubsta \<sigma> \<L> \<phi>))) = True" .
    thus "\<omega> \<in> fml_sem I (the(usubstf \<sigma> \<L> {} \<phi>))" by simp
  qed
qed



subsection \<open>Soundness of Uniform Substitution of Rules\<close>

definition usubstl :: "usubst \<Rightarrow> stat_sem \<Rightarrow> fml list \<Rightarrow> (fml list) option"
  where "usubstl \<sigma> \<L> \<Gamma> \<equiv> if (\<forall>\<phi>\<in>set \<Gamma>. usubstf \<sigma> \<L> allbindrs \<phi> \<noteq> undeff)
    then Some(map (the o (usubstf \<sigma> \<L> allbindrs)) \<Gamma>) else None"

text \<open>Uniform substitution applied to a rule or inference\<close>
definition usubstr:: "usubst \<Rightarrow> stat_sem \<Rightarrow> inference \<Rightarrow> inference option"
  where "usubstr \<sigma> \<L> R \<equiv> if (usubstf \<sigma> \<L> allbindrs (snd R) \<noteq> undeff) then
    (case usubstl \<sigma> \<L> (fst R) of
        Some \<sigma>\<Gamma> \<Rightarrow> Some(\<sigma>\<Gamma>, the(usubstf \<sigma> \<L> allbindrs (snd R)))
      | None \<Rightarrow> None)
  else None"

text \<open>Simple observations about applying uniform substitutions to a rule\<close>

lemma usubstl_conv: "usubstl \<sigma> \<L> \<Gamma> \<noteq> None
  \<Longrightarrow> (\<forall>\<phi>\<in>set \<Gamma>. usubstf \<sigma> \<L> allbindrs \<phi> \<noteq> undeff)"
  by (meson usubstl_def)

lemma usubstr_conv: "usubstr \<sigma> \<L> R \<noteq> None 
  \<Longrightarrow> usubstf \<sigma> \<L> allbindrs (snd R) \<noteq> undeff \<and> (usubstl \<sigma> \<L> (fst R) \<noteq> None)"
  by (metis option.simps(4) usubstr_def)

lemma usubstl_cons_undef: "(usubstl \<sigma> \<L> (\<phi> # \<Gamma>) \<noteq> None) = (usubstl \<sigma> \<L> [\<phi>] \<noteq> None \<and> usubstl \<sigma> \<L> \<Gamma> \<noteq> None)"
  using usubstl_def by auto
lemma usubstl_cons_undef2: "(usubstl \<sigma> \<L> (\<phi> # \<Gamma>) \<noteq> None) \<Longrightarrow> (usubstl \<sigma> \<L> [\<phi>] \<noteq> None \<and> usubstl \<sigma> \<L> \<Gamma> \<noteq> None)"
  using usubstl_cons_undef by blast

lemma usubstl_union_undef: "(usubstl \<sigma> \<L> (\<Gamma> @ \<Delta>) \<noteq> None) = (usubstl \<sigma> \<L> \<Gamma> \<noteq> None \<and> usubstl \<sigma> \<L> \<Delta> \<noteq> None)"
  using usubstl_def by auto
lemma usubstl_union_undef2: "(usubstl \<sigma> \<L> (\<Gamma> @ \<Delta>) \<noteq> None) \<Longrightarrow> (usubstl \<sigma> \<L> \<Gamma> \<noteq> None \<and> usubstl \<sigma> \<L> \<Delta> \<noteq> None)"
  using usubstl_union_undef by blast

lemma usubstl_cons: "usubstl \<sigma> \<L> (\<phi> # \<Gamma>) \<noteq> None \<Longrightarrow>
  the(usubstl \<sigma> \<L> (\<phi> # \<Gamma>)) = (the(usubstf \<sigma> \<L> allbindrs \<phi>)) # (the(usubstl \<sigma> \<L> \<Gamma>))"
proof -
  assume def: "usubstl \<sigma> \<L> (\<phi> # \<Gamma>) \<noteq> None"
  hence "the(usubstl \<sigma> \<L> (\<phi> # \<Gamma>)) = map (the o (usubstf \<sigma> \<L> allbindrs)) (\<phi> # \<Gamma>)" by (metis option.sel usubstl_def)
  also have "... = (the(usubstf \<sigma> \<L> allbindrs \<phi>)) # (map(the o (usubstf \<sigma> \<L> allbindrs)) \<Gamma>)" by simp
  also have "... = (the(usubstf \<sigma> \<L> allbindrs \<phi>)) # (the(usubstl \<sigma> \<L> \<Gamma>))"
    by (metis def list.set_intros(2) option.sel usubstl_def)
  ultimately show ?thesis by auto
qed

lemma usubstl_union: "usubstl \<sigma> \<L> (\<Gamma> @ \<Delta>) \<noteq> None \<Longrightarrow>
  the(usubstl \<sigma> \<L> (\<Gamma> @ \<Delta>)) = (the(usubstl \<sigma> \<L> \<Gamma>)) @ (the(usubstl \<sigma> \<L> \<Delta>))"
proof-
  assume def: "usubstl \<sigma> \<L> (\<Gamma> @ \<Delta>) \<noteq> None"
  hence def2: "usubstl \<sigma> \<L> \<Gamma> \<noteq> None \<and> usubstl \<sigma> \<L> \<Delta> \<noteq> None"
    by (metis Un_iff option.distinct(1) set_append usubstl_def)

  have "the(usubstl \<sigma> \<L> (\<Gamma> @ \<Delta>)) = map(the o (usubstf \<sigma> \<L> allbindrs)) (\<Gamma> @ \<Delta>)" 
    using def by (metis option.sel usubstl_def)
  also have "... = (map(the o (usubstf \<sigma> \<L> allbindrs)) \<Gamma>) @ (map(the o (usubstf \<sigma> \<L> allbindrs)) \<Delta>)" by simp
  also have "... = (the(usubstl \<sigma> \<L> \<Gamma>)) @ (the(usubstl \<sigma> \<L> \<Delta>))" by (metis def2 option.sel usubstl_def)
  ultimately show ?thesis by simp
qed

lemma usubstl_length: "usubstl \<sigma> \<L> \<Gamma> \<noteq> None \<Longrightarrow> length (the(usubstl \<sigma> \<L> \<Gamma>)) = length \<Gamma>"
  by (metis length_map option.sel usubstl_def)

lemma usubstl_nth: "usubstl \<sigma> \<L> \<Gamma> \<noteq> None \<Longrightarrow> k<length \<Gamma> \<Longrightarrow> nth(the(usubstl \<sigma> \<L> \<Gamma>)) k = the(usubstf \<sigma> \<L> allbindrs (nth \<Gamma> k))"
proof (induction \<Gamma> arbitrary: k, simp)
  case (Cons \<phi> \<Gamma>)
  then show ?case
  proof (cases k)
    case 0
    then show ?thesis using Cons usubstl_cons by simp
  next
    case (Suc n)
    hence "n<length \<Gamma>" using Cons.prems(2) by auto 
    moreover have "usubstl \<sigma> \<L> \<Gamma> \<noteq> None" using Cons usubstl_cons_undef2 by blast
    ultimately have "nth (the(usubstl \<sigma> \<L> \<Gamma>)) n = the(usubstf \<sigma> \<L> allbindrs (nth \<Gamma> n))" using Cons.IH by blast
    then show ?thesis using Cons usubstl_cons by (simp add: Suc) 
  qed
qed

lemma usubstr_fst: "usubstr \<sigma> \<L> R \<noteq> None \<Longrightarrow> fst(the(usubstr \<sigma> \<L> R)) = the(usubstl \<sigma> \<L> (fst R))"
  by (metis (no_types, lifting) fst_conv option.case_eq_if option.sel usubstr_def)



text \<open>Theorem 19 of \<^url>\<open>http://arxiv.org/abs/1902.07230\<close>\<close>
theorem usubst_rule_sound:
  assumes sound_stat: "is_sound_stat_sem \<L>"
  assumes wf_usubs: "wf_usubs \<L> \<sigma>"
  assumes def: "usubstr \<sigma> \<L> R \<noteq> None \<and> wf_inference \<L> R"
  shows "locally_sound R \<Longrightarrow> locally_sound (the(usubstr \<sigma> \<L> R))"
proof -
  fix \<omega>
  have substeq: "\<And>I \<nu> \<phi>. usubstf \<sigma> \<L> allbindrs \<phi> \<noteq> undeff \<Longrightarrow> wf_fml \<L> \<phi> 
    \<Longrightarrow> (\<nu> \<in> fml_sem I (the(usubstf \<sigma> \<L> allbindrs \<phi>))) = (\<nu> \<in> fml_sem (adjoint \<sigma> I \<omega>) \<phi>)" 
    using usubst_fml Uvariation_univ sound_stat wf_usubs by blast
  hence substval: "\<And>I \<phi>. usubstf \<sigma> \<L> allbindrs \<phi> \<noteq> undeff \<Longrightarrow> wf_fml \<L> \<phi> 
    \<Longrightarrow> valid_in I (the(usubstf \<sigma> \<L> allbindrs \<phi>)) = valid_in (adjoint \<sigma> I \<omega>) \<phi>" 
    unfolding valid_in_def by blast

  have wf_pos: "\<forall>k < length (fst R). wf_fml \<L> ((fst R) ! k)" using def wf_inference_def by blast
  have def_pos: "\<forall>k < length (fst R). (usubstf \<sigma> \<L> allbindrs ((fst R) ! k)) \<noteq> None"
    using def nth_mem usubstr_conv usubstl_conv by blast
  
  assume prem: "locally_sound R"
  show "locally_sound (the (usubstr \<sigma> \<L> R))" 
  unfolding locally_sound_def proof (clarify)
    fix I::interp
    let ?\<sigma>R = "usubstr \<sigma> \<L> R"

    assume sigprems: "\<forall>k\<ge>0. k < length (fst(the ?\<sigma>R)) \<longrightarrow> valid_in I (nth(fst(the ?\<sigma>R)) k)"  
    have len: "length (fst (the (usubstr \<sigma> \<L> R))) = length (fst R)"
      using def usubstl_length usubstr_conv usubstr_fst by auto
    
    have "\<forall>k\<ge>0. k < length (fst(the ?\<sigma>R)) \<longrightarrow> valid_in (adjoint \<sigma> I \<omega>) (nth(fst R) k)"
    proof (clarify)
      fix k
      let ?\<phi> = "nth (fst R) k"

      assume pos: "k < length (fst (the (usubstr \<sigma> \<L> R)))"
      hence "valid_in I (nth(fst(the ?\<sigma>R)) k)" using sigprems by simp
      hence "valid_in I (nth(the(usubstl \<sigma> \<L> (fst R))) k)"
        using def usubstr_def usubstr_fst by simp
      hence "valid_in I (the(usubstf \<sigma> \<L> allbindrs ?\<phi>))" 
        using def pos len usubstr_conv usubstl_nth by simp
      thus "valid_in (adjoint \<sigma> I \<omega>) ?\<phi>"
        using wf_pos def_pos pos substval len by simp
    qed
    hence "valid_in (adjoint \<sigma> I \<omega>) (snd R)" using len locally_sound_def prem by presburger
    hence "valid_in I (the(usubstf \<sigma> \<L> allbindrs (snd R)))" 
      by (metis wf_inference_def def substval usubstr_conv)
    thus "valid_in I (snd (the (usubstr \<sigma> \<L> R)))"
      by (metis (no_types, lifting) def option.case_eq_if option.sel sndI usubstr_def)
  qed
qed

end
