theory "dLCHP_Ids"
imports Complex_Main
  "Syntax"
begin
text \<open>Some specific identifiers used in Axioms\<close>
abbreviation chpid1::ident where "chpid1 \<equiv> CHR ''a''"
abbreviation chpid2::ident where "chpid2 \<equiv> CHR ''b''"
abbreviation chpid3::ident where "chpid3 \<equiv> CHR ''c''"

abbreviation ch1::ident where "ch1 \<equiv> CHR ''9''"

abbreviation chset1::ident where "chset1 \<equiv> CHR ''Y''"
abbreviation chset2::ident where "chset2 \<equiv> CHR ''L''"
abbreviation chset3::ident where "chset3 \<equiv> CHR ''M''"

(* chars used for variable identifiers may be unusual 
on paper but are anyway abstracted by the names of 
the variables *)
abbreviation xvar1::ident where "xvar1 \<equiv> CHR ''z''"
abbreviation xvar2::ident where "xvar2 \<equiv> CHR ''l''"
abbreviation vvar::rvar where "vvar \<equiv> RVarName CHR ''v''"


abbreviation zvar3::ident where "zvar3 \<equiv> CHR ''j''"
abbreviation zvar4::ident where "zvar4 \<equiv> CHR ''k''"
abbreviation zvar5::ident where "zvar5 \<equiv> CHR ''o''"
abbreviation zvar6::ident where "zvar6 \<equiv> CHR ''n''"

abbreviation pid1::ident  where "pid1 \<equiv> CHR ''p''"
abbreviation pid2::ident  where "pid2 \<equiv> CHR ''q''"

abbreviation pid_A::ident  where "pid_A \<equiv> CHR ''A''"
abbreviation pid_B::ident where "pid_B \<equiv> CHR ''B''"
abbreviation pid_C::ident  where "pid_C \<equiv> CHR ''C''"
abbreviation pid_C2::ident  where "pid_C2 \<equiv> CHR ''E''"
abbreviation pid_p3::ident  where "pid_p3 \<equiv> CHR ''P''"

abbreviation fid1::ident  where "fid1 \<equiv> CHR ''f''"
abbreviation xid1::rvar where "xid1 \<equiv> RVarName CHR ''x''"

abbreviation rec::tvar where "rec \<equiv> CHR ''h''"
abbreviation his::tvar where "his \<equiv> CHR ''w''"
abbreviation hid0::tvar where "hid0 \<equiv> CHR ''r''"
abbreviation hid'::tvar where "hid' \<equiv> CHR ''i''"

end
