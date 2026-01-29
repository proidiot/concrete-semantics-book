theory Examples
  imports BigStepEquiv
begin

theorem dead_assign: "(v ::= 9001 ;; v ::= 42) \<sim> (v ::= 42)"
proof (intro allI iffI)
  fix s t
  assume "(v ::= 9001 ;; v ::= 42,s) \<leadsto> t"
  then obtain x where
      step1: "(v ::= 9001,s) \<leadsto> x"
      and
      step2: "(v ::= 42,x) \<leadsto> t"
    using big_step.cases
    by blast
  from step1 have state1: "x = s replacing ''v'' with 9001"
    using big_step.cases by blast
  from step2 have state2: "t = x replacing ''v'' with 42"
    using big_step.cases by blast
  hence "t = (s replacing ''v'' with 9001) replacing ''v'' with 42"
    using state1 by simp
  hence "t = s replacing ''v'' with 42"
    by simp
  thus "(v ::= 42,s) \<leadsto> t"
    using big_step.Assignment sorry
next
  fix s t
  assume "(v ::= 42,s) \<leadsto> t"
  hence "t = s replacing ''v'' with 42"
    using big_step.cases by blast
  have step1: "(v ::= 9001,s) \<leadsto> (s replacing ''v'' with 9001)"
    using big_step.Assignment sorry
  have
      "(v ::= 42,(s replacing v with 9001))
      \<leadsto> (s replacing v with 9001) replacing v with 42"
    using big_step.Assignment sorry
  hence
      "(v ::= 42,(s replacing v with 9001))
      \<leadsto> (s replacing v with 42)"
    by simp
  hence step2: "(v ::= 42,(s replacing v with 9001)) \<leadsto> t"
    using `t = s replacing v with 42` by simp
  show "(v ::= 9001 ;; v ::= 42,s) \<leadsto> t"
    using step1 step2 big_step.Sequence by metis
qed    

theorem infinite_loop: "\<not> (WHILE TRUE DO SKIP OD,s) \<leadsto> t"
proof
  assume assm: "(WHILE TRUE DO SKIP OD,s) \<leadsto> t"
  then obtain c where
      "c = (WHILE TRUE DO SKIP OD)"
      and
      "(c,s) \<leadsto> t"
    by blast
  from `(c,s) \<leadsto> t` show False
  proof (induct "(c,s)" t rule: big_step.induct)
    case LoopFalse
    thus ?case
      using `c = (WHILE TRUE DO SKIP OD)` by simp
  next
    case LoopTrue
    thus False try
  qed auto
qed

end