theory Bicompose_Rename_Fix_Test
  imports Main
begin

text \<open>Checks of the renaming in \<open>newAs\<close> (\<open>Thm.bicompose_aux\<close>).
  R1--R3: the three cases found by Kevin Kappelmann and Fabian Huch do not prove \<open>False\<close>. P1--P3: ordinary rule steps still rename after the goal's bound variables.
  D1, E1, N1: the proof state's own unknowns keep their names.
  Each check prints one line \<open><id>: PASS\<close> or \<open><id>: FAIL\<close> and never aborts the others;
  after all checks, the theory fails if any check failed.\<close>


section \<open>Fixtures: the rules of the three cases\<close>

lemma flex_rule1: "x True \<Longrightarrow> x True" .
lemma flex_rule2: "P True \<Longrightarrow> \<forall>x::bool. P True" by simp
lemma eres_rule: "P True \<Longrightarrow> (\<forall>x::bool. \<not> P True) \<Longrightarrow> False" by simp

definition X :: "prop" where "X \<equiv> (\<And>w::bool. True \<Longrightarrow> False)"
lemma split_rule: "(\<And>z::bool. z = w \<Longrightarrow> z \<noteq> w) \<Longrightarrow> PROP X"
  unfolding X_def by auto
lemma split_aux: "z = True \<Longrightarrow> z \<noteq> False" by simp


section \<open>Checks\<close>

ML \<open>
structure Bicompose_Rename_Fix_Test =
struct

val ctxt = \<^context>;

fun term_str t = Syntax.string_of_term ctxt t;
fun first_result tac st = Option.map #1 (Seq.pull (tac st));
fun var_names t = rev (Term.add_vars t []) |> map (fn ((x, _), _) => x);
fun subgoal st = Thm.prem_of st 1;
fun nprems_str st = "nprems " ^ string_of_int (Thm.nprems_of st);

(*R1, R2: the new subgoal is False and TrueI does not close it*)
fun check_false st =
  let
    val ok_subgoal = Thm.nprems_of st = 1 andalso subgoal st aconv \<^prop>\<open>False\<close>;
    val closed = first_result (resolve_tac ctxt @{thms TrueI} 1) st;
    val ok_closed = is_none closed;
    val closed_str =
      (case closed of
        NONE => "rule TrueI fails"
      | SOME st' =>
          "rule TrueI closes it" ^
            (case Exn.result (Goal.finish ctxt) st' of
              Exn.Res th => ", proving " ^ term_str (Thm.prop_of th)
            | Exn.Exn exn => ", Goal.finish fails: " ^ Runtime.exn_message exn));
  in (ok_subgoal andalso ok_closed, "subgoal " ^ term_str (subgoal st) ^ "; " ^ closed_str) end;

(*R3: both equations contain the same unknown, and rule split_aux, assumption fails*)
fun check_split st =
  let
    val prem = subgoal st;
    val hyps = Logic.strip_assums_hyp prem;
    val concl = Logic.strip_assums_concl prem;
    val same =
      (case (hyps, try (HOLogic.dest_not o HOLogic.dest_Trueprop) concl) of
        ([hyp], SOME eq) =>
          (case (try (HOLogic.dest_eq o HOLogic.dest_Trueprop) hyp, try HOLogic.dest_eq eq) of
            (SOME (_, a), SOME (_, b)) => is_Var a andalso a aconv b
          | _ => false)
      | _ => false);
    val cont =
      first_result (resolve_tac ctxt @{thms split_aux} 1 THEN assume_tac ctxt 1) st;
    val cont_str =
      (case cont of
        NONE => "rule split_aux, assumption fails"
      | SOME st' => "rule split_aux, assumption succeeds, leaving " ^ nprems_str st' ^
          (if Thm.nprems_of st' = 0 then ", goal " ^ term_str (Thm.concl_of st') else ""));
  in
    (Thm.nprems_of st = 1 andalso same andalso is_none cont,
      "subgoal " ^ term_str prem ^ "; " ^ cont_str)
  end;

(*P1, P2: the new subgoal contains an unknown named y*)
fun check_unknown_y st =
  (exists (fn x => x = "y") (var_names (subgoal st)),
    "subgoal " ^ term_str (subgoal st) ^ "; unknowns " ^ commas (var_names (subgoal st)));

(*P3: the new subgoal has a parameter named y*)
fun check_param_y st =
  let val params = map #1 (Logic.strip_params (subgoal st))
  in (params = ["y"], "subgoal " ^ term_str (subgoal st) ^ "; parameters " ^ commas params) end;

(*a term with every unknown shown as ?name.index and every loose bound variable as B<index>*)
fun raw_str (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ A $ B) =
      "(" ^ raw_str A ^ " ==> " ^ raw_str B ^ ")"
  | raw_str (Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (x, _, b)) =
      "(!!" ^ x ^ ". " ^ raw_str b ^ ")"
  | raw_str (Const (\<^const_name>\<open>Trueprop\<close>, _) $ t) = raw_str t
  | raw_str (Abs (x, _, b)) = "(%" ^ x ^ ". " ^ raw_str b ^ ")"
  | raw_str (t as _ $ _) =
      let val (h, args) = strip_comb t in "(" ^ space_implode " " (map raw_str (h :: args)) ^ ")" end
  | raw_str (Const (c, _)) = Long_Name.base_name c
  | raw_str (Free (x, _)) = x
  | raw_str (Var ((x, i), _)) = "?" ^ x ^ "." ^ string_of_int i
  | raw_str (Bound i) = "B" ^ string_of_int i;

fun vars_str vs = commas (map (fn v => raw_str (Var v)) vs);

(*D1, E1, N1: the state's unknown s has the name that the renaming in newAs renames
  (old -> new) in the rule. Unknowns of the state have index <= smax (the goal's maxidx),
  unknowns of the lifted rule a higher index, and the renaming changes names only.
  (a) s occurs in the new subgoal, and every unknown of the new subgoal with index <= smax is
      an unknown of the goal: no occurrence of s is renamed, in the lifted part or elsewhere;
  (b) no unknown with index > smax is named old, and one named new occurs.
  Unknowns of the rule occur only in the remaining part, so (b) is about the remaining part.*)
fun check_preserved (s, (old, new)) goal st =
  let
    val smax = Term.maxidx_of_term goal;
    val goal_vars = Term.add_vars goal [];
    val prem = subgoal st;
    val (state_vars, rule_vars) =
      List.partition (fn ((_, i), _) => i <= smax) (rev (Term.add_vars prem []));
    val ok_a =
      exists (fn (xi, _) => xi = s) state_vars andalso
      forall (member (op =) goal_vars) state_vars;
    val ok_b =
      not (exists (fn ((x, _), _) => x = old) rule_vars) andalso
      exists (fn ((x, _), _) => x = new) rule_vars;
    fun verdict ok = if ok then "holds" else "does not hold";
  in
    (ok_a andalso ok_b,
      "goal " ^ raw_str goal ^ "; subgoal " ^ raw_str prem ^ "; " ^ nprems_str st ^
      "; (a) state unknown ?" ^ fst s ^ "." ^ string_of_int (snd s) ^ " kept: " ^
      verdict ok_a ^
      " [unknowns with index <= " ^ string_of_int smax ^ ": " ^ vars_str state_vars ^ "]" ^
      "; (b) rule unknown ?" ^ old ^ " renamed to ?" ^ new ^ " everywhere: " ^ verdict ok_b ^
      " [unknowns with index > " ^ string_of_int smax ^ ": " ^ vars_str rule_vars ^ "]")
  end;

val schematic_goal =
  Var (("G", 0), (\<^typ>\<open>nat\<close> --> \<^typ>\<open>nat\<close>) --> propT) $
    Abs ("v", \<^typ>\<open>nat\<close>, Bound 0);

(*the state's unknown sits in the parameters and assumptions introduced by lifting;
  \<^prop> rejects unknowns, so the goals are read in schematic mode*)
val read_schematic = Syntax.read_prop (Proof_Context.set_mode Proof_Context.mode_schematic ctxt);
val goal_D1 = read_schematic "\<And>u::nat. ?x = u \<Longrightarrow> \<exists>y. y = ?x";
val goal_E1 = read_schematic "(\<forall>y::nat. y = ?x) \<Longrightarrow> ?x = 0 \<Longrightarrow> False";
val goal_N1 =
  read_schematic "True \<Longrightarrow> (\<And>a::nat. ?w = a \<Longrightarrow> PROP ?G (\<lambda>v::nat. v))";

val checks =
 [("R1", \<^prop>\<open>\<forall>y::bool. False\<close>,
    resolve_tac ctxt @{thms flex_rule1[THEN flex_rule2]} 1, check_false),
  ("R2", \<^prop>\<open>\<forall>y::bool. \<not> False \<Longrightarrow> False\<close>,
    eresolve_tac ctxt @{thms flex_rule1[THEN eres_rule, rotated]} 1, check_false),
  ("R3", schematic_goal,
    resolve_tac ctxt @{thms split_rule[unfolded X_def]} 1, check_split),
  ("P1", \<^prop>\<open>\<exists>y::nat. y = y\<close>, resolve_tac ctxt @{thms exI} 1, check_unknown_y),
  ("P2", \<^prop>\<open>\<forall>y::nat. P y \<Longrightarrow> P 0\<close>, eresolve_tac ctxt @{thms allE} 1, check_unknown_y),
  ("P3", \<^prop>\<open>\<forall>y::nat. y = y\<close>, resolve_tac ctxt @{thms allI} 1, check_param_y),
  ("D1", goal_D1, resolve_tac ctxt @{thms exI} 1,
    check_preserved (("x", 0), ("x", "y")) goal_D1),
  ("E1", goal_E1, eresolve_tac ctxt @{thms allE} 1,
    check_preserved (("x", 0), ("x", "y")) goal_E1),
  ("N1", goal_N1, resolve_tac ctxt @{thms split_rule[unfolded X_def]} 1,
    check_preserved (("w", 0), ("w", "v")) goal_N1)];

(*SOME line for a failed check*)
fun run_check (id, goal, tac, check) =
  let
    val st0 = Goal.init (Thm.cterm_of ctxt goal);
    fun step () =
      (case first_result tac st0 of
        NONE => (false, "the rule step fails")
      | SOME st => check st);
    val (ok, detail) =
      (case Exn.result step () of
        Exn.Res res => res
      | Exn.Exn exn => (false, "exception: " ^ Runtime.exn_message exn));
    val line = id ^ ": " ^ (if ok then "PASS" else "FAIL") ^ " -- " ^ detail;
    val _ = writeln line;
  in if ok then NONE else SOME line end;

fun run () =
  (case map_filter run_check checks of
    [] => ()
  | failed => error (cat_lines ("Bicompose_Rename_Fix_Test: failed checks:" :: failed)));

end;

val _ = Bicompose_Rename_Fix_Test.run ();
\<close>

end
