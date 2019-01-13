/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    z3str3_tactic.cpp

Abstract:

    Tactic for string instances that synergizes with Z3str3

Author:

    Murphy Berzish (mtrberzi) 2019-01-10

Notes:

--*/
#include "util/params.h"
#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "smt/tactic/smt_tactic.h"

tactic * mk_z3str3_tactic(ast_manager & m, params_ref const & p) {
    tactic * preamble = mk_simplify_tactic(m, p);

    params_ref preprocess_p = p;
    preprocess_p.set_bool("str.fixed_length_preprocessing", true);
    preprocess_p.set_bool("str.fixed_length_models", true);
    preprocess_p.set_bool("str.count_abstraction", true);
    preprocess_p.set_bool("str.multiset_check", true);
    preprocess_p.set_sym("string_solver", symbol("z3str3"));

    params_ref general_p = p;
    general_p.set_bool("str.fixed_length_preprocessing", false);
    general_p.set_bool("str.fixed_length_models", false);
    general_p.set_sym("string_solver", symbol("z3str3"));

    tactic * st = and_then(preamble, or_else(
            using_params(mk_smt_tactic(m), preprocess_p),
            using_params(mk_smt_tactic(m), general_p)));
    st->updt_params(p);
    return st;
}
