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
#include "smt/params/smt_params.h"
#include "ast/ast_pp.h"

// conjunctive fragment := cf

static bool is_cf(goal const & g) {
    ast_manager & m = g.m();
    seq_util u(m);
    unsigned sz = g.size();
    for (unsigned i = 0; i < sz; i++) {
        expr * f  = g.form(i);
        bool sign = true;
        while (m.is_not(f, f))
            sign = !sign;
        if (m.is_eq(f) && !sign) {
            if (m.get_sort(to_app(f)->get_arg(0))->get_family_id() == u.get_family_id())
                TRACE("str", tout << "Not conjunctive fragment! " << mk_pp(f, m) << std::endl;);
                return false;
            continue;
        }
        if ((u.str.is_prefix(f) || u.str.is_suffix(f)) && !sign) {
            TRACE("str", tout << "Not conjunctive fragment! " << mk_pp(f, m)<< std::endl;);
            return false;
        }
        if (u.str.is_contains(f)) {
            TRACE("str", tout << "Not conjunctive fragment! " << mk_pp(f, m) << std::endl;);
            return false;
        }
    }
    TRACE("str", tout << "Conjunctive fragment!" << std::endl;);
    return true;
}

class is_cf_probe : public probe {
public:
    result operator()(goal const & g) override {
        return is_cf(g);
    }
};

probe * mk_is_cf_probe() {
    return alloc(is_cf_probe);
}

class z3str3_cegar_tactical : public tactic {
protected:
    tactic * _solver1;
    tactic * _solver2;
public:
    z3str3_cegar_tactical(tactic * solver1, tactic * solver2) :
        _solver1(solver1), _solver2(solver2) {
    }
    tactic * translate(ast_manager & m) override {
        return alloc(z3str3_cegar_tactical, _solver1, _solver2);
    }
    void cleanup() override {
    }

    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        ast_manager & m = in->m();
        try {
            _solver1->operator()(in, result);
            return;
        } catch (tactic_exception &) {
            result.reset();
        }
        expr_ref_vector forms(m);
        in->get_formulas(forms);
        for (auto ex : forms) {
            TRACE("str", tout << mk_pp(ex, m) << std::endl;);
        }
        _solver2->operator()(in, result);
    }

    void collect_statistics(::statistics & st) const {
        _solver1->collect_statistics(st);
        _solver2->collect_statistics(st);
    }

};

tactic * mk_z3str3_cegar_tactical(tactic * s1, tactic * s2) {
    return alloc(z3str3_cegar_tactical, s1, s2);
}

tactic * mk_z3str3_tactic(ast_manager & m, params_ref const & p) {
    TRACE("str", tout << "using Z3str3 portfolio tactic" << std::endl;);
    smt_params m_smt_params;
    m_smt_params.updt_params(p);

    tactic * preamble = mk_simplify_tactic(m, p);

    params_ref preprocess_p = p;
    preprocess_p.set_bool("str.fixed_length_preprocessing", true);
    preprocess_p.set_bool("str.fixed_length_models", true);
    preprocess_p.set_sym("string_solver", symbol("z3str3"));

    params_ref general_p = p;
    general_p.set_bool("str.fixed_length_preprocessing", false);
    general_p.set_bool("str.fixed_length_models", false);
    general_p.set_sym("string_solver", symbol("z3str3"));

    params_ref seq_p = p;
    seq_p.set_sym("string_solver", symbol("seq"));

    tactic * z3str3_1 = using_params(mk_smt_tactic(m), preprocess_p);
    tactic * z3str3_2 = using_params(mk_smt_tactic(m), general_p);
    tactic * z3seq    = try_for(using_params(mk_smt_tactic(m), seq_p), 200);

    tactic * st = using_params(and_then(preamble, cond(mk_is_cf_probe(), 
                        mk_z3str3_cegar_tactical(z3str3_1, z3str3_2),
                        or_else(z3seq, z3str3_2))), p);
    return st;
}
