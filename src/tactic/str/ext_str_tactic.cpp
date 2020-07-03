#include "tactic/tactical.h"
#include "tactic/str/ext_str_tactic.h"
#include "tactic/generic_model_converter.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/expr_replacer.h"
#include "ast/rewriter/var_subst.h"

class ext_str_tactic : public tactic {
    struct imp {
        typedef generic_model_converter mc;

        ast_manager& m;
        seq_util u;
        arith_util m_autil;
        scoped_ptr<expr_replacer> m_replace;
        ptr_vector<expr> stack;
        ref<mc> m_mc;
        bool m_produce_models;

        imp(ast_manager& _m, params_ref const& p) :
            m(_m),
            u(m),
            m_autil(m) {
            m_replace = mk_default_expr_replacer(m, false);
            updt_params(p);
        }

        void updt_params(params_ref const& p) {

        }

        void process_eq(expr* eq, goal_ref const& g, expr_substitution& sub) {
            if (sub.contains(eq)) return;

            expr* lhs;
            expr* rhs;

            m.is_eq(eq, lhs, rhs);

            // Rewrite: (= (str.to_int S) #const) and #const >= 0 --> (str.in_re S (0* ++ #const))
            {
                bool rewrite_applies = false;
                expr* string_subterm = nullptr;
                rational integer_constant;

                if (u.str.is_stoi(lhs, string_subterm)) {
                    if (m_autil.is_numeral(rhs, integer_constant)) {
                        rewrite_applies = true;
                    }
                } else if (u.str.is_stoi(rhs, string_subterm)) {
                    if (m_autil.is_numeral(lhs, integer_constant)) {
                        rewrite_applies = true;
                    }
                }

                if (rewrite_applies) {
                    if (integer_constant.is_nonneg()) {
                        TRACE("ext_str_tactic", tout << "str.to_int rewrite applies: " << mk_pp(string_subterm, m) << " in 0*" << integer_constant << std::endl;);
                        symbol integer_constant_string(integer_constant.to_string().c_str());
                        symbol zero("0");
                        expr_ref regex(u.re.mk_concat(u.re.mk_star(u.re.mk_to_re(u.str.mk_string(zero))), u.re.mk_to_re(u.str.mk_string(integer_constant_string))), m);
                        expr_ref str_in_regex(u.re.mk_in_re(string_subterm, regex), m);
                        sub.insert(eq, str_in_regex);
                    }
                }
            }

            stack.push_back(lhs);
            stack.push_back(rhs);
        }

        void operator()(goal_ref const& g, goal_ref_buffer& result) {
            SASSERT(g->is_well_formed());
            tactic_report report("ext_str", *g);
            fail_if_proof_generation("ext_str", g);
            m_produce_models = g->models_enabled();
            if (m_produce_models) {
                m_mc = alloc(generic_model_converter, m, "ext_str");
            } else {
                m_mc = nullptr;
            }

            SASSERT(g->is_well_formed());

            result.reset();

            TRACE("ext_str_tactic", tout << "BEFORE:" << std::endl; g->display(tout););

            if (g->inconsistent()) {
                result.push_back(g.get());
                return;
            }

            expr_substitution sub(m);
            unsigned size = g->size();
            for (unsigned idx = 0; idx < size; ++idx) {
                if (g->inconsistent()) break;
                expr* curr = g->form(idx);

                if (is_app(curr)) {
                    stack.reset();
                    stack.push_back(curr);

                    while (!stack.empty()) {
                        curr = stack.back();
                        stack.pop_back();

                        if (!is_app(curr)) continue;

                        TRACE("ext_str_tactic", tout << "curr: " << mk_pp(curr, m) << std::endl;);

                        if (m.is_eq(curr)) {
                            process_eq(curr, g, sub);
                        }
                    }
                }
            }

            m_replace->set_substitution(&sub);

            for (unsigned i = 0; i < g->size(); ++i) {
                expr_ref new_curr(m);
                proof_ref new_pr(m);
                (*m_replace)(g->form(i), new_curr, new_pr);
                if (m.proofs_enabled() && !new_pr) {
                    new_pr = m.mk_rewrite(g->form(i), new_curr);
                    new_pr = m.mk_modus_ponens(g->pr(i), new_pr);
                }
                g->update(i, new_curr, new_pr, g->dep(i));
            }

            /*
            for (auto e : m_delayed_assertions) {
                g->assert_expr(e);
            }

            if (m_mc) {
                for (auto v : m_fresh_vars) {
                    m_mc->hide(to_app(v)->get_decl());
                }
            }

            if (m_produce_models && !m_fresh_vars.empty()) {
                g->add(m_mc.get());
            }
            */
            g->inc_depth();
            result.push_back(g.get());
            SASSERT(g->is_well_formed());
            TRACE("ext_str_tactic", tout << "AFTER: " << std::endl; g->display(tout);
            if (g->mc()) g->mc()->display(tout); tout << std::endl;);
        }
    };

    imp* m_imp;
    params_ref m_params;

public:
    ext_str_tactic(ast_manager& m, params_ref const& p) :
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    tactic* translate(ast_manager& m) override {
        return alloc(ext_str_tactic, m, m_params);
    }

    ~ext_str_tactic() override {
        dealloc(m_imp);
    }

    void updt_params(params_ref const& p) override {
        m_params = p;
        m_imp->updt_params(p);
    }

    void operator()(goal_ref const& in, goal_ref_buffer& result) override {
        try {
            (*m_imp)(in, result);
        }
        catch (rewriter_exception& ex) {
            throw tactic_exception(ex.msg());
        }
    }

    void cleanup() override {
        imp* d = alloc(imp, m_imp->m, m_params);
        std::swap(d, m_imp);
        dealloc(d);
    }
};

tactic * mk_ext_str_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(ext_str_tactic, m, p));
}