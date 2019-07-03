/*++

Module Name:

    ext_str_tactic.cpp

Abstract:

    Tactic that eliminates extended string expressions

Author:

    Federico Mora (FedericoAureliano) 2019-06-06

Notes:

--*/
#include "tactic/tactical.h"
#include "tactic/str/ext_str_tactic.h"
#include "tactic/generic_model_converter.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/expr_replacer.h"

class ext_str_tactic : public tactic {

    struct imp {

        typedef generic_model_converter mc;

        ast_manager &              m;
        seq_util                   u;
        arith_util                 m_autil;
        expr_ref_vector            m_fresh_vars;
        ptr_vector<expr>           stack;
        scoped_ptr<expr_replacer>  m_replace;
        ref<mc>                    m_mc;
        bool                       m_produce_models;

        imp(ast_manager & _m, params_ref const & p):
            m(_m),
            u(m),
            m_autil(m),
            m_fresh_vars(m) {
            m_replace = mk_default_expr_replacer(m);
            updt_params(p);
        }

        void updt_params(params_ref const & p) {

        }

        void process_logical_connective(expr * op, goal_ref const & g, expr_substitution & sub)
        {
            
        }

        void process_eq(expr * eq, goal_ref const & g, expr_substitution & sub)
        {
            expr * lhs, * rhs;
            m.is_eq(eq, lhs, rhs);
            stack.push_back(lhs);
            stack.push_back(rhs);
        }

        void process_concat(expr * concat, goal_ref const & g, expr_substitution & sub)
        {
            expr * lhs, * rhs;
            u.str.is_concat(concat, lhs, rhs);
            stack.push_back(lhs);
            stack.push_back(rhs);
        }

        void process_prefix(expr * prefix, goal_ref const & g, expr_substitution & sub)
        {
            expr * lhs, * rhs;
            u.str.is_prefix(prefix, lhs, rhs);
            stack.push_back(lhs);
            stack.push_back(rhs);
        }

        void process_suffix(expr * suffix, goal_ref const & g, expr_substitution & sub)
        {
            expr * lhs, * rhs;
            u.str.is_suffix(suffix, lhs, rhs);
            stack.push_back(lhs);
            stack.push_back(rhs);
        }

        void process_contains(expr * contains, goal_ref const & g, expr_substitution & sub)
        {
            expr * lhs, * rhs;
            u.str.is_contains(contains, lhs, rhs);
            stack.push_back(lhs);
            stack.push_back(rhs);
        }

        void process_extract(expr * extract, goal_ref const & g, expr_substitution & sub)
        {
            expr * y, *n, *l;
            u.str.is_extract(extract, y, n, l);
            // make a fresh string variable and put it in place of the ext_string
            app * v;
            v = m.mk_fresh_const(nullptr, u.str.mk_string_sort());
            m_fresh_vars.push_back(v);
            expr_ref x(v, m);

            // inject auxiliary lemma
            v = m.mk_fresh_const(nullptr, u.str.mk_string_sort());
            m_fresh_vars.push_back(v);
            expr_ref z1(v, m);
            v = m.mk_fresh_const(nullptr, u.str.mk_string_sort());
            m_fresh_vars.push_back(v);
            expr_ref z2(v, m);

            expr_ref zero(m_autil.mk_numeral(rational(0), true), m);
            symbol sym("");
            expr_ref empty_str(u.str.mk_string(sym), m);
            expr_ref len_y(u.str.mk_length(y), m);
            expr_ref len_z1(u.str.mk_length(z1), m);

            expr_ref c(m.mk_and(m_autil.mk_ge(n, zero), m_autil.mk_ge(n, zero), m_autil.mk_gt(m_autil.mk_add(n, len_y), zero)), m);
            expr_ref then(m.mk_and(m.mk_eq(y, u.str.mk_concat(z1, x, z2)), m.mk_eq(len_z1, n)), m);
            expr_ref el(m.mk_eq(x, empty_str), m);

            TRACE("ext_str_debug", tout 
                << "if\n\t" << mk_pp(c, m) 
                << "\nthen\n\t" << mk_pp(then, m) 
                << "\nelse\n\t" << mk_pp(el, m) << std::endl;);

            g->assert_expr(m.mk_ite(c, then, el));

            // TRACE("ext_str_debug", tout << "curr replaced by: " << mk_pp(x, m) << std::endl;);
            // return x;
            stack.push_back(y);
            stack.push_back(n);
            stack.push_back(l);

            sub.insert(extract, x);
        }

        void process_length(expr * length, goal_ref const & g, expr_substitution & sub)
        {
            expr * child;
            u.str.is_length(length, child);
            stack.push_back(child);
        }

        void process_arith_op(expr * op, goal_ref const & g, expr_substitution & sub)
        {
            
        }

        void process_arith_comparison(expr * comparison, goal_ref const & g, expr_substitution & sub)
        {
            
        }

        void operator()(goal_ref const & g, goal_ref_buffer & result) {
            SASSERT(g->is_well_sorted());
            tactic_report report("ext_str", *g);
            fail_if_proof_generation("ext_str", g);
            m_produce_models      = g->models_enabled();
            m_fresh_vars.reset();
            if (m_produce_models)
                m_mc = alloc(generic_model_converter, m, "ext_str");
            else
                m_mc = nullptr;

            SASSERT(g->is_well_sorted());

            result.reset();

            TRACE("ext_str", tout << "BEFORE: " << std::endl; g->display(tout););

            if (g->inconsistent()) {
                result.push_back(g.get());
                return;
            }

            expr_substitution sub(m);

            unsigned idx = 0;
            while (idx < g->size()) {
                if (g->inconsistent())
                    break;
                expr * curr = g->form(idx);

                if (is_app(curr)) {
                    stack.reset();
                    stack.push_back(curr);
                    while (!stack.empty())
                    {
                        curr = stack.back();
                        stack.pop_back();
                        if (m.is_not(curr) || m.is_and(curr) || m.is_or(curr) || m.is_ite(curr) || m.is_iff(curr) || m.is_implies(curr))
                        {
                            process_logical_connective(curr, g, sub);
                        }
                        else if (m.is_eq(curr))
                        {
                            //possible not string equality
                            process_eq(curr, g, sub);
                        }
                        else if (u.str.is_concat(curr))
                        {
                            process_concat(curr, g, sub);
                        }
                        else if (u.str.is_prefix(curr))
                        {
                            process_prefix(curr, g, sub);
                        }
                        else if (u.str.is_suffix(curr))
                        {
                            process_suffix(curr, g, sub);
                        }
                        else if (u.str.is_contains(curr))
                        {
                            process_contains(curr, g, sub);
                        }
                        else if (u.str.is_extract(curr))
                        {
                            process_extract(curr, g, sub);
                        } 
                        else if (u.str.is_length(curr))
                        {
                            process_length(curr, g, sub);
                        }
                        else if (m_autil.is_add(curr) || m_autil.is_sub(curr) || m_autil.is_mul(curr))
                        {
                            process_arith_op(curr, g, sub);
                        }
                        else if (m_autil.is_ge(curr) || m_autil.is_gt(curr) || m_autil.is_le(curr) || m_autil.is_lt(curr))
                        {
                            process_arith_comparison(curr, g, sub);
                        }
                    }
                }
                idx++;
            }

            m_replace->set_substitution(&sub);

            for (unsigned i = 0; i < g->size(); i++) {            
                expr_ref   new_curr(m);
                proof_ref  new_pr(m);  
                (* m_replace)(g->form(i), new_curr, new_pr);
                if (m.proofs_enabled() && !new_pr) {
                    new_pr = m.mk_rewrite(g->form(i), new_curr);
                    new_pr = m.mk_modus_ponens(g->pr(i), new_pr);
                }
                g->update(i, new_curr, new_pr, g->dep(i));
            }

            if (m_mc) 
            {
                for (auto v: m_fresh_vars) {
                    m_mc->hide(to_app(v)->get_decl());
                }
            }

            if (m_produce_models && !m_fresh_vars.empty())
            {
                g->add(m_mc.get());
            }
            g->inc_depth();
            result.push_back(g.get());
            SASSERT(g->is_well_sorted());
            TRACE("ext_str", tout << "AFTER: " << std::endl; g->display(tout);
            if (g->mc()) g->mc()->display(tout); tout << std::endl; );
        }
    };

    imp *      m_imp;
    params_ref m_params;

public:

    ext_str_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(ext_str_tactic, m, m_params);
    }

    ~ext_str_tactic() override {
        dealloc(m_imp);
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
        m_imp->updt_params(p);
    }

    void operator()(goal_ref const & in,
                    goal_ref_buffer & result) override {
        try {
            (*m_imp)(in, result);
        }
        catch (rewriter_exception & ex) {
            throw tactic_exception(ex.msg());
        }
    }

    void cleanup() override {
        imp * d = alloc(imp, m_imp->m, m_params);
        std::swap(d, m_imp);        
        dealloc(d);
    }

};

tactic * mk_ext_str_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(ext_str_tactic, m, p));
}
