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

// return the new expression, keep track of fresh variables used to ignore them in the model, add new assertions to side.
static expr * ext_str_helper(ast_manager &m, expr_ref_vector & fresh, expr * curr, expr_ref_vector & side)
{
    seq_util u(m);
    arith_util m_autil(m);

    TRACE("ext_str_debug", tout << "curr " << mk_pp(curr, m) << std::endl;);

    if (m.is_not(curr))
    {
        expr * child;
        m.is_not(curr, child);
        TRACE("ext_str_debug", tout << "curr " << mk_pp(curr, m) << std::endl;);
        return m.mk_not(ext_str_helper(m , fresh, child, side));
    }
    else if (m.is_and(curr)) 
    {
        expr * lhs, * rhs;
        m.is_and(curr, lhs, rhs);
        TRACE("ext_str_debug", tout << "curr " << mk_pp(curr, m) << std::endl;);
        return m.mk_and(ext_str_helper(m , fresh, lhs, side), ext_str_helper(m , fresh, rhs, side));
    }
    else if (m.is_or(curr)) 
    {
        expr * lhs, * rhs;
        m.is_or(curr, lhs, rhs);
        TRACE("ext_str_debug", tout << "curr " << mk_pp(curr, m) << std::endl;);
        return m.mk_or(ext_str_helper(m , fresh, lhs, side), ext_str_helper(m , fresh, rhs, side));
    }
    else if (m.is_ite(curr)) 
    {
        expr * cond, * lhs, * rhs;
        m.is_ite(curr, cond, lhs, rhs);
        TRACE("ext_str_debug", tout << "curr " << mk_pp(curr, m) << std::endl;);
        return m.mk_ite(ext_str_helper(m , fresh, cond, side), ext_str_helper(m , fresh, lhs, side), ext_str_helper(m , fresh, rhs, side));
    }
    else if (m.is_implies(curr)) 
    {
        expr * lhs, * rhs;
        m.is_implies(curr, lhs, rhs);
        TRACE("ext_str_debug", tout << "curr " << mk_pp(curr, m) << std::endl;);
        return m.mk_implies(ext_str_helper(m , fresh, lhs, side), ext_str_helper(m , fresh, rhs, side));
    }    
    else if (m.is_iff(curr)) 
    {
        expr * lhs, * rhs;
        m.is_iff(curr, lhs, rhs);
        TRACE("ext_str_debug", tout << "curr " << mk_pp(curr, m) << std::endl;);
        return m.mk_iff(ext_str_helper(m , fresh, lhs, side), ext_str_helper(m , fresh, rhs, side));
    }
    else if (m.is_eq(curr))
    {
        expr * lhs, * rhs;
        m.is_eq(curr, lhs, rhs);
        TRACE("ext_str_debug", tout << "curr " << mk_pp(curr, m) << std::endl;);
        return m.mk_eq(ext_str_helper(m , fresh, lhs, side), ext_str_helper(m , fresh, rhs, side));
    }
    else if (u.str.is_concat(curr))
    {
        expr * lhs, * rhs;
        u.str.is_concat(curr, lhs, rhs);
        TRACE("ext_str_debug", tout << "curr " << mk_pp(curr, m) << std::endl;);
        return u.str.mk_concat(ext_str_helper(m , fresh, lhs, side), ext_str_helper(m , fresh, rhs, side));
    }
    else if (u.str.is_prefix(curr))
    {
        expr * needle, * haystack;
        u.str.is_prefix(curr, needle, haystack);
        TRACE("ext_str_debug", tout << "curr " << mk_pp(curr, m) << std::endl;);
        return u.str.mk_prefix(ext_str_helper(m , fresh, needle, side), ext_str_helper(m , fresh, haystack, side));
    }
    else if (u.str.is_suffix(curr))
    {
        expr * needle, * haystack;
        u.str.is_suffix(curr, needle, haystack);
        TRACE("ext_str_debug", tout << "curr " << mk_pp(curr, m) << std::endl;);
        return u.str.mk_suffix(ext_str_helper(m , fresh, needle, side), ext_str_helper(m , fresh, haystack, side));
    }
    else if (u.str.is_contains(curr))
    {
        expr * needle, * haystack;
        u.str.is_contains(curr, haystack, needle);
        TRACE("ext_str_debug", tout << "curr " << mk_pp(curr, m) << std::endl;);
        return u.str.mk_contains(ext_str_helper(m , fresh, haystack, side), ext_str_helper(m , fresh, needle, side));
    }
    else if (u.str.is_extract(curr))
    {
        expr * y, *n, *l;
        u.str.is_extract(curr, y, n, l);
        // make a fresh string variable and put it in place of the ext_string
        app * v;
        v = m.mk_fresh_const(nullptr, u.str.mk_string_sort());
        fresh.push_back(v);
        expr_ref x(v, m);

        // inject auxiliary lemma
        v = m.mk_fresh_const(nullptr, u.str.mk_string_sort());
        fresh.push_back(v);
        expr_ref z1(v, m);
        v = m.mk_fresh_const(nullptr, u.str.mk_string_sort());
        fresh.push_back(v);
        expr_ref z2(v, m);

        expr_ref zero(m_autil.mk_numeral(rational(0), true), m);
        symbol sym("");
        expr_ref empty_str(u.str.mk_string(sym), m);
        expr_ref len_y(u.str.mk_length(y), m);
        expr_ref len_z1(u.str.mk_length(z1), m);

        expr_ref cond(m.mk_and(m_autil.mk_ge(n, zero), m_autil.mk_ge(n, zero), m_autil.mk_gt(m_autil.mk_add(n, len_y), zero)), m);
        expr_ref then(m.mk_and(m.mk_eq(y, u.str.mk_concat(z1, x, z2)), m.mk_eq(len_z1, n)), m);
        expr_ref el(m.mk_eq(x, empty_str), m);

        TRACE("ext_str_debug", tout << "if " << mk_pp(cond, m) << std::endl;);
        TRACE("ext_str_debug", tout << "then " << mk_pp(then, m) << std::endl;);
        TRACE("ext_str_debug", tout << "else " << mk_pp(el, m) << std::endl;);

        side.push_back(m.mk_ite(cond, then, el));

        TRACE("ext_str_debug", tout << "curr replaced by: " << mk_pp(x, m) << std::endl;);
        return x;
    } 
    else if (u.str.is_length(curr))
    {
        expr * child;
        u.str.is_length(curr, child);
        TRACE("ext_str_debug", tout << "curr " << mk_pp(curr, m) << std::endl;);
        return u.str.mk_length(ext_str_helper(m , fresh, child, side));
    }
    else if (m_autil.is_add(curr))
    {
        expr * lhs, * rhs;
        m_autil.is_add(curr, lhs, rhs);
        TRACE("ext_str_debug", tout << "curr " << mk_pp(curr, m) << std::endl;);
        return m_autil.mk_add(ext_str_helper(m , fresh, lhs, side), ext_str_helper(m , fresh, rhs, side));
    }
    
    TRACE("ext_str_debug", tout << "curr " << mk_pp(curr, m) << std::endl;);
    return curr;
}


class ext_str_tactic : public tactic {
    struct imp {

        typedef generic_model_converter mc;

        ast_manager &     m;
        seq_util          u;
        expr_ref_vector   m_fresh_vars;
        ref<mc>           m_mc;
        bool              m_produce_models;

        imp(ast_manager & _m, params_ref const & p):
            m(_m),
            u(m),
            m_fresh_vars(m) {
            updt_params(p);
        }

        void updt_params(params_ref const & p) {

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

            expr_ref_vector side(m);
            unsigned idx = 0;
            while (idx < g->size()) {
                if (g->inconsistent())
                    break;
                expr_ref curr(g->form(idx), m);
                TRACE("ext_str_debug", tout << "curr " << mk_pp(curr, m) << std::endl;);

                if (is_app(curr)) {
                    side.reset();
                    expr_ref new_curr(ext_str_helper(m, m_fresh_vars, curr, side), m);
                    TRACE("ext_str_debug", tout << "curr replaced by: " << mk_pp(new_curr, m) << std::endl;);
                    g->update(idx, new_curr);
                    for (expr * e : side)
                    {
                        TRACE("ext_str_debug", tout << "asserting: " << mk_pp(e, m) << std::endl;);
                        g->assert_expr(e);
                    }
                }
                idx++;
                TRACE("ext_str_debug", tout << "curr " << mk_pp(curr, m) << std::endl;);
            }

            if (m_mc) 
            {
                for (auto v: m_fresh_vars) {
                    m_mc->hide(to_app(v)->get_decl());
                }
            }

            if (m_produce_models && !m_fresh_vars.empty()) 
                g->add(m_mc.get());
            g->inc_depth();
            result.push_back(g.get());
            SASSERT(g->is_well_sorted());
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
