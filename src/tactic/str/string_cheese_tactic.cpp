#include "tactic/tactical.h"
#include "tactic/str/string_cheese_tactic.h"
#include "ast/ast_pp.h"
#include "util/zstring.h"
#include <set>
#include "ast/rewriter/expr_replacer.h"
#include "ast/rewriter/var_subst.h"
#include "tactic/generic_model_converter.h"

const int MAX_STRING_VARIABLES = 3;

class string_cheese_tactic : public tactic {

    params_ref m_params;

    seq_util u;
    arith_util m_autil;

    scoped_ptr<expr_replacer> m_replace;

public:
    string_cheese_tactic(ast_manager& m, params_ref const& p):
    m_params(p), u(m), m_autil(m) {
        m_replace = mk_expr_simp_replacer(m);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(string_cheese_tactic, m, m_params);
    }

    ~string_cheese_tactic() override {}

    void updt_params(params_ref const& p) override {
        m_params = p;
    }

    bool is_string_var(expr * e, ast_manager & m) const {
        sort * ex_sort = e->get_sort();
        sort * str_sort = u.str.mk_string_sort();
        // non-string-sort terms cannot be string variables
        if (ex_sort != str_sort) return false;
        // string constants cannot be variables
        if (u.str.is_string(e)) return false;
        if (u.str.is_concat(e) || u.str.is_at(e) || u.str.is_extract(e) || u.str.is_replace(e) || u.str.is_itos(e))
            return false;
        if (m.is_ite(e))
            return false;
        return true;
    }

    void operator()(goal_ref const& g, goal_ref_buffer& result) override {
        SASSERT(g->is_well_formed());
        tactic_report report("string_cheese", *g);
        fail_if_proof_generation("string_cheese", g);

        result.reset();
        if (g->inconsistent()) {
            result.push_back(g.get());
            return;
        }
        ptr_vector<expr> stack;
        expr_ref_vector string_variables(g->m());
        std::set<zstring> string_constants;

        unsigned size = g->size();
        for (unsigned idx = 0; idx < size; ++idx) {
            expr * curr = g->form(idx);
            stack.push_back(curr);
        }
        result.reset();
        while (!stack.empty()) {
            expr * curr = stack.back();
            stack.pop_back();

            zstring str;
            if (u.str.is_string(curr, str)) {
                string_constants.insert(str);
            } else if (is_string_var(curr, g->m())) {
                bool duplicate = false;
                for (auto v: string_variables) {
                    if (g->m().are_equal(v, curr)) {
                        duplicate = true;
                        break;
                    }
                }
                if (!duplicate) {
                    string_variables.push_back(curr);
                    // abort if there are too many string variables
                    if (string_variables.size() > MAX_STRING_VARIABLES) {
                        break;
                    }
                }
            }
            // TODO give up if there are non-string variables

            // recursively check arguments
            unsigned n_args = to_app(curr)->get_num_args();
            for (unsigned idx = 0; idx < n_args; ++idx) {
                expr * e = to_app(curr)->get_arg(idx);
                stack.push_back(e);
            }
        }

        if (string_variables.size() > MAX_STRING_VARIABLES) {
            TRACE("str", tout << "too many variables for string cheese -- bailing out of tactic" << std::endl;);
            throw tactic_exception("string_cheese gave up due to too many variables");
        }

        TRACE("str", tout << "found string constants:" << std::endl; for(auto str : string_constants){tout << "\"" << str << "\"" << std::endl;});
        TRACE("str", tout << "found string variables:" << std::endl; for (auto e : string_variables){tout << mk_pp(e, g->m()) << std::endl;});

        expr_substitution sub(g->m());
        // construct the set of all string solutions we want to try
        expr_ref_vector candidate_solutions(g->m());
        {
            expr_ref empty(u.str.mk_string(zstring("")), g->m());
            candidate_solutions.push_back(empty);
            // construct an initial substitution
            for (auto v : string_variables) {
                sub.insert(v, empty);
            }
        }
        for (auto str : string_constants) {
            candidate_solutions.push_back(expr_ref(u.str.mk_string(str), g->m()));
        }
        for (auto s1 : string_constants) {
            for (auto s2 : string_constants) {
                zstring str = s1 + s2;
                candidate_solutions.push_back(expr_ref(u.str.mk_string(str), g->m()));
            }
        }

        // now try every possible solution
        for (auto v : string_variables) {
            for (auto str : candidate_solutions) {
                sub.insert(v, str);
                m_replace->set_substitution(&sub);
                bool valid = true;
                for (unsigned i = 0; i < g->size(); ++i) {
                    expr_ref curr(g->form(i), g->m());
                    expr_ref new_curr(g->m());
                    proof_ref new_pr(g->m());
                    (*m_replace)(curr, new_curr, new_pr);
                    TRACE("str", tout << "substituted/replaced: " << mk_pp(new_curr, g->m()) << std::endl;);
                    if (!g->m().is_true(new_curr)) {
                        valid = false;
                        break;
                    }
                }
                if (valid) {
                    g->reset();
                    if (g->models_enabled()) {
                        generic_model_converter * m_mc = alloc(generic_model_converter, g->m(), "string_cheese");
                        for (auto entry : sub.sub()) {
                            m_mc->add(to_app(entry.m_key), entry.m_value);
                        }
                        g->add(m_mc);
                        result.push_back(g.get());
                    } else {
                        result.push_back(g.get());
                    }
                    return;
                }
            }
        }
        
        throw tactic_exception("string_cheese inconclusive");
    }

    void cleanup() override {}
};

tactic * mk_string_cheese_tactic(ast_manager & m, params_ref const& p) {
    return clean(alloc(string_cheese_tactic, m, p));
}
