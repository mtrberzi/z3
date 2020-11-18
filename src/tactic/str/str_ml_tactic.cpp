#include "tactic/tactical.h"
#include "tactic/str/str_ml_tactic.h"
#include "ast/ast_pp.h"

class str_ml_tactic : public tactic {

    params_ref m_params;
    tactic * las_tactic;
    tactic * arr_tactic;
    tactic * seq_tactic;

    seq_util u;
    arith_util m_autil;

    unsigned feature_concat;
    unsigned feature_substr;
    unsigned feature_str_at;
    unsigned feature_contains;
    unsigned feature_regex_membership;
    unsigned feature_strlen;
    unsigned feature_indexof;
    unsigned feature_replace;
    unsigned feature_prefixof;
    unsigned feature_suffixof;
    unsigned feature_str_to_int;
    unsigned feature_int_to_str;
    unsigned feature_declare_const;
    unsigned feature_assert;
    unsigned feature_str_to_re;
    unsigned feature_re_none;
    unsigned feature_re_all;
    unsigned feature_re_allchar;
    unsigned feature_re_concat;
    unsigned feature_re_union;
    unsigned feature_re_inter;
    unsigned feature_re_star;
    unsigned feature_re_plus;
    

public:
    str_ml_tactic(ast_manager& m, params_ref const& p, tactic * las, tactic * arr, tactic * seq) :
        m_params(p), las_tactic(las), arr_tactic(arr), seq_tactic(seq), u(m), m_autil(m),
        feature_concat(0), feature_substr(0), feature_str_at(0), feature_contains(0), feature_regex_membership(0),
        feature_strlen(0), feature_indexof(0), feature_replace(0), feature_prefixof(0), feature_suffixof(0),
        feature_str_to_int(0), feature_int_to_str(0), feature_declare_const(0), feature_assert(0),
        feature_str_to_re(0), feature_re_none(0), feature_re_all(0), feature_re_allchar(0),
        feature_re_concat(0), feature_re_union(0), feature_re_inter(0), feature_re_star(0), feature_re_plus(0) {
    }

    tactic* translate(ast_manager& m) override {
        tactic * new_las = las_tactic->translate(m);
        tactic * new_arr = arr_tactic->translate(m);
        tactic * new_seq = seq_tactic->translate(m);
        return alloc(str_ml_tactic, m, m_params, new_las, new_arr, new_seq);
    }

    ~str_ml_tactic() override {
        
    }

    void updt_params(params_ref const& p) override {
        m_params = p;
    }

    void operator()(goal_ref const& g, goal_ref_buffer& result) override {
        SASSERT(g->is_well_formed());
        tactic_report report("str_ml", *g);
        result.reset();
        if (g->inconsistent()) {
            result.push_back(g.get());
            return;
        }
        ptr_vector<expr> stack;

        unsigned size = g->size();
        feature_assert = size;
        for (unsigned idx = 0; idx < size; ++idx) {
            expr * curr = g->form(idx);
            stack.push_back(curr);
        }
        while (!stack.empty()) {
            expr * curr = stack.back();
            stack.pop_back();
            if (!is_app(curr)) continue;
            if (u.str.is_concat(curr)) {
                feature_concat++;
            } else if (u.str.is_extract(curr)) {
                feature_substr++;
            } else if (u.str.is_at(curr)) {
                feature_str_at++;
            } else if (u.str.is_contains(curr)) {
                feature_contains++;
            } else if (u.str.is_in_re(curr)) {
                feature_regex_membership++;
            } else if (u.str.is_length(curr)) {
                feature_strlen++;
            } else if (u.str.is_index(curr)) {
                feature_indexof++;
            } else if (u.str.is_replace(curr)) {
                feature_replace++;
            } else if (u.str.is_prefix(curr)) {
                feature_prefixof++;
            } else if (u.str.is_suffix(curr)) {
                feature_suffixof++;
            } else if (u.str.is_itos(curr)) {
                feature_int_to_str++;
            } else if (u.str.is_stoi(curr)) {
                feature_str_to_int++;
            } else if (u.re.is_to_re(curr)) {
                feature_str_to_re++;
            } else if (u.re.is_concat(curr)) {
                feature_re_concat++;
            } else if (u.re.is_union(curr)) {
                feature_re_union++;
            } else if (u.re.is_intersection(curr)) {
                feature_re_inter++;
            } else if (u.re.is_star(curr)) {
                feature_re_star++;
            } else if (u.re.is_plus(curr)) {
                feature_re_plus++;
            } else if (u.re.is_empty(curr)) {
                feature_re_none++;
            } else if (u.re.is_full_char(curr)) {
                feature_re_allchar++;
            } else if (u.re.is_full_seq(curr)) {
                feature_re_all++;
            }
            // recursively check arguments
            unsigned n_args = to_app(curr)->get_num_args();
            for (unsigned idx = 0; idx < n_args; ++idx) {
                expr * e = to_app(curr)->get_arg(idx);
                stack.push_back(e);
            }
        }
        TRACE("str_ml_tactic", tout
            << "Feature count:" << std::endl
            << "assertions: " << feature_assert << std::endl
            << "concat: " << feature_concat << std::endl
            << "substr: " << feature_substr << std::endl
            << "str.at: " << feature_str_at << std::endl
            << "contains: " << feature_contains << std::endl
            << "str.in.re: " << feature_regex_membership << std::endl
            << "str.len: " << feature_strlen << std::endl
            << "indexof: " << feature_indexof << std::endl
            << "replace: " << feature_replace << std::endl
            << "prefixof: " << feature_prefixof << std::endl
            << "suffixof: " << feature_suffixof << std::endl
            << "str.to_int: " << feature_str_to_int << std::endl
            << "str.from_int: " << feature_int_to_str << std::endl
            << "str.to_re: " << feature_str_to_re << std::endl
            << "re.++: " << feature_re_concat << std::endl
            << "re.union: " << feature_re_union << std::endl
            << "re.inter: " << feature_re_inter << std::endl
            << "re.*: " << feature_re_star << std::endl
            << "re.+: " << feature_re_plus << std::endl
            << "re.none: " << feature_re_none << std::endl
            << "re.allchar: " << feature_re_allchar << std::endl
            << "re.all: " << feature_re_all << std::endl
            ;);

        // TODO declare-const

        double las_prediction = -12.183755502422986 + -3.1254385225360104 * feature_declare_const + 0.05331238417912233 * feature_assert + 1.328366905811407 * feature_concat + -0.7174958370853266 * feature_strlen + -0.4087282787110762 * feature_str_to_re + -2.390171890723547 * feature_regex_membership + 0.0 * feature_re_none + 0.0 * feature_re_all + -1.9392379745374149 * feature_re_allchar + 0.8907610856695246 * feature_re_concat + -1.6082569227549446 * feature_re_union + -0.05109103483890132 * feature_re_inter + 0.8685475922613429 * feature_re_star + 0.1044034190185983 * feature_re_plus + -1.7370951845224845 * feature_str_at + 1.2306275348152365 * feature_substr + -16.05147033677781 * feature_prefixof + -0.9462948191900853 * feature_suffixof + 0.3754080385988988 * feature_contains + 2.1458234632341577 * feature_indexof + 3.5363881505884454 * feature_replace + 0.0 * feature_str_to_int + 0.0 * feature_int_to_str;
        double arr_prediction = -6.9593011001349465 + -3.30981051782431 * feature_declare_const + -1.9170244811295871 * feature_assert + 2.1391594152113678 * feature_concat + 8.01240707234446 * feature_strlen + -1.28171856965401 * feature_str_to_re + -2.401278637427879 * feature_regex_membership + 0.0 * feature_re_none + 0.0 * feature_re_all + -3.1232171731954117 * feature_re_allchar + 0.7263812344487794 * feature_re_concat + -0.970729661939115 * feature_re_union + -0.042205637475614004 * feature_re_inter + 1.228406185474505 * feature_re_star + 0.3731866892580719 * feature_re_plus + -1.479418660987267 * feature_str_at + 11.517696332160934 * feature_substr + -7.006135820951969 * feature_prefixof + -0.7974644133550233 * feature_suffixof + -3.7629657833519623 * feature_contains + 1.586043429347055 * feature_indexof + 0.8707689416021043 * feature_replace + 0.0 * feature_str_to_int + 0.0 * feature_int_to_str;
        double seq_prediction = -8.24059060924262 + -0.2732259689210663 * feature_declare_const + -0.031098890771779873 * feature_assert + 0.23102033144547796 * feature_concat + 3.3609015526634014 * feature_strlen + -0.35541589453142247 * feature_str_to_re + -11.593222209746793 * feature_regex_membership + 0.0 * feature_re_none + 0.0 * feature_re_all + 2.116945921803152 * feature_re_allchar + 0.9462948191900786 * feature_re_concat + -0.6508553568607838 * feature_re_union + 0.0 * feature_re_inter + 0.07552587758792148 * feature_re_star + 0.37985073728052765 * feature_re_plus + -51.49976311761577 * feature_str_at + -3.4675263210228686 * feature_substr + -6.641834529057203 * feature_prefixof + -0.5109103483890111 * feature_suffixof + -17.113275321691553 * feature_contains + 4.3649514547146975 * feature_indexof + 3.0876755837423873 * feature_replace + 0.0 * feature_str_to_int + 0.0 * feature_int_to_str;

        TRACE("str_ml_tactic", tout
            << "LAS prediction: " << las_prediction << std::endl
            << "ARR prediction: " << arr_prediction << std::endl
            << "SEQ prediction: " << seq_prediction << std::endl
            ;);

        tactic * t = nullptr;
        if (las_prediction <= 0.0) {
            // LAS will be fast, always use it first
            if (seq_prediction <= arr_prediction) {
                TRACE("str_ml_tactic", tout << "tactic order: LAS -> SEQ -> ARR" << std::endl;);
                t = and_then(las_tactic, seq_tactic, arr_tactic);
            } else {
                TRACE("str_ml_tactic", tout << "tactic order: LAS -> ARR -> SEQ" << std::endl;);
                t = and_then(las_tactic, arr_tactic, seq_tactic);
            }
        } else {
            // LAS will be slow, do not use it first
            if (seq_prediction <= arr_prediction) {
                TRACE("str_ml_tactic", tout << "tactic order: SEQ -> ARR" << std::endl;);
                t = and_then(seq_tactic, arr_tactic);              
            } else {
                TRACE("str_ml_tactic", tout << "tactic order: ARR -> SEQ" << std::endl;);
                t = and_then(arr_tactic, seq_tactic);           
            }
        }
        t->operator()(g, result);
    }

    void cleanup() override {

    }
};


tactic * mk_str_ml_tactic(ast_manager & m, params_ref const & p, tactic * las, tactic * arr, tactic * seq) {
    return clean(alloc(str_ml_tactic, m, p, las, arr, seq));
}