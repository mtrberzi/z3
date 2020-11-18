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
            ;);
        // feature indices:
        // 0 declare-const
        // 1 assert
        // 2 str.++
        // 3 str.len
        // 4 str.to_re
        // 5 str.in_re
        // 6 re.none
        // 7 re.all
        // 8 re.allchar
        // 9 re.++
        // 10 re.union
        // 11 re.inter
        // 12 re.*
        // 13 re.+
        // 14 str.at
        // 15 str.substr
        // 16 str.prefixof
        // 17 str.suffixof
        // 18 str.contains
        // 19 str.indexof
        // 20 str.replace
        // 21 str.to_int
        // 22 str.from_int

        // TODO declare-const, assert
        // TODO regex features

        double las_prediction = -4.00287151 * feature_declare_const + -1.23729158 * feature_assert + 1.83261321 * feature_concat + 2.28576847 * feature_strlen
            + 0.0 * feature_str_to_re + 0.0 * feature_regex_membership + 0.0 * feature_re_none + 0.0 * feature_re_all 
            + -1.32614556 * feature_re_allchar + -0.85299815 * feature_re_concat + -0.27100462 * feature_re_union
            + -0.03332024 * feature_re_inter + 0.59754297 * feature_re_star + 0.6752902 * feature_re_plus
            + -6.2131141 * feature_str_at + 7.9279958 * feature_substr
            + -16.1714232 * feature_prefixof + -1.6526839 * feature_suffixof + -1.83483456 * feature_contains
            + 5.3467879 * feature_indexof + 9.7983719 * feature_replace + 0.0 * feature_str_to_int + 0.0 * feature_int_to_str
            + -9.946056;

        double arr_prediction = -6.137588 * feature_declare_const + -6.293082 * feature_assert + 3.85848381 * feature_concat + 2.8211137 * feature_strlen
            + 0.0 * feature_str_to_re + 0.0 * feature_regex_membership + 0.0 * feature_re_none + 0.0 * feature_re_all 
            + -2.7789080 * feature_re_allchar + -0.8641049 * feature_re_concat + 0.5842149 * feature_re_union
            + -0.0177708 * feature_re_inter + 1.4505411 * feature_re_star + 1.099568 * feature_re_plus
            + -7.217164 * feature_str_at + 7.6036788 * feature_substr
            + -7.032792 * feature_prefixof + -1.0062713 * feature_suffixof + -7.012800 * feature_contains
            + 1.4816400 * feature_indexof + 6.233106 * feature_replace + 0.0 * feature_str_to_int + 0.0 * feature_int_to_str
            + -5.816511;

        double seq_prediction = -2.0436414 * feature_declare_const + -1.58826478 * feature_assert + 0.648634 * feature_concat + 5.3001395 * feature_strlen
            + 0.0 * feature_str_to_re + 0.0 * feature_regex_membership + 0.0 * feature_re_none + 0.0 * feature_re_all 
            + 0.037763 * feature_re_allchar + -0.69972504 * feature_re_concat + 0.2510125 * feature_re_union
            + -0.0333202 * feature_re_inter + 0.6397486 * feature_re_star + 1.1173387 * feature_re_plus
            + -51.0510506 * feature_str_at + 0.8085711 * feature_substr
            + -6.377494 * feature_prefixof + -0.72638123 * feature_suffixof + -18.4483063 * feature_contains
            + 1.208414 * feature_indexof + 10.9645803 * feature_replace + 0.0 * feature_str_to_int + 0.0 * feature_int_to_str
            + -9.18353;

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