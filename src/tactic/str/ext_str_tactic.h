/*
Module name:
    ext_str_tactic.h

Abstract:
    Tactic that performs global formula rewriting on string terms for extended constraints

Authors:
    Federico Mora and Murphy Berzish
*/

#ifndef ext_str_tactic_H_
#define ext_str_tactic_H_

#include "util/params.h"
class ast_manager;
class tactic;

tactic* mk_ext_str_tactic(ast_manager& m, params_ref const& p);

/*
ADD_TACTIC("ext_str", "Rewrite and eliminate extended string constraints.", "mk_ext_str_tactic(m, p)")
*/

#endif // !defined ext_str_tactic_H_
