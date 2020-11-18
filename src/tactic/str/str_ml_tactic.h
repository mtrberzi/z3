/*
Module name:
    str_ml_tactic.h

Abstract:
    Machine learning tactic for string algorithm selection

Authors:
    Murphy Berzish
*/

#ifndef str_ml_tactic_H_
#define str_ml_tactic_H_

#include "util/params.h"
class ast_manager;
class tactic;

tactic* mk_str_ml_tactic(ast_manager& m, params_ref const& p, tactic * las, tactic * arr, tactic * seq);

/*
ADD_TACTIC("str_ml", "Use machine learning to select a string solving algorithm." "mk_str_mk_tactic(m, p)")
*/

#endif // !defined #define str_ml_tactic_H_
