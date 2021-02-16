/*
Module name:
    string_cheese_tactic.h

Abstract:
    A "cheese" tactic for strings.
    Under certain circumstances, uses string constants in the input formula
    to guess and check easy solutions.

Authors:
    Murphy Berzish
*/

#ifndef string_cheese_tactic_H_
#define string_cheese_tactic_H_

#include "util/params.h"
class ast_manager;
class tactic;

tactic* mk_string_cheese_tactic(ast_manager& m, params_ref const& p);

/*
ADD_TACTIC("string_cheese", "Use string constants in the input formula to guess and check easy solutions.", "mk_string_cheese_tactic(m, p)")
*/

#endif // !defined #define string_cheese_tactic_H_
