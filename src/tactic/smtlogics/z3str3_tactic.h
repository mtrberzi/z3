/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    z3str3_tactic.h

Abstract:

    Tactic for string instances that synergizes with Z3str3

Author:

    Murphy Berzish (mtrberzi) 2019-01-10

Notes:

--*/
#ifndef Z3STR3_TACTIC_H_
#define Z3STR3_TACTIC_H_

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_z3str3_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("z3str3",  "use z3str3 tricks to solve string problems.", "mk_z3str3_tactic(m, p)")
*/


#endif
