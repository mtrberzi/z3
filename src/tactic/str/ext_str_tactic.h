/*++

Module Name:

    ext_str_tactic.h

Abstract:

    Tactic that eliminates substring expressions

Author:

    Federico Mora (FedericoAureliano) 2019-06-06

Notes:

--*/
#ifndef ext_str_tactic_H_
#define ext_str_tactic_H_

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_ext_str_tactic(ast_manager & m, params_ref const & p);
/*
  ADD_TACTIC("substr", "eliminate substr expressions.", "mk_ext_str_tactic(m, p)")
*/

#endif
