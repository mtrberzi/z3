/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    theory_seq_params.cpp

Abstract:

    Parameters for sequence theory plugin

Revision History:


--*/

#include "smt/params/theory_seq_params.h"
#include "smt/params/smt_params_helper.hpp"

void theory_seq_params::updt_params(params_ref const & _p) {
    smt_params_helper p(_p);
    m_split_w_len = p.seq_split_w_len();
    m_multiset_check = p.seq_multiset_check();
    m_length_based_word_solving = p.seq_length_based_word_solving();
    m_max_length_based_solving_length = p.seq_max_length_based_solving_length();
}
