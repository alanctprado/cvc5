/******************************************************************************
 * Top contributors (to current version):
 *   Alan Prado
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * PB Solver types.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__PB_SOLVER_TYPES_H
#define CVC5__THEORY__BV__PB_SOLVER_TYPES_H

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb {

/**
 * A ConstraintId should be a shared identifier between the proofs module and
 * the PB solver for a clause. TODO: implement it in `proof/constraint_id.h`
 */
typedef unsigned ConstraintId;

/**
 * Possible states of the PB solver.
 */
enum PbSolveState {
  PB_UNKNOWN,
  PB_SAT,
  PB_UNSAT
};

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif  // CVC5__THEORY__BV__PB_SOLVER_TYPES_H
