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
 * Pb Solver.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__PB__PB_SOLVER_H
#define CVC5__THEORY__BV__PB__PB_SOLVER_H

#include "theory/bv/pb/pb_solver_types.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb {

template <class T>
class PbSolver {
public:
  /** Virtual destructor */
  virtual ~PbSolver() {}
  /** Add a variable to the solver. */
  virtual void addVariable(T variable) = 0;
  /** Assert a constraint to the solver. */
  virtual void addConstraint(T constraint) = 0;
  /** Check the satisfiability of the added clauses */
  virtual PbValue solve() = 0;
//  /** Call modelValue() when the search is done.*/
//  virtual PbValue modelValue(PbLiteral l) = 0;

 private:
  void init();
};

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif  // CVC5__THEORY__BV__PB__PB_SOLVER_H
