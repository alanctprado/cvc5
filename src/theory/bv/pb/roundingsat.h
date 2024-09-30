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
 * Wrapper for the RoundingSat PB Solver for cvc5 (bit-vectors).
 *
 */

#include "cvc5_private.h"

#ifdef CVC5_USE_ROUNDINGSAT

#ifndef CVC5__THEORY__BV__PB__ROUNDINGSAT_H
#define CVC5__THEORY__BV__PB__ROUNDINGSAT_H

#include "theory/bv/pb/pb_solver.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb {

class RoundingSatSolver : public PbSolver<Node>, protected EnvObj
{
  // friend class PbSolverFactory;

 public:
  ~RoundingSatSolver() override = default;

  /* ExactSolver interface -------------------------------------------------- */
  void addConstraint(Node) override;
  void addVariable(Node) override;
  PbSolveState solve() override;

// private:   TODO: should the constructor be private (factory)?
  /**
   * Constructor.
   * Private to disallow creation outside of PbSolverFactory.
   * Function init() must be called after creation.
   * @param env       The associated environment.
   * @param registry  The associated statistics registry.
   * @param name      The name of the PB solver.
   * @param logProofs Whether to log proofs
   */
  RoundingSatSolver(std::string solverPath,
                    Env& env,
                    StatisticsRegistry& registry,
                    const std::string& name = "",
                    bool logProofs = false);
 private:
  /**
   * Initialize PB solver instance.
   * Note: Split out to not call virtual functions in constructor.
   */
  void init();

  std::string d_binPath;

  /** Whether we are logging proofs */
  bool d_logProofs;

  /** TODO: implement statistics */
  struct Statistics
  {
    Statistics(StatisticsRegistry& registry, const std::string& prefix);
  };
  Statistics d_statistics;

  /** Set of variables already in the solver */
  std::unordered_set<Node> d_variableSet;

  /** Set of constraints already in the solver */
  std::unordered_set<Node> d_constraintSet;

  std::vector<std::string> d_opbConstraints;

  /** Tmp File */
  std::fstream d_pboFile;
  std::string d_pboPath;
};

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif  // CVC5__THEORY__BV__PB__ROUDNINGSAT_H
#endif  // CVC5_USE_ROUDNINGSAT
