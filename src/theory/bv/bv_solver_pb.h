/******************************************************************************
 * Top contributors (to current version):
 *   Alan Prado, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * PB-blasting solver that currently supports no PB-solver :'-)
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BV_SOLVER_PB_H
#define CVC5__THEORY__BV__BV_SOLVER_PB_H

#include <vector>

#include "context/cdqueue.h"
#include "theory/bv/bv_solver.h"
#include "theory/bv/pb/pb_node_blaster.h"

namespace cvc5::internal {

namespace theory {
namespace bv {
namespace pb {

class NotifyResetAssertions;
class BBRegistrar;

/**
 * PB-blasting solver
 */
class BVSolverPseudoBoolean : public BVSolver
{
 public:
  BVSolverPseudoBoolean(Env& env,
                        TheoryState* state,
                        TheoryInferenceManager& inferMgr);
  ~BVSolverPseudoBoolean() = default;

  void postCheck(Theory::Effort level) override;
  bool preNotifyFact(TNode atom,
                     bool pol,
                     TNode fact,
                     bool isPrereg,
                     bool isInternal) override;

  /** TODO: understant these */
  std::string identify() const override { return "BVSolverPseudoBoolean"; }
  void preRegisterTerm(TNode n) override {}
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override
  {
    return 1;
  }

 private:
  /** Initialize pseudo-boolean solver. */
  void initPbSolver();
  /**
   * Transform the node representation of a constraint to the OPB string that
   * represents the same constraint;
   */
  std::string constraintToStringOPB(Node constraint,
                                    std::unordered_set<Node>& variables);
  /** Write PB problem in OPB format */
  void convertProblemOPB(std::vector<Node> problem);
  /** Bit-blaster used to bit-blast atoms/terms. */
  std::unique_ptr<PseudoBooleanBlaster> d_pbBlaster;
  /**
   * PB-blast queue for facts sent to this solver.
   * Gets populated on preNotifyFact().
   */
  context::CDQueue<Node> d_facts;
};

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif
