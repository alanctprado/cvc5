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
 * PB-blasting solver. Supports RoundingSAT and Exact back-ends.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BV_SOLVER_PB_H
#define CVC5__THEORY__BV__BV_SOLVER_PB_H

#include <vector>

#include "context/cdqueue.h"
#include "theory/bv/bv_solver.h"
#include "theory/bv/pb/pb_solver.h"
#include "theory/bv/pb/pb_node_blaster.h"

namespace cvc5::internal {

namespace theory {
namespace bv {
namespace pb {

class NotifyResetAssertions;
class BBRegistrar;

/**
 * PB-blasting solver for the theory of bit-vectors
 */
class BVSolverPseudoBoolean : public BVSolver
{
 public:
  BVSolverPseudoBoolean(Env& env,
                        TheoryState* state,
                        TheoryInferenceManager& inferMgr);
  ~BVSolverPseudoBoolean() = default;

  /** TODO(alanctprado): document */
  bool needsEqualityEngine(EeSetupInfo& esi) override;

  /** TODO(alanctprado): document */
  void preRegisterTerm(TNode n) override {}  // same as BVSolverBitblast

  /** TODO(alanctprado): document */
  void postCheck(Theory::Effort level) override;

  /** TODO(alanctprado): document */
  bool preNotifyFact(TNode atom,
                     bool pol,
                     TNode fact,
                     bool isPrereg,
                     bool isInternal) override;

  /** TODO(alanctprado): document */
  TrustNode explain(TNode n) override;

  /** TODO(alanctprado): document */
  std::string identify() const override { return "BVSolverPseudoBoolean"; }

  /** TODO(alanctprado): document */
  void computeRelevantTerms(std::set<Node>& termSet) override;

  /** TODO(alanctprado): document */
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;

  /** TODO(alanctprado): document */
  Node getValue(TNode node, bool initialize) override;

 private:
  /** Initialize pseudo-boolean solver. */
  void initPbSolver();

  /** PB solver back end (configured via options::bvSatSolver. */
  std::unique_ptr<PbSolver<Node>> d_pbSolver;
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
