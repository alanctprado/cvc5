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
 * TODO: description
 */

#include "cvc5_private.h"
#include "prop/sat_solver_types.h"

#ifndef CVC5__PROP__DRAT_PROOF_MANAGER_H
#define CVC5__PROP__DRAT_PROOF_MANAGER_H

#include "prop/sat_proof_manager.h"
#include "prop/sat_solver.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace prop {

class CnfStream;
class PropPfManager;

/**
 * This class is responsible for managing the proof production of a SAT * solver
 * that generates a DRAT proof.
 *
 * TODO: describe a DRAT proof.
 *
 * Is this class is specific to CaDiCaL?
 */
class DratProofManager : public SatProofManager<CDCLTSatSolver>
{
 public:
  DratProofManager(Env& env,
                   CDCLTSatSolver* solver,
                   CnfStream* cnfStream,
                   PropPfManager* ppm);

  /** Retrive the DRAT proof */
  std::shared_ptr<ProofNode> getProof() override;

  /** Register a clause input, converted to its node representation. */
  void registerSatClause(SatClause& clause);
  /** Register a set of assumptions. */
  void registerSatLitAssumptions(const std::vector<SatLiteral>& assumps);

  void registerSatAssumptions(const std::vector<Node>& assumps) override;

 private:
  /** The true/false nodes */
  Node d_true;
  Node d_false;

  /**
   * Stores the current set of clauses provided to the solver via solve(). Used
   * to generate the antecedents of a proof.
   */
  std::vector<SatLiteral> d_assumptions;
  /**
   * Stores the current set of clauses provided to the solver via addClause().
   * Used to generate the antecedents of a proof.
   */
  std::vector<SatClause> d_clauses;

}; /* class DratProofManager */

}  // namespace prop
}  // namespace cvc5::internal

#endif /* CVC5__PROP__DRAT_PROOF_MANAGER_H */
