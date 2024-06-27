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

#include "prop/drat_proof_manager.h"

namespace cvc5::internal {
namespace prop {

DratProofManager::DratProofManager(Env& env,
                                   CDCLTSatSolver* solver,
                                   CnfStream* cnfStream,
                                   PropPfManager* ppm)
    : SatProofManager<CDCLTSatSolver>(env, solver, cnfStream, ppm)
{
  d_true = nodeManager()->mkConst(true);
  d_false = nodeManager()->mkConst(false);
  // temporary, to allow this class to be notified when new clauses are added
  // see https://github.com/cvc5/cvc5-wishues/issues/149
  ppm->d_satPm = this;
}

std::shared_ptr<ProofNode> DratProofManager::getProof()
{
  return nullptr;
}

void DratProofManager::registerSatClause(SatClause& clause)
{
  d_clauses.emplace_back(clause);
}

void DratProofManager::registerSatLitAssumptions(const std::vector<SatLiteral>& a)
{
  d_assumptions.insert(d_assumptions.end(), a.begin(), a.end());
}

void DratProofManager::registerSatAssumptions(const std::vector<Node>& assumps)
{
  return;
}

}  // namespace prop
}  // namespace cvc5::internal
