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
 * Abstract SAT proof manager.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__SAT_PROOF_MANAGER_H
#define CVC5__PROP__SAT_PROOF_MANAGER_H

#include "proof/proof_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace prop {

class CnfStream;
class PropPfManager;

/**
 * This class is responsible for managing the proof production of a SAT
 * solver.
 */
class SatProofManager : protected EnvObj
{
 public:
  SatProofManager(Env& env, CnfStream* cnfStream, PropPfManager* ppm)
  : EnvObj(env), d_cnfStream(cnfStream), d_ppm(ppm) {}
  virtual ~SatProofManager() = default;

  /** Register a set clause inputs. */
  virtual void registerSatAssumptions(const std::vector<Node>& assumps) = 0;
  /** Retrive the unsatisfiability proof */
  virtual std::shared_ptr<ProofNode> getProof() = 0;

 protected:
  /** Pointer to the underlying cnf stream. */
  CnfStream* d_cnfStream;
  /** The prop proof manager */
  PropPfManager* d_ppm;

}; /* class SatProofManager */

}  // namespace prop
}  // namespace cvc5::internal

#endif /* CVC5__PROP__SAT_PROOF_MANAGER_H */
