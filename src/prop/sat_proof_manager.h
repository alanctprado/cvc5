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

template <class T>
class SatProofManager : protected EnvObj
{
 public:
  SatProofManager(Env& env, T* solver, CnfStream* cnfStream, PropPfManager* ppm)
  : EnvObj(env), d_solver(solver), d_cnfStream(cnfStream), d_ppm(ppm) {}

  /** Retrive the unsatisfiability proof */
  virtual std::shared_ptr<ProofNode> getProof() = 0;

 protected:
  /** The SAT solver to which we are managing proofs */
  T* d_solver;
  /** Pointer to the underlying cnf stream. */
  CnfStream* d_cnfStream;
  /** The prop proof manager */
  PropPfManager* d_ppm;
}; /* class SatProofManager */

}  // namespace prop
}  // namespace cvc5::internal

#endif /* CVC5__PROP__SAT_PROOF_MANAGER_H */
