/******************************************************************************
 * Top contributors (to current version):
 *   Alan Prado
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * TODO(alanctprado)
 */

#include "theory/bv/pb/pb_proof_manager.h"
#include "proof/proof.h"
#include "util/string.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb{

PbProofManager::PbProofManager(Env& env, PbBlastProofGenerator* pbbpg)
    : EnvObj(env), d_pbbpg(pbbpg), d_proof(new CDProof(env))
{}

void PbProofManager::addPbProof(std::vector<std::string> proofLines)
{
  NodeManager* nm = NodeManager::currentNM();

  std::vector<Node> cutting_plane_steps;
  for (auto& line : proofLines)
  {
    Trace("bv-pb-proof") << line << "\n";
    cutting_plane_steps.push_back(processProofStep(line));
  }

  Node expected = nm->mkConst(false);
  std::vector<Node> children;

  d_proof->addStep(expected,
                   ProofRule::CUTTING_PLANES_REFUTATION,
                   children,
                   cutting_plane_steps);

  // The step above generates the following error:
  //
  // Fatal failure within cvc5::internal::ProofNodeManager* cvc5::internal::CDProof::getManager() const at /home/alan/logic/cvc5/src/proof/proof.cpp:454
  // Check failure

  // pnm != nullptr
}

Node PbProofManager::processProofStep(std::string step)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkConst(String(step));
}

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
