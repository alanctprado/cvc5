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
#include <sstream>
#include "prop/sat_solver_types.h"

namespace cvc5::internal {
namespace prop {

DratProofManager::DratProofManager(Env& env,
                                   CDCLTSatSolver* solver,
                                   CnfStream* cnfStream)
    : SatProofManager(env, cnfStream, nullptr),
      d_solver(solver)
{
  d_true = nodeManager()->mkConst(true);
  d_false = nodeManager()->mkConst(false);
}

std::shared_ptr<ProofNode> DratProofManager::getProof()
{
  CDProof cdp(d_env);
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> drat_steps;

  std::string line;
  while (std::getline(d_dratProof, line)) {
    Assert(line.length() > 0);

    bool is_deletion = line[0] == 'd';
    std::istringstream iss(line);
    if (is_deletion) iss.get();  // Removes 'd'

    std::vector<Node> literal_nodes;
    int cadical_lit;
    while(iss >> cadical_lit && cadical_lit != 0)
    {
      SatLiteral lit(std::abs(cadical_lit), cadical_lit < 0);
      literal_nodes.push_back(d_cnfStream->getNode(lit));
    }

    Node clause = nm->mkNode(Kind::OR, literal_nodes);
    /** A negated clause is used to represent a deletion */
    if (is_deletion) clause = nm->mkNode(Kind::NOT, clause);
    /**
     * NOTE: I was thinking of perhaps having Kinds like 'Kind::DRAT_ADDITION'
     * or 'Kind::DRAT_DELETION'. Then, we could have something like
     *
     * `clause = nm->mkNode(Kind::DRAT_DELETION, clause)`
     *
     * etc.
     */
    drat_steps.push_back(clause);
  }

  Node expected = nm->mkConst(false);
  Node assumptions = nm->mkNode(Kind::SEXPR, d_assumptions);
  Node input_formula = nm->mkNode(Kind::SEXPR, d_clauses);
  cdp.addStep(expected,
              ProofRule::DRAT_REFUTATION,
              drat_steps,
              {assumptions, input_formula});
  return cdp.getProofFor(expected);
}

void DratProofManager::setProofStream(std::string proof)
{
  d_dratProof.str(proof);
}

void DratProofManager::resetCnfStream(CnfStream* cnfStream)
{
  d_cnfStream = cnfStream;
}

void DratProofManager::registerSatClause(SatClause& clause)
{
  std::vector<Node> literal_nodes;
  for (SatLiteral lit : clause)
  {
    literal_nodes.push_back(d_cnfStream->getNode(lit));
  }
  Node clause_node = NodeManager::currentNM()->mkNode(Kind::OR, literal_nodes);
  d_clauses.emplace_back(clause_node);
}

void DratProofManager::registerSatLitAssumptions(const std::vector<SatLiteral>& a)
{
  d_assumptions.clear();
  for (SatLiteral lit : a)
  {
    d_assumptions.push_back(d_cnfStream->getNode(lit));
  }
}

void DratProofManager::registerSatAssumptions(const std::vector<Node>& a)
{
  Unimplemented();
}

}  // namespace prop
}  // namespace cvc5::internal
