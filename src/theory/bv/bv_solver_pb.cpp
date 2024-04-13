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

#include "theory/bv/bv_solver_pb.h"

#include <sstream>
#include <unordered_set>
#include "options/bv_options.h"
#include "theory/bv/theory_bv.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb {

BVSolverPseudoBoolean::BVSolverPseudoBoolean(Env& env,
                                             TheoryState* s,
                                             TheoryInferenceManager& inferMgr)
    : BVSolver(env, *s, inferMgr),
      d_pbBlaster(new PseudoBooleanBlaster(env, s)),
      d_facts(context()),
      d_factConstraintCache(context())
{
  Trace("bv-pb") << "Built BVSolverPseudoBoolean\n";
  initPbSolver();
}

void BVSolverPseudoBoolean::postCheck(Theory::Effort level)
{
  Trace("bv-pb") << "Post check with effort level " << level << "\n";
  if (level != Theory::Effort::EFFORT_FULL) { return; }
  Variables problem_variables;
  Constraints problem_constraints;
  /** Process PB-blast queue and generate sets of variables and constraints. */
  while (!d_facts.empty())
  {
    Node fact = d_facts.front();
    d_facts.pop();
    PbResult result;  // Variables and constraints of the current fact.
    if (d_factConstraintCache.find(fact) == d_factConstraintCache.end())
    {
      if (fact.getKind() == Kind::BITVECTOR_EAGER_ATOM) { Unhandled(); }
      else
      {
        d_pbBlaster->blastAtom(fact);
        result = d_pbBlaster->getStoredAtom(fact);
        d_factConstraintCache[fact] = result;
      }
    }
    else { result = d_factConstraintCache[fact]; }
    for (unsigned v : result.first) { problem_variables.insert(v); }
    for (std::string c : result.second) { problem_constraints.insert(c); }
  }
  writeProblem(problem_variables, problem_constraints);
}

void BVSolverPseudoBoolean::writeProblem(Variables variables,
                                         Constraints constraints)
{
  std::ostringstream opb_file;
  opb_file << "* #variable= " << variables.size();
  opb_file << " #constraint= " << constraints.size() << "\n";
  for (std::string constraint : constraints) { opb_file << constraint; }
  Trace("bv-pb-opb") << opb_file.str();
}

bool BVSolverPseudoBoolean::preNotifyFact(TNode atom, bool pol, TNode fact,
                                          bool isPrereg, bool isInternal)
{
  Trace("bv-pb") << "Adding fact: " << fact << std::endl;
  /**
   * Check whether `fact` is an input assertion on user-level 0.
   *
   * Not really sure if this should be handled. I'm confident we concluded it
   * won't happen. We don't care about other theories?
   */
  Valuation& val = d_state.getValuation();
  if (options().bv.bvAssertInput && val.isFixed(fact)) { Unhandled(); }
  d_facts.push_back(fact);
  /**
   * Return false to enable equality engine reasoning in Theory, which is
   * available if we are using the equality engine. I don't think it is our
   * case.
   */
  return 1; 
}

void BVSolverPseudoBoolean::initPbSolver()
{
  switch(options().bv.bvPbSolver)
  {
    case options::BvPbSolverMode::ROUNDINGSAT:
      Trace("bv-pb") << "TO-DO: initialize RoundingSAT" << std::endl;
      break;
    default:
      Unimplemented();
  }
}

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
