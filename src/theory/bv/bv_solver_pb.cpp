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
      d_facts(context())
{
  Trace("bv-pb") << "Built BVSolverPseudoBoolean\n";
  initPbSolver();
}

void BVSolverPseudoBoolean::postCheck(Theory::Effort level)
{
  Trace("bv-pb") << "Post check with effort level " << level << "\n";
  if (level != Theory::Effort::EFFORT_FULL) { return; }
  /** Process PB-blast queue and generate sets of variables and constraints. */
  std::vector<Node> blasted_atoms;
  while (!d_facts.empty())
  {
    Node fact = d_facts.front();
    d_facts.pop();
    Node result;  // Variables and constraints of the current fact.
    if (fact.getKind() == Kind::BITVECTOR_EAGER_ATOM) { Unhandled(); }
    else
    {
      d_pbBlaster->blastAtom(fact);
      result = d_pbBlaster->getAtom(fact);
    }
    blasted_atoms.push_back(result);
  }
  convertProblemOPB(blasted_atoms);
}

std::string BVSolverPseudoBoolean::
constraintToStringOPB(Node constraint, std::unordered_set<Node> &variables)
{
  std::ostringstream result;
  Node form = constraint[0];

  if (form.getKind() == Kind::MULT)
  {
    if (form[0].getConst<Rational>() >= 0) { result << "+" << form[0]; }
    else { result << form[0].getConst<Rational>(); }
    result << " " << form[1] << " ";
    variables.emplace(form[1]);
  }

  else if (form.getKind() == Kind::ADD)
  {
    for (Node term : form)
    {
      if (term[0].getConst<Rational>() >= 0) { result << "+" << term[0]; }
      else { result << term[0].getConst<Rational>(); }
      result << " " << term[1] << " ";
      variables.emplace(term[1]);
    }
  }

  else {Unreachable();}

  std::string literal = constraint.getKind() == Kind::EQUAL ? "=" : ">=";
  result << literal << " " << constraint[1].getConst<Rational>() << " ;";
  return result.str();
}

void BVSolverPseudoBoolean::convertProblemOPB(std::vector<Node> blasted_atoms)
{
  std::unordered_set<Node> variables;
  std::set<std::string> ordered_constraints;
  for (Node atom : blasted_atoms)
  {
    for (Node constraint : atom)
    {
      std::string constraint_str = constraintToStringOPB(constraint, variables);
      ordered_constraints.emplace(constraint_str);
    }

  }
  std::ostringstream opb_file;
  opb_file << "* #variable= " << variables.size();
  opb_file << " #constraint= " << ordered_constraints.size() << "\n";
  for (std::string c : ordered_constraints) { opb_file << c << "\n"; }
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
