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

#include "theory/bv/pb/exact.h"
#include "theory/bv/pb/roundingsat.h"

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

/** Same as BVSolverBitblast::needsEqualityEngine */
bool BVSolverPseudoBoolean::needsEqualityEngine(EeSetupInfo& esi)
{
  // we always need the equality engine if sharing is enabled for processing
  // equality engine and shared terms
  return logicInfo().isSharingEnabled() || options().bv.bvEqEngine;
}

void BVSolverPseudoBoolean::postCheck(Theory::Effort level)
{
  Trace("bv-pb") << "Post check with effort level " << level << "\n";
  if (level != Theory::Effort::EFFORT_FULL) return;

  std::vector<Node> blasted_atoms;
  while (!d_facts.empty())
  {
    Node fact = d_facts.front();
    d_facts.pop();
    Node result;  // Variables and constraints for the current fact.
    if (fact.getKind() == Kind::BITVECTOR_EAGER_ATOM) Unhandled();
    d_pbBlaster->blastAtom(fact);
    result = d_pbBlaster->getAtom(fact);
    for (Node constraint : result)
    {
      d_pbSolver->addConstraint(constraint);
    }
    blasted_atoms.push_back(fact);
  }

  PbSolveState s = d_pbSolver->solve();
  if (s == PbSolveState::PB_UNSAT)
  {
    Node conflict;
    NodeManager* nm = nodeManager();
    conflict = nm->mkAnd(blasted_atoms);
    d_im.conflict(conflict, InferenceId::BV_PB_BLAST_CONFLICT);
  }
  else if (s == PbSolveState::PB_SAT)
  {
    Trace("bv-pb") << "SATISFIABLE\n";
  }
  else
  {
    Unreachable();
  }
}

bool BVSolverPseudoBoolean::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  Trace("bv-pb") << "Adding fact: " << fact << std::endl;
  /**
   * Check whether `fact` is an input assertion on user-level 0.
   *
   * TODO(alanctprado):
   * Not really sure if this should be handled. I'm confident we concluded it
   * won't happen. We don't care about other theories?
   */
  Valuation& val = d_state.getValuation();
  if (options().bv.bvAssertInput && val.isFixed(fact)) Unhandled();
  d_facts.push_back(fact);
  /**
   * TODO(alanctprado):
   * Return false to enable equality engine reasoning in Theory, which is
   * available if we are using the equality engine. I don't think it is our
   * case.
   */
  return 1;
}

/** Same as BVSolverBitblast::explain */
TrustNode BVSolverPseudoBoolean::explain(TNode n)
{
  Trace("bv-pb") << "explain called on " << n << std::endl;
  return d_im.explainLit(n);
}

/**
 * TODO(alanctprado):
 * Used in BvSolverBitblast. Not sure we need it.
 */
void BVSolverPseudoBoolean::computeRelevantTerms(std::set<Node>& termSet)
{
   Unimplemented();
}

/**
 * TODO(alanctprado):
 * Used in BvSolverBitblast. Not sure we need it.
 * Why is cvc5's documentation so bad? :O :(
 */
bool BVSolverPseudoBoolean::collectModelValues(TheoryModel* m,
                                               const std::set<Node>& termSet)
{
   Unimplemented();
}

/**
 * TODO(alanctprado):
 * Used in BvSolverBitblast. Not sure we need it.
 * Why is cvc5's documentation so bad? :O :(
 */
Node BVSolverPseudoBoolean::getValue(TNode node, bool initialize)
{
   Unimplemented();
}

/** TODO(alanctprado): currently unused */
std::string BVSolverPseudoBoolean::constraintToStringOPB(
    Node constraint, std::unordered_set<Node>& variables)
{
  std::ostringstream result;
  Node form = constraint[0];

  if (form.getKind() == Kind::MULT)
  {
    if (form[0].getConst<Rational>() >= 0)
      result << "+" << form[0];
    else
      result << form[0].getConst<Rational>();
    result << " " << form[1] << " ";
    variables.emplace(form[1]);
  }

  else if (form.getKind() == Kind::ADD)
  {
    for (Node term : form)
    {
      if (term[0].getConst<Rational>() >= 0)
        result << "+" << term[0];
      else
        result << term[0].getConst<Rational>();
      result << " " << term[1] << " ";
      variables.emplace(term[1]);
    }
  }

  else
    Unreachable();

  std::string literal = constraint.getKind() == Kind::EQUAL ? "=" : ">=";
  result << literal << " " << constraint[1].getConst<Rational>() << " ;";
  return result.str();
}

/** TODO(alanctprado): currently unused */
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
  for (Node variable : variables) { d_pbSolver->addVariable(variable); }
  std::ostringstream opb_file;
  opb_file << "* #variable= " << variables.size();
  opb_file << " #constraint= " << ordered_constraints.size() << "\n";
  for (std::string c : ordered_constraints) opb_file << c << "\n";
  Trace("bv-pb-opb") << opb_file.str();
}

void BVSolverPseudoBoolean::initPbSolver()
{
  // TODO: move guards / creation to a factory class
  switch (options().bv.bvPbSolver)
  {
    case options::BvPbSolver::EXACT:
      Trace("bv-pb") << "Initializing Exact PB Solver...\n";
      #ifdef CVC5_USE_EXACT
        d_pbSolver.reset(new ExactSolver(
            d_env,
            statisticsRegistry(),
            "theory::bv::BVSolverBitblast::"));
        Trace("bv-pb") << "Initialization successful...\n";
      #endif
      break;
    case options::BvPbSolver::ROUNDINGSAT:
      Trace("bv-pb") << "Initializing RoundingSat PB Solver...\n";
      #ifdef CVC5_USE_ROUNDINGSAT
        Trace("bv-pb") << "Deu: " << ROUNDINGSAT_PATH << "\n\n";
        d_pbSolver.reset(new RoundingSatSolver(
            ROUNDINGSAT_PATH,
            d_env,
            statisticsRegistry(),
            "theory::bv::BVSolverBitblast::"));
        Trace("bv-pb") << "Initialization successful...\n";
      #endif
      break;
    default: Unimplemented();
  }
}

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
