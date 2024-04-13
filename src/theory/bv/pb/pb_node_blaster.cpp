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
 * PB-blaster used to PB-blast to 0-1 linear inequalities
 */

#include "theory/bv/pb/pb_node_blaster.h"

#include <algorithm>
#include <sstream>
#include <unordered_set>

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb {

PseudoBooleanBlaster::PseudoBooleanBlaster(Env& env, TheoryState* s)
    : TPseudoBooleanBlaster<unsigned, std::string>(), EnvObj(env)
{
  d_varCounter = 1;
}

void PseudoBooleanBlaster::blastAtom(TNode atom)
{
  /**
   * Note: We rewrite the nodes because it's not guaranteed (yet) that facts
   * sent to theories are rewritten.
   */
  Trace("bv-pb-blast") << "Original atom: " << atom << "\n";
  if (hasAtom(atom)) return;
  std::vector<std::string> constraints;
  if (atom.getKind() == Kind::NOT)
  {
    Node normalized = rewrite(atom[0]);
    Trace("bv-pb") << "Normalized atom: " << normalized << "; Kind: "
                   << normalized.getKind() << "\n";
    constraints = d_negAtomStrategies[
      static_cast<uint32_t>(normalized.getKind())
    ](normalized, this);
  }

  else
  {
    Node normalized = rewrite(atom);
    Trace("bv-pb") << "Normalized atom: " << normalized << "; Kind: "
                   << normalized.getKind() << "\n";
    constraints = d_atomStrategies[
      static_cast<uint32_t>(normalized.getKind())
    ](normalized, this);
  }

  Trace("bv-pb-blast") << "Blasted atom:\n";
  if (TraceIsOn("bv-pb-blast"))
  {
    for (std::string c : constraints) { Trace("bv-pb-blast") << c; }
  }

  Subproblem unique_constraints;
  simplifyConstraints(constraints, unique_constraints);
  storeAtom(atom, unique_constraints);
}

void PseudoBooleanBlaster::simplifyConstraints(std::vector<std::string>
                                               constraints, Subproblem& ret)
{
  std::unordered_set<std::string> unique_constraints;
  std::unordered_set<unsigned> unique_variables;
  for (std::string c : constraints) { unique_constraints.insert(c); }
  for (std::string c : unique_constraints)
  {
    ret.second.push_back(c);
    size_t prev = 0;
    size_t next = 0;
    std::string token;
    while ((next = c.find(" ", prev)) != std::string::npos)
    {
      token = c.substr(prev, next - prev);
      if (token[0] == 'x')
        unique_variables.insert(std::stoul(token.substr(1)));
      prev = next + 1;
    }
  }
  for (unsigned v : unique_variables) { ret.first.push_back(v); }
}


void PseudoBooleanBlaster::storeAtom(TNode atom, Subproblem atom_bb)
{
  d_pbAtoms.emplace(atom, atom_bb);
}

void PseudoBooleanBlaster::makeVariables(TNode node, Subproblem& sp,
                                         unsigned spare)
{
  Assert(sp.first.size() == 0);
  for (unsigned i = 0; i < utils::getSize(node) + spare; i++)
  {
    sp.first.push_back(newVariable());
  }
}

void PseudoBooleanBlaster::storeTerm(TNode node, const Subproblem& sp)
{
  /** TO-DO: unordered_map::insert vs unordered_map::emplace ?? */
  d_termCache.emplace(node, sp);
}

bool PseudoBooleanBlaster::hasAtom(TNode atom) const
{
  return d_pbAtoms.find(atom) != d_pbAtoms.end();
}

unsigned PseudoBooleanBlaster::newVariable()
{
  return d_varCounter++;
}

void PseudoBooleanBlaster::blastTerm(TNode node, Subproblem& sp)
{
  Assert(node.getType().isBitVector());
  if (hasTerm(node))
  {
    getTerm(node, sp);
    return;
  }
  d_termStrategies[static_cast<uint32_t>(node.getKind())](node, sp, this);
  Assert(sp.first.size() == utils::getSize(node));
  storeTerm(node, sp);
}

std::pair<std::vector<unsigned>, std::vector<std::string>>
PseudoBooleanBlaster::getStoredAtom(TNode atom)
{
  Assert(hasAtom(atom));
  return d_pbAtoms.at(atom);
}

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
