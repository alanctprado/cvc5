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

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb {

PseudoBooleanBlaster::PseudoBooleanBlaster(Env& env, TheoryState* s)
    : TPseudoBooleanBlaster<Node>(env.getNodeManager()), EnvObj(env)
{
  d_varCounter = 1;
}

void PseudoBooleanBlaster::blastAtom(Node atom)
{
  /**
   * Note: We rewrite the nodes because it's not guaranteed (yet) that facts
   * sent to theories are rewritten.
   */
  Trace("bv-pb") << "\nOriginal atom: " << atom << "\n";
  if (hasAtom(atom)) return;

  Node result;
  if (atom.getKind() == Kind::NOT)
  {
    Node normalized = rewrite(atom[0]);
    Trace("bv-pb-blast") << "\nNormalized atom: " << normalized << "; Kind: "
                   << normalized.getKind() << "\n";
    result = d_negAtomStrategies[
      static_cast<uint32_t>(normalized.getKind())
    ](normalized, this);
  }

  else
  {
    Node normalized = rewrite(atom);
    Trace("bv-pb-blast") << "\nNormalized atom: " << normalized << "; Kind: "
                   << normalized.getKind() << "\n";
    result = d_atomStrategies[
      static_cast<uint32_t>(normalized.getKind())
    ](normalized, this);
  }

  Trace("bv-pb-blast") << "Blasted atom:\n";
  if (TraceIsOn("bv-pb-blast"))
  {
    for (Node c : result) { Trace("bv-pb-blast") << c << "\n"; }
  }

  storeAtom(atom, result);
}

Node PseudoBooleanBlaster::newVariable(unsigned numBits)
{
  Assert(numBits > 0);
  NodeManager* nm = getNodeManager();
  std::vector<Node> bits;
  for (unsigned i = 0; i < numBits; i++)
  {
    bits.push_back(nm->mkBoundVar("x" + std::to_string(d_varCounter++),
                                  nm->booleanType()));
  }
  return getNodeManager()->mkNode(Kind::SEXPR, bits);
}

Node PseudoBooleanBlaster::blastTerm(Node term)
{
  Assert(term.getType().isBitVector());
  if (hasTerm(term))
  {
    Trace("bv-pb") << "Recovered bits " << getTerm(term)[0] << " for term "
                   << term << "\n";
    return getTerm(term);
  }
  Kind kind = term.getKind();
  Node result = d_termStrategies[static_cast<uint32_t>(kind)](term, this);
  Assert(result[0].getNumChildren() == utils::getSize(term));
  storeTerm(term, result);
  return result;
}

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
