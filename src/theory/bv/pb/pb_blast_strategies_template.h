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
 * Implementation of pseudo-boolean blasting functions for various operators.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__PB__PB_BLAST_STRATEGIES_TEMPLATE_H
#define CVC5__THEORY__BV__PB__PB_BLAST_STRATEGIES_TEMPLATE_H

#include "theory/bv/pb/pb_blast_utils.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb {

/**
 * Default Atom PB-Bitblasting strategies: 
 * 
 * @param node the atom to be bitblasted
 * @param pbb the pseudo-boolean bitblaster
 */

template <class T>
T UndefinedAtomPbStrategy(T atom, TPseudoBooleanBlaster<T>* pbb)
{
  Trace("bv-pb") << "Undefined PB-blasting strategy for atom of kind: "
                 << atom.getKind() << "\n";
  Unreachable();
}

/** TODO: consider adding bit-level equalities? */
template <class T>
T DefaultEqPb(T atom, TPseudoBooleanBlaster<T>* pbb)
{
  Assert(atom.getKind() == Kind::EQUAL);
  Trace("bv-pb") << "theory::bv::pb::DefaultEqPb " << atom << "\n";

  T lhs = pbb->blastTerm(atom[0]);
  T rhs = pbb->blastTerm(atom[1]);
  Assert(lhs[0].getNumChildren() == rhs[0].getNumChildren());

  NodeManager* nm = pbb->getNodeManager();
  std::vector<T> coefficients = bvToUnsigned(lhs[0].getNumChildren(), nm);
  for (T c : bvToUnsigned(lhs[1].getNumChildren(), nm, -1))
  {
    coefficients.push_back(c);
  }

  std::vector<T> variables;
  for (T v : lhs[0]) { variables.push_back(v); }
  for (T v : rhs[0]) { variables.push_back(v); }

  T atom_constraint = mkConstraintNode(Kind::EQUAL, variables, coefficients,
                                       pbb->d_ZERO, nm);
  Trace("bv-pb") << "theory::bv::pb::DefaultEqPb resulted in constraint "
                 << atom_constraint << "\n";

  std::unordered_set<T> constraints;
  constraints.insert(atom_constraint);
  for (T c : lhs[1]) { constraints.insert(c); }
  for (T c : rhs[1]) { constraints.insert(c); }
  return mkAtomNode(constraints, nm);
}

template <class T>
T DefaultUltPb(T atom, TPseudoBooleanBlaster<T>* pbb)
{
  Assert(atom.getKind() == Kind::BITVECTOR_ULT);
  Trace("bv-pb") << "theory::bv::pb::DefaultUltPb " << atom  << "\n";

  T lhs = pbb->blastTerm(atom[0]);
  T rhs = pbb->blastTerm(atom[1]);
  Assert(lhs[0].getNumChildren() == rhs[0].getNumChildren());

  NodeManager* nm = pbb->getNodeManager();
  std::vector<T> coefficients = bvToUnsigned(rhs[0].getNumChildren(), nm);
  for (T c : bvToUnsigned(lhs[0].getNumChildren(), nm, -1))
  {
    coefficients.push_back(c);
  }

  std::vector<T> variables;
  for (T v : rhs[0]) { variables.push_back(v); }
  for (T v : lhs[0]) { variables.push_back(v); }

  T atom_constraint = mkConstraintNode(Kind::GEQ, variables, coefficients,
                                       pbb->d_ONE, nm);
  Trace("bv-pb") << "theory::bv::pb::DefaultUltPb resulted in constraint "
                 << atom_constraint << "\n";

  std::unordered_set<T> constraints;
  constraints.emplace(atom_constraint);
  for (T c : lhs[1]) { constraints.insert(c); }
  for (T c : rhs[1]) { constraints.insert(c); }
  return mkAtomNode(constraints, nm);
}

/**
 * Negated Atom PB-Bitblasting strategies: 
 * 
 * @param node the atom to be bitblasted
 * @param pbb the pseudo-boolean bitblaster
 */

template <class T>
T NegatedEqPb(T atom, TPseudoBooleanBlaster<T>* pbb)
{
  Assert(atom.getKind() == Kind::EQUAL);
  Trace("bv-pb") << "theory::bv::pb::NegatedEqPb " << atom << "\n";
  NodeManager* nm = pbb->getNodeManager();

  T xor_node = pbb->getNodeManager()->mkNode(Kind::BITVECTOR_XOR, atom[0],
                                             atom[1]);
  T blasted_xor = pbb->blastTerm(xor_node);
  /** TODO: can I assume that # atom[0] == # atom[1] ? */
  Assert(blasted_xor[0].getNumChildren() == utils::getSize(atom[0]));

  std::vector<T> variables;
  for (T v : blasted_xor[0]) { variables.push_back(v); }
  T atom_constraint = mkConstraintNode(Kind::GEQ, variables,
                                       std::vector<int>{1, 1, 1, 1}, 0, nm);
  Trace("bv-pb") << "theory::bv::pb::NegatedEqPb resulted in constraint "
                 << atom_constraint << "\n";

  std::unordered_set<T> constraints;
  constraints.emplace(atom_constraint);
  for (T c : blasted_xor[1]) { constraints.emplace(c); }
  return mkAtomNode(constraints, nm);
}

/* 
 * Default Term PB-Blasting strategies
 * 
 * @param node the term to be bitblasted
 * @param sp [output parameter] pair representing the variables and constraints
 *                              generated by the blasting process
 * @param pbb the bitblaster in which the clauses are added
 */

template <class T>
T UndefinedTermPbStrategy(T node, TPseudoBooleanBlaster<T>* pbb)
{
  Trace("bv-pb") << "Undefined PB-blasting strategy for term of kind: "
                 << node.getKind() << "\n";
  Unreachable();
}

template <class T>
T DefaultVarPb(T term, TPseudoBooleanBlaster<T>* pbb)
{
  Trace("bv-pb") << "theory::bv::pb::DefaultVarPb blasting " << term;
  T variables = pbb->newVariable(utils::getSize(term));
  Trace("bv-pb") << " with bits " << variables << "\n";
  return mkTermNode(variables, std::vector<T>(), pbb->getNodeManager());
}

/** TODO: consider adding word-level constraints? */
/** TODO: Change `term` type to T */
template <class T>
T DefaultConstPb(Node term, TPseudoBooleanBlaster<T>* pbb)
{
  Trace("bv-pb") << "theory::bv::pb::DefaultConstPb blasting " << term << " ";
  Assert(term.getKind() == Kind::CONST_BITVECTOR);

  NodeManager* nm = pbb->getNodeManager();
  unsigned size = utils::getSize(term);
  T variables = pbb->newVariable(size);
  Trace("bv-pb") << "with bits " << variables << "\n"; 

  std::vector<T> constraints;
  for (unsigned i = 0; i < size; i++)
  {
    Integer bit_value = term.getConst<BitVector>().extract(size-i-1, size-i-1)
                                                  .getValue();
    T rhs = bit_value == Integer(0) ? pbb->d_ZERO : pbb->d_ONE;
    constraints.push_back(mkConstraintNode(Kind::EQUAL, {variables[i]},
                                           {pbb->d_ONE}, rhs, nm));
  }
  return mkTermNode(variables, constraints, nm);
}

template <class T>
T DefaultXorPb(T term, TPseudoBooleanBlaster<T>* pbb)
{
  Trace("bv-pb") << "theory::bv::pb::DefaultXorPb blasting " << term;
  Assert(term.getKind() == Kind::BITVECTOR_XOR);
  if (term.getNumChildren() != 2) { Unreachable(); }

  NodeManager* nm = pbb->getNodeManager();
  unsigned num_bits = utils::getSize(term);

  T variables = pbb->newVariable(num_bits);
  Trace("bv-pb") << " with bits " << variables << "\n";

  T lhs = pbb->blastTerm(term[0]);
  T rhs = pbb->blastTerm(term[1]);
  Assert(lhs[0].getNumChildren() == rhs[0].getNumChildren());

  std::unordered_set<T> constraints;
  for (unsigned i = 0; i < num_bits; i++)
  {
    for (T c : mkPbXor(lhs[0][i], rhs[0][i], variables[i], nm))
    {
      constraints.emplace(c);
    }
  }

  for (T c : lhs[1]) { constraints.insert(c); }
  for (T c : rhs[1]) { constraints.insert(c); }

  T blasted_term = mkTermNode(variables, constraints, nm);
  Assert(blasted_term[0].getNumChildren() == utils::getSize(term));
  Trace("bv-pb") << "theory::bv::pb::DefaultXorPb done\n";
  return blasted_term;
}

template <class T>
T DefaultAddPb(T term, TPseudoBooleanBlaster<T>* pbb)
{
  Trace("bv-pb") << "theory::bv::pb::DefaultAddPb blasting " << term << "\n";
  Assert(term.getKind() == Kind::BITVECTOR_ADD);

  NodeManager* nm = pbb->getNodeManager();
  unsigned num_bits = utils::getSize(term);
  T term_vars = pbb->newVariable(num_bits);
  Trace("bv-pb") << " with bits " << term_vars << "\n";

  std::vector<Node> variables, coefficients;
  std::unordered_set<Node> constraints;

  std::vector<Node> aux = bvToUnsigned(num_bits, nm);
  for(unsigned i = 0; i < term.getNumChildren(); i++)
  {
    T blasted = pbb->blastTerm(term[i]);
    Assert(blasted[0].getNumChildren() == num_bits);
    for (T v: blasted[0]) { variables.push_back(v); }
    std::copy(aux.begin(), aux.end(), std::back_inserter(coefficients));
    for (T c: blasted[1]) { constraints.insert(c); }
  }

  /** extra_bits used to store possible overflow */
  int extra_bits = ceil_log2(term.getNumChildren());
  T extra_vars = pbb->newVariable(extra_bits);
  for (T v : extra_vars) { variables.push_back(v); }
  for (T v : term_vars) { variables.push_back(v); }

  aux = bvToUnsigned(num_bits + extra_bits, nm, -1);
  std::move(aux.begin(), aux.end(), std::back_inserter(coefficients));
  constraints.insert(mkConstraintNode(Kind::EQUAL, variables, coefficients,
                                      pbb->d_ZERO, nm));

  T blasted_term = mkTermNode(term_vars, constraints, nm);
  Assert(blasted_term[0].getNumChildren() == utils::getSize(term));
  Trace("bv-pb") << "theory::bv::pb::DefaultAddPb done\n";
  return blasted_term;
}

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif   // CVC5__THEORY__BV__PB__PB_BLAST_STRATEGIES_TEMPLATE_H