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
 * Wrapper around the PB solver used for PB-blasting.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__PB__PB_BLASTER_H
#define CVC5__THEORY__BV__PB__PB_BLASTER_H

#include <unordered_map>
#include "expr/node.h"
#include "theory/theory.h"

#include "theory/bv/pb/pb_blast_strategies_template.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb {

/**
 * The PB-blaster that manages the mapping between Nodes
 * and their bitwise definition
 *
 * T = variables, U = constraints
 */

template <class T, class U>
class TPseudoBooleanBlaster
{
 protected:
  typedef std::vector<T> Variables;
  typedef std::vector<U> Constraints;
  typedef std::pair<Variables, Constraints> Subproblem;
  typedef std::unordered_map<Node, Subproblem> TermDefMap;

  typedef void (*TermStrategy)(TNode, Subproblem&,
                               TPseudoBooleanBlaster<T,U>*);
  typedef std::vector<U> (*AtomStrategy)(TNode, TPseudoBooleanBlaster<T,U>*);

  TermDefMap d_termCache;

  void initAtomStrategies();
  void initTermStrategies();

  /**
   * Function tables for the various pseudo-boolean blasting strategies,
   * indexed
   * by node kind>
   */
  AtomStrategy d_atomStrategies[static_cast<uint32_t>(Kind::LAST_KIND)];
  AtomStrategy d_negAtomStrategies[static_cast<uint32_t>(Kind::LAST_KIND)];
  TermStrategy d_termStrategies[static_cast<uint32_t>(Kind::LAST_KIND)];

 public:
  TPseudoBooleanBlaster();
  virtual ~TPseudoBooleanBlaster() {}
  virtual void blastAtom(TNode node) = 0;
  virtual void blastTerm(TNode node, Subproblem& sp) = 0;
  virtual void makeVariables(TNode node, Subproblem& sp, unsigned spare=0) = 0;
  virtual bool hasAtom(TNode atom) const = 0;
  virtual T newVariable() = 0;
  virtual void storeAtom(TNode atom, Subproblem atom_bb) = 0;
  virtual void simplifyConstraints(Constraints constraints, Subproblem& sp) = 0;
  bool hasTerm(TNode node) const;
  void getTerm(TNode node, Subproblem& sp) const;
  virtual void storeTerm(TNode term, const Subproblem& subproblem);
};

/** Pseudo-boolean blaster implementation. */
template <class T, class U>
void TPseudoBooleanBlaster<T,U>::initAtomStrategies()
{
  for (uint32_t i = 0; i < static_cast<uint32_t>(Kind::LAST_KIND); ++i)
  {
    d_atomStrategies[i] = UndefinedAtomPbStrategy<T,U>;
    d_negAtomStrategies[i] = UndefinedAtomPbStrategy<T,U>;
  }
  /** Setting default PB strategies for atoms */
  d_atomStrategies[static_cast<uint32_t>(Kind::EQUAL)] =
      DefaultEqPb<T,U>;
  d_atomStrategies[static_cast<uint32_t>(Kind::BITVECTOR_ULT)] =
      DefaultUltPb<T,U>;
  /** Setting default PB strategies for negated atoms */
  d_negAtomStrategies[static_cast<uint32_t>(Kind::EQUAL)] =
      NegatedEqPb<T,U>;
}

template <class T, class U>
void TPseudoBooleanBlaster<T,U>::initTermStrategies()
{
  for (uint32_t i = 0; i < static_cast<uint32_t>(Kind::LAST_KIND); i++)
  {
    d_termStrategies[i] = UndefinedTermPbStrategy<T,U>;
  }
  /** Setting default PB strategies for terms */
   d_termStrategies[static_cast<uint32_t>(Kind::VARIABLE)] =
       DefaultVarPb<T,U>;
   d_termStrategies[static_cast<uint32_t>(Kind::CONST_BITVECTOR)] =
       DefaultConstPb<T,U>;
   d_termStrategies[static_cast<uint32_t>(Kind::BITVECTOR_XOR)] =
       DefaultXorPb<T,U>;
   d_termStrategies[static_cast<uint32_t>(Kind::BITVECTOR_ADD)] =
       DefaultAddPb<T,U>;
}

template <class T, class U>
TPseudoBooleanBlaster<T,U>::TPseudoBooleanBlaster()
{
  initAtomStrategies();
  initTermStrategies();
}

template <class T, class U>
bool TPseudoBooleanBlaster<T,U>::hasTerm(TNode node) const
{
  return d_termCache.find(node) != d_termCache.end();
}

template <class T, class U>
void TPseudoBooleanBlaster<T,U>::getTerm(TNode node, Subproblem& sp) const
{
  Assert(hasTerm(node));
  sp = d_termCache.find(node)->second;
}

template <class T, class U>
void TPseudoBooleanBlaster<T,U>::storeTerm(TNode node, const Subproblem& sp)
{
  d_termCache.insert(std::make_pair(node, sp));
}

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif  // CVC5__THEORY__BV__PB__PB_BLASTER_H
