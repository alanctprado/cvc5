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

#include "theory/bv/pb/pb_blast_strategies_template.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb {

/**
 * The PB-blaster that manages the mapping between Nodes
 * and their bitwise definition
 */

template <class T>
class TPseudoBooleanBlaster
{
 private:
  NodeManager* d_nm;

 protected:
  typedef std::unordered_map<T, T> TermDefMap;  // TODO: CDHashMap?
  typedef std::unordered_map<T, T> AtomDefMap;
  TermDefMap d_termCache;
  AtomDefMap d_atomCache;

  typedef T (*TermStrategy)(T, TPseudoBooleanBlaster<T>*);
  typedef T (*AtomStrategy)(T, TPseudoBooleanBlaster<T>*);

  /**
   * Function tables for the various pseudo-boolean blasting strategies,
   * indexed by node kind
   */
  AtomStrategy d_atomStrategies[static_cast<uint32_t>(Kind::LAST_KIND)];
  AtomStrategy d_negAtomStrategies[static_cast<uint32_t>(Kind::LAST_KIND)];
  TermStrategy d_termStrategies[static_cast<uint32_t>(Kind::LAST_KIND)];

  void initAtomStrategies();
  void initTermStrategies();

 public:
  TPseudoBooleanBlaster(NodeManager* nm);
  virtual ~TPseudoBooleanBlaster() {}

  virtual void blastAtom(T atom) = 0;
  T getAtom(T atom) const;
  bool hasAtom(T atom) const;
  void storeAtom(T atom, const T blastedAtom);

  virtual T blastTerm(T term) = 0;
  T getTerm(T term) const;
  bool hasTerm(T term) const;
  void storeTerm(T term, const T blastedTerm);

  virtual T newVariable(unsigned numBits) = 0;
  NodeManager* getNodeManager() const;
  const Node d_ZERO = d_nm->mkConstInt(Rational(0));
  const Node d_ONE = d_nm->mkConstInt(Rational(1));
};

/** Pseudo-boolean blaster implementation. */
template <class T>
void TPseudoBooleanBlaster<T>::initAtomStrategies()
{
  for (uint32_t i = 0; i < static_cast<uint32_t>(Kind::LAST_KIND); ++i)
  {
    d_atomStrategies[i] = UndefinedAtomPbStrategy<T>;
    d_negAtomStrategies[i] = UndefinedAtomPbStrategy<T>;
  }
  /** Setting default PB strategies for atoms */
  d_atomStrategies[static_cast<uint32_t>(Kind::EQUAL)] =
      DefaultEqPb<T>;
  d_atomStrategies[static_cast<uint32_t>(Kind::BITVECTOR_ULT)] =
      DefaultUltPb<T>;
  /** Setting default PB strategies for negated atoms */
  d_negAtomStrategies[static_cast<uint32_t>(Kind::EQUAL)] =
      NegatedEqPb<T>;
}

template <class T>
void TPseudoBooleanBlaster<T>::initTermStrategies()
{
  for (uint32_t i = 0; i < static_cast<uint32_t>(Kind::LAST_KIND); i++)
  {
    d_termStrategies[i] = UndefinedTermPbStrategy<T>;
  }
  /** Setting default PB strategies for terms */
  d_termStrategies[static_cast<uint32_t>(Kind::VARIABLE)] =
      DefaultVarPb<T>;
  d_termStrategies[static_cast<uint32_t>(Kind::CONST_BITVECTOR)] =
      DefaultConstPb<T>;
   d_termStrategies[static_cast<uint32_t>(Kind::BITVECTOR_XOR)] =
       DefaultXorPb<T>;
   d_termStrategies[static_cast<uint32_t>(Kind::BITVECTOR_ADD)] =
       DefaultAddPb<T>;
}

template <class T>
TPseudoBooleanBlaster<T>::TPseudoBooleanBlaster(NodeManager* nm) : d_nm(nm)
{
  initAtomStrategies();
  initTermStrategies();
}

template <class T>
T TPseudoBooleanBlaster<T>::getAtom(T atom) const
{
  Assert(hasAtom(atom));
  return d_atomCache.find(atom)->second;
}

template <class T>
bool TPseudoBooleanBlaster<T>::hasAtom(T atom) const
{
  return d_atomCache.find(atom) != d_atomCache.end();
}

template <class T>
void TPseudoBooleanBlaster<T>::storeAtom(T atom, const T blastedAtom)
{
  d_atomCache.emplace(atom, blastedAtom);
}

template <class T>
T TPseudoBooleanBlaster<T>::getTerm(T term) const
{
  Assert(hasTerm(term));
  return d_termCache.find(term)->second;
}

template <class T>
bool TPseudoBooleanBlaster<T>::hasTerm(T term) const
{
  return d_termCache.find(term) != d_termCache.end();
}

template <class T>
void TPseudoBooleanBlaster<T>::storeTerm(T term, const T blastedTerm)
{
  d_termCache.emplace(term, blastedTerm);
}

template <class T>
NodeManager* TPseudoBooleanBlaster<T>::getNodeManager() const
{
  return d_nm;
}

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif  // CVC5__THEORY__BV__PB__PB_BLASTER_H
