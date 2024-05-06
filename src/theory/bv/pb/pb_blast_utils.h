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
 * Various utility functions for PB-blasting.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__PB__PB_BLAST_UTILS_H
#define CVC5__THEORY__BV__PB__PB_BLAST_UTILS_H

#include "expr/node.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb {

template <class T> class TPseudoBooleanBlaster;

/** Constraint creation functions */
template <class T> inline
T mkConstraintNode(Kind k, std::vector<T> variables,
                   std::vector<T> coefficients, T value, NodeManager* nm);
template <class T> inline
T mkConstraintNode(Kind k, std::vector<T> variables,
                   std::vector<int> coefficients, int value, NodeManager* nm);
/** Term creation functions */
template <class T> inline
T mkTermNode(T variables, std::vector<T> constraints, NodeManager* nm);
template <class T> inline
T mkTermNode(T variables, std::unordered_set<T> constraints, NodeManager* nm);
/** Atom creation functions */
template <class T> inline
T mkAtomNode(std::vector<T> constraints, NodeManager* nm);
template <class T> inline
T mkAtomNode(std::unordered_set<T> constraints, NodeManager* nm);
/** PB logic gates */
template <class T> std::vector<std::string> mkPbXor(T a, T b, T res);
/** Other auxiliary functions */
template <class T = Node> inline  // TODO: I don't really want to set T as Node
std::vector<T> bvToUnsigned(unsigned size, NodeManager* nm, int sign = 1);
template <class T>
int ceil_log2(T a);

/**
 * Constraint Node format:
 * ( LITERAL ( ADD ( MULT var coeff ) ( MULT var coeff ) ... ) value )
 */
template <class T> inline
T mkConstraintNode(Kind k, std::vector<T> variables,
                   std::vector<T> coefficients, T value, NodeManager* nm)
{
  Assert(variables.size() == coefficients.size());
  unsigned size = variables.size();
  std::vector<T> terms;
  for (unsigned i = 0; i < size; i++)
  {
    terms.push_back(nm->mkNode(Kind::MULT, coefficients[i], variables[i]));
  }
  T linear_form = size == 1 ? terms[0] : nm->mkNode(Kind::ADD, terms);
  T result = nm->mkNode(k, linear_form, value);
  return result;
} 

template <class T> inline
T mkConstraintNode(Kind k, std::vector<T> variables,
                   std::vector<int> coefficients, int value, NodeManager* nm)
{
  Assert(variables.size() == coefficients.size());
  std::vector<T> coefficients_t;
  for (int coeff : coefficients)
  {
    coefficients_t.push_back(nm->mkConstInt(Rational(coeff)));
  }
  T value_t = nm->mkConstInt(value);
  return mkConstraintNode(k, variables, coefficients_t, value_t, nm);
} 

/**
 * Term Node format:
 * ( SEXPR ( SEXPR variables ... ) ( SEXPR constraints ... ) )
 */
template <class T> inline
T mkTermNode(T variables, std::vector<T> constraints,
             NodeManager* nm)
{
  T constraints_t = nm->mkNode(Kind::SEXPR, constraints);
  std::vector<T> result = {variables, constraints_t};
  T result_t = nm->mkNode(Kind::SEXPR, result);
  return result_t;
} 

template <class T> inline
T mkTermNode(T variables, std::unordered_set<T> constraints,
             NodeManager* nm)
{
  std::vector<T> v;
  v.reserve(constraints.size());
  for (auto it = constraints.begin(); it != constraints.end();)
  {
      v.push_back(std::move(constraints.extract(it++).value()));
  } // I'm pretty sure this works...
  return mkTermNode(variables, v, nm);
} 

/**
 * Atom Node format:
 * SEXPR ( Constraints )
 */
template <class T> inline
T mkAtomNode(std::vector<T> constraints, NodeManager* nm)
{
  T result = nm->mkNode(Kind::SEXPR, constraints);
  return result;
} 

template <class T> inline
T mkAtomNode(std::unordered_set<T> constraints, NodeManager* nm)
{
  std::vector<T> v;
  v.reserve(constraints.size());
  for (auto it = constraints.begin(); it != constraints.end();)
  {
    v.push_back(std::move(constraints.extract(it++).value()));
  } // TODO: I'm pretty sure this works...
  return mkAtomNode(v, nm);
} 

/** Creates the constraints that correspond to res = a \xor b */
template <class T> inline
std::vector<T> mkPbXor(T a, T b, T res, NodeManager* nm)
{
  std::vector<T> constraints;
  constraints.push_back(mkConstraintNode(Kind::GEQ,
      std::vector<T>{res, a, b}, std::vector<int>{-1, 1, 1}, 0, nm));
  constraints.push_back(mkConstraintNode(Kind::GEQ,
      std::vector<T>{res, a, b}, std::vector<int>{-1, -1, -1}, -2, nm));
  constraints.push_back(mkConstraintNode(Kind::GEQ,
      std::vector<T>{res, a, b}, std::vector<int>{1, 1, -1}, 0, nm));
  constraints.push_back(mkConstraintNode(Kind::GEQ,
      std::vector<T>{res, a, b}, std::vector<int>{1, -1, 1}, 0, nm));
  return constraints;
}

template <class T> inline
std::vector<T> bvToUnsigned(unsigned size, NodeManager* nm, int sign)
{
  std::ostringstream os;
  int coeff = (1 << size) * sign;
  std::vector<T> coefficients(size);
  std::generate(coefficients.begin(), coefficients.end(), [&coeff, nm] {
      return nm->mkConstInt(Rational(coeff /= 2)); });
  return coefficients;
}

template <class T> inline
int ceil_log2(T a)
{
  unsigned long long x = (unsigned long long) a;
  static const unsigned long long t[6] = {
    0xFFFFFFFF00000000ull, 0x00000000FFFF0000ull, 0x000000000000FF00ull,
    0x00000000000000F0ull, 0x000000000000000Cull, 0x0000000000000002ull
  };
  int y = (((x & (x - 1)) == 0) ? 0 : 1);
  int j = 32;
  int i;
  for (i = 0; i < 6; i++)
  {
    int k = (((x & t[i]) == 0) ? 0 : j);
    y += k;
    x >>= k;
    j >>= 1;
  }
  return y;
}

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif  // CVC5__THEORY__BV__PB__PB_BLAST_UTILS_H
