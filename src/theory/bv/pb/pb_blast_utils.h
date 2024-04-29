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

#include <initializer_list>
#include <iterator>
#include <unordered_set>
#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__PB__PB_BLAST_UTILS_H
#define CVC5__THEORY__BV__PB__PB_BLAST_UTILS_H

#include <ostream>
#include <vector>
#include "expr/node.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb {

template <class T> class TPseudoBooleanBlaster;

template <class T> T
mkConstraintNode(Kind k, std::vector<T> variables, std::vector<T> coefficients,
                 T value, NodeManager* nm);

template <class T>
T mkTermNode(T variables, std::vector<T> constraints, NodeManager* nm);
template <class T>
T mkTermNode(T variables, std::unordered_set<T> constraints, NodeManager* nm);

template <class T = Node>
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
  /** Use bool for type */
  Assert(variables.size() == coefficients.size());
  std::vector<T> terms;
  for (unsigned i = 0; i < variables.size(); i++)
  {
    terms.push_back(nm->mkNode(Kind::MULT, coefficients[i], variables[i]));
  }
  T linear_form = nm->mkNode(Kind::ADD, terms);
  T result = nm->mkNode(k, linear_form, value);
  return result;
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

///**
// * Atom Node format:
// * SEXPR ( Constraint,
// *         children...
// *       )
// */
//template <class T> inline
//T mkAtomNode(T constraint, std::vector<T> children, NodeManager* nm)
//{
//  std::vector<T> result = {constraint};
//  std::move(children.begin(), children.end(), std::back_inserter(result));
//  T result_t = nm->mkNode(Kind::SEXPR, result);
//  return result_t;
//} 


//template <class T> inline
//std::string toString (const std::vector<T>& bv)
//{
//  std::ostringstream os;
//  os << "[ ";
//  for (unsigned i = 0; i < bv.size(); i++) { os << bv[i] << " "; }
//  os << "]";
//  return os.str();
//} 
//
//template <class T> inline
//std::string mkPbVar(T var, long long coeff)
//{
//  std::string sign = coeff >= 0 ? "+" : "-";
//  return sign + std::to_string(llabs(coeff)) + " x" + std::to_string(var);
//}
//
//template <class T> inline
//std::string mkPbVar(T var)
//{
//  return "+1 x" + std::to_string(var);
//}
//
//template <class T> inline
//std::string bvToUnsigned(const std::vector<T>& bv, int sign)
//{
//  std::ostringstream os;
//  long long coeff = (1 << (bv.size() - 1)) * sign;
//  for (unsigned i = 0; i < bv.size(); i++)
//  {
//    os << mkPbVar(bv[i], coeff) << " ";
//    coeff /= 2;
//  }
//  return os.str();
//} 

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

//template <class T> inline
//std::string bvToClause(const std::vector<T>& bv)
//{
//  std::ostringstream os;
//  for (unsigned i = 0; i < bv.size(); i++) { os << mkPbVar(bv[i]) << " "; }
//  os <<  ">= 1 ;\n";
//  return os.str();
//} 
//
//template <class T> std::vector<std::string> mkPbXor(T a, T b, T res);
//
//template <class T> inline
//std::vector<std::string> mkPbXor(T a, T b, T res)
//{
//  std::vector<std::string> constraints;
//  constraints.push_back(mkPbVar(res, -1) + " " + mkPbVar(a, 1) + " "
//                        + mkPbVar(b, 1) + " >= 0 ;\n");
//  constraints.push_back(mkPbVar(res, -1) + " " + mkPbVar(a, -1) + " "
//                        + mkPbVar(b, -1) + " >= -2 ;\n");
//  constraints.push_back(mkPbVar(res, 1) + " " + mkPbVar(a, 1) + " "
//                        + mkPbVar(b, -1) + " >= 0 ;\n");
//  constraints.push_back(mkPbVar(res, 1) + " " + mkPbVar(a, -1) + " "
//                        + mkPbVar(b, 1) + " >= 0 ;\n");
//  return constraints;
//}

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
