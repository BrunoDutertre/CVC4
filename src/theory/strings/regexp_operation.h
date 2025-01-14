/*********************                                                        */
/*! \file regexp_operation.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tianyi Liang, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Symbolic Regular Expresion Operations
 **
 ** Symbolic Regular Expression Operations
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__REGEXP__OPERATION_H
#define CVC4__THEORY__STRINGS__REGEXP__OPERATION_H

#include <vector>
#include <set>
#include <algorithm>
#include <climits>
#include "util/hash.h"
#include "util/regexp.h"
#include "theory/theory.h"
#include "theory/rewriter.h"
//#include "context/cdhashmap.h"

namespace CVC4 {
namespace theory {
namespace strings {

class RegExpOpr {
  typedef std::pair< Node, CVC4::String > PairNodeStr;
  typedef std::set< Node > SetNodes;
  typedef std::pair< Node, Node > PairNodes;

 private:
  /** the code point of the last character in the alphabet we are using */
  unsigned d_lastchar;
  Node d_emptyString;
  Node d_true;
  Node d_false;
  Node d_emptySingleton;
  Node d_emptyRegexp;
  Node d_zero;
  Node d_one;

  Node d_sigma;
  Node d_sigma_star;

  std::map<PairNodes, Node> d_simpl_cache;
  std::map<PairNodes, Node> d_simpl_neg_cache;
  std::map<Node, std::pair<int, Node> > d_delta_cache;
  std::map<PairNodeStr, Node> d_dv_cache;
  std::map<PairNodeStr, std::pair<Node, int> > d_deriv_cache;
  std::map<Node, std::pair<Node, int> > d_compl_cache;
  std::map<Node, bool> d_cstre_cache;
  std::map<Node, std::pair<std::set<unsigned>, std::set<Node> > > d_cset_cache;
  std::map<Node, std::pair<std::set<unsigned>, std::set<Node> > > d_fset_cache;
  std::map<PairNodes, Node> d_inter_cache;
  std::map<Node, Node> d_rm_inter_cache;
  std::map<Node, bool> d_norv_cache;
  std::map<Node, std::vector<PairNodes> > d_split_cache;
  void simplifyPRegExp(Node s, Node r, std::vector<Node> &new_nodes);
  void simplifyNRegExp(Node s, Node r, std::vector<Node> &new_nodes);
  std::string niceChar(Node r);
  Node mkAllExceptOne(unsigned c);
  bool isPairNodesInSet(std::set<PairNodes> &s, Node n1, Node n2);

  bool containC2(unsigned cnt, Node n);
  Node convert1(unsigned cnt, Node n);
  void convert2(unsigned cnt, Node n, Node &r1, Node &r2);
  bool testNoRV(Node r);
  Node intersectInternal(Node r1,
                         Node r2,
                         std::map<PairNodes, Node> cache,
                         unsigned cnt);
  Node removeIntersection(Node r);
  void firstChars(Node r, std::set<unsigned> &pcset, SetNodes &pvset);

 public:
  RegExpOpr();
  ~RegExpOpr();

  bool checkConstRegExp( Node r );
  void simplify(Node t, std::vector< Node > &new_nodes, bool polarity);
  int delta( Node r, Node &exp );
  int derivativeS( Node r, CVC4::String c, Node &retNode );
  Node derivativeSingle( Node r, CVC4::String c );
  Node intersect(Node r1, Node r2, bool &spflag);

  std::string mkString( Node r );
};

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__STRINGS__REGEXP__OPERATION_H */
