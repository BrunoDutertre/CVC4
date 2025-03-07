/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of entailment tests involving regular expressions.
 */

#include "theory/strings/regexp_entail.h"

#include "theory/rewriter.h"
#include "theory/strings/regexp_eval.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"
#include "util/rational.h"
#include "util/string.h"
#include "util/regexp.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

RegExpEntail::RegExpEntail(Rewriter* r) : d_aent(r)
{
  d_zero = NodeManager::currentNM()->mkConstInt(Rational(0));
  d_one = NodeManager::currentNM()->mkConstInt(Rational(1));
}

/**** AWS update: Brzozowski derivatives ****/

/** Initialize the cache */
std::map<std::tuple<Node, Node, bool>, Node> RegExpEntail::brzo_consume_one_cache;
std::map<Node, Node> RegExpEntail::flattened_regex_cache;

/**
 * Returns Node::null() if we cannot decide the test, otherwise Node(true) or Node(false).
 */
Node RegExpEntail::check_epsilon_in_re(Node& regex) {
  Trace("regexp-brzo-rewrite-debug") << "Checking if epsilon is in RE: " << regex << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  Node d_emptyWord = Word::mkEmptyWord(nm->stringType());
  switch(regex.getKind()) {
    case Kind::REGEXP_NONE: return nm->mkConst(false); break;
    // case Kind::REGEXP_ALL: return nm->mkConst(true);
    case Kind::REGEXP_ALLCHAR: return nm->mkConst(false); break;
    case Kind::STRING_TO_REGEXP: {
      // check if the string is constant
      Node re_str = regex[0];
      if (re_str.isConst()) {
        return nm->mkConst(Word::isEmpty(re_str));
      }
      return Node::null();
      break;
    }
    case Kind::REGEXP_INTER:
    case Kind::REGEXP_CONCAT: {
      Trace("regexp-brzo-rewrite-debug") << "Case matched - REGEXP_CONCAT or INTER " << std::endl;
      std::vector<Node> childrenc;
      for (auto c : regex) {
        Trace("regexp-brzo-rewrite-debug") << "Checking Child " << c << std::endl;
        Trace("regexp-brzo-rewrite-debug") << push;
        Node ret = check_epsilon_in_re(c);
        Trace("regexp-brzo-rewrite-debug") << pop;
        Trace("regexp-brzo-rewrite-debug") << "Result of checking child " << c << " is " << ret << std::endl;

        if (ret == Node::null() || ret == nm->mkConst(false)) {
          return ret;
        }
        if (ret == nm->mkConst(true)) {
          continue;
        }
        else {
          Trace("regexp-brzo-rewrite-debug") << "\tResult of epsilon_in_re_check must be null, true or false node." << std::endl;
          Unreachable();
        }
      }
      return nm->mkConst(true);
      break;
    }
    case Kind::REGEXP_UNION: {
      // Result might be unknown. If we encountered an unknown result, and we did not get  `true` for any element, then we return Node::null().
      bool encountered_unknown = false;
      for (auto c : regex) {
        Node ret = check_epsilon_in_re(c);
        if (ret == Node::null()) {
          encountered_unknown = true;
        }
        if (ret == nm->mkConst(true)) {
          return nm->mkConst(true);
        }
      }
      if (encountered_unknown) {
        return Node::null();
      }
      return nm->mkConst(false);
      break;
    }
    case Kind::REGEXP_STAR: return nm->mkConst(true); break;
    case Kind::REGEXP_PLUS: {
      Node reg_inside = regex[0];
      return check_epsilon_in_re(reg_inside);
      break;
    }
    case Kind::REGEXP_OPT:  return nm->mkConst(true); break;
    case Kind::REGEXP_RANGE: {
      // a range can never contain epsilon
      return nm->mkConst(false);
      break;
    }
    case Kind::REGEXP_LOOP: {
      // HS Caution: Not clear about the structure of the regexp_loop node.
      // Still sound.
      uint32_t lo = utils::getLoopMinOccurrences(regex);
      if (lo == 0) { return nm->mkConst(true); }
      else {
        Node reg_inside = regex[0];
        return check_epsilon_in_re(reg_inside);
      }
      break;
    }
    case Kind::REGEXP_COMPLEMENT: {
      Node reg_inside = regex[0];
      Node res = check_epsilon_in_re(reg_inside);
      if (res == nm->mkConst(true)) { return nm->mkConst(false); }
      if (res == nm->mkConst(false)) { return nm->mkConst(true); }
      return Node::null();
      break;
    }
    default:
      return Node::null();
      break;
  }
}

/**
 * Deeply flattens the strings. Removes the empty string from str.++
 */
std::vector<Node> string_flatten_deep(const Node& str) {
  NodeManager* nm = NodeManager::currentNM();
  Node d_emptyWord = Word::mkEmptyWord(nm->stringType());
  std::vector<Node> children;
  if (str.getKind() == Kind::STRING_CONCAT) {
    for (auto c: str) {
      auto c_flat = string_flatten_deep(c);
      for (auto cc: c_flat) {
        if (cc == d_emptyWord) continue; // filter out empty strings and drop them
        children.push_back(cc);
      }
    }

    return children;
  }
  // Otherwise just return the string node inside a vector
  return {str};
}

/**
 * Deeply flattens the strings. Removes the empty string from str.++. Also, expands words "abc" to "a" ++ "b" ++ "c"
 */
std::vector<Node> string_flatten_deep_true(const Node& str) {
  NodeManager* nm = NodeManager::currentNM();
  Node d_emptyWord = Word::mkEmptyWord(nm->stringType());
  std::vector<Node> children;
  if (str.getKind() == Kind::STRING_CONCAT) {
    for (auto c: str) {
      auto c_flat = string_flatten_deep_true(c);
      for (auto cc: c_flat) {
        if (cc == d_emptyWord) continue; // filter out empty strings and drop them
        children.push_back(cc);
      }
    }
    return children;
  }
  else if (str.isConst()) {
    return Word::getChars(str);
  }
  // Otherwise just return the string node inside a vector
  return {str};
}

// We also remove all the redundant empty strings from inside the str.to_re

Node RegExpEntail::deeply_flatten_strings_in_regex (const Node& regex) {
  Trace("regexp-brzo-rewrite-debug") << "Flattening the regex " << regex << std::endl;
  // check cache
  if (flattened_regex_cache.find(regex) != flattened_regex_cache.end()) {
    return flattened_regex_cache[regex];
  }
  Node result;
  NodeManager* nm = NodeManager::currentNM();
  switch (regex.getKind()) {
    case Kind::STRING_TO_REGEXP: {
      Node re_str = regex[0];
      auto str_vec = string_flatten_deep(re_str);
      Node flat_str = utils::mkConcat(str_vec, nm->stringType());
      result = nm->mkNode(Kind::STRING_TO_REGEXP, flat_str);
      break;
    }
    case Kind::REGEXP_CONCAT:
    case Kind::REGEXP_PLUS:
    case Kind::REGEXP_OPT:
    case Kind::REGEXP_STAR:
    case Kind::REGEXP_COMPLEMENT:
    case Kind::REGEXP_INTER:
    case Kind::REGEXP_UNION: {
        std::vector<Node> children;
        for (auto c: regex) {
          Node c_flat = deeply_flatten_strings_in_regex(c);
          children.push_back(c_flat);
        }
        result =  nm->mkNode(regex.getKind(), children);
        break;
    }
    case Kind::REGEXP_LOOP: {
      Node lop = regex.getOperator();
      Node reg_inside = regex[0];
      Node ret_c = deeply_flatten_strings_in_regex(reg_inside);
      result =  nm->mkNode(Kind::REGEXP_LOOP, lop, ret_c);
      break;
    }
    default: {
        if (regex.getMetaKind() == MetaKind::CONSTANT) {
          return regex;
          break;
        }
        // Trace("regexp-brzo-rewrite-debug") << "In default case for deeply_flatten_strings_in_regex() for regex " << regex << std::endl;
        return regex;
    }
  }
  // cache the result
  flattened_regex_cache[regex] = result;
  return result;
}


// Removes chr from str from back if reverse is true, and from front if reverse is false
// requirement: `chr` must be constant string of length 1, or a variable, skolem, or STRING_REV kind
//               `str` must not have any "" unless it is itself "", and it must be deeply flattened. So, there should
//                not be any STRING_CONCAT inside the first level child.
// returns: Null if trimming failed due to presence of variable/skolem etc. For example, for str = "ab"  , chr = var_X, we would return Node::null()
// returns remaining string if prefix/suffix is found. For example, for str = "abc" , chr = "a", we would return "bc"
// returns d_emptyLanguage if prefix/suffix is not there. For example, for str = "a" , chr = "b", we would return d_emptyLanguage
Node trimChrFromDirection(const Node& str, const Node& chr, const bool reverse) {
  NodeManager* nm = NodeManager::currentNM();
  Node d_emptyWord = Word::mkEmptyWord(nm->stringType());
  Node d_emptyLanguage = nm->mkNode(Kind::REGEXP_NONE);
  Trace("regexp-brzo-rewrite-debug") << "Trimming a unit-length string (prefix/suffix) " << chr << " from " << str << " in direction (0 is left to right) " << reverse << std::endl;
  Assert((chr.isConst() && Word::getLength(chr) == 1) || (chr.getKind() == Kind::SKOLEM || chr.getKind() == Kind::VARIABLE || chr.getKind() == Kind::STRING_REV));
  if (chr.isConst() && Word::isEmpty(chr)) {
    return str;
  }
  else if (str == chr) {
    return d_emptyWord;
  }
  else if (str.isConst() && chr.isConst()) {
      Node ret;
      if (!reverse) {
        ret = Word::hasPrefix(str, chr)
                ? Word::substr(str, 1, Word::getLength(str)-1)
                : d_emptyLanguage;
      }
      else {
        ret = Word::hasSuffix(str, chr)
                ? Word::substr(str, 0, Word::getLength(str)-1)
                : d_emptyLanguage;
      }
      return ret;
  }
  else if (str.getKind() == Kind::STRING_CONCAT) {
    Node child_to_check = reverse? str[str.getNumChildren()-1] : str[0];
    Node res = trimChrFromDirection(child_to_check, chr, reverse);
    if (res == Node::null()) return Node::null(); // If the last step failed, then we fail.
    std::vector<Node> children;
    if (reverse) {
      // Note that we do not add the last child in this loop
      for (auto i = 0; i < str.getNumChildren()-1; i++) {
        children.push_back(str[i]);
      }
      if (res != d_emptyWord) children.push_back(res);
    }
    else {
      // We add the result as first child if it is not empty string
      if (res != d_emptyWord) children.push_back(res);
      for (auto i = 1; i < str.getNumChildren(); i++) {
        children.push_back(str[i]);
      }
    }
    return utils::mkConcat(children, nm->stringType());
  }
  return Node::null();
}

Node mkConcatRegex(std::vector<Node> children) {
    NodeManager* nm = NodeManager::currentNM();
    std::vector<Node> children_ret;
    for (auto c: children) {
      if (c.getKind() == Kind::REGEXP_NONE) {
        // If one of the regex in concatentation/intersection is \emptyset then whole concat is \emptyset
        // so, we can decide that the result has to be re.none
        return  nm->mkNode(Kind::REGEXP_NONE, {});
      }
      // We flatten all the concat children except those that are of the form (r1.r2*)
      if (c.getKind() == Kind::REGEXP_CONCAT && !(c.getNumChildren() == 2 && c[1].getKind() == Kind::REGEXP_STAR)) {
        for (auto cc: c) {
          children_ret.push_back(cc);
        }
      }
      else if (c.getKind() == Kind::STRING_TO_REGEXP && c[0].isConst() && Word::isEmpty(c[0])) {
        // ignore str.to_re "" in concatenations
        continue;
      }
      else {
        children_ret.push_back(c);
      }
    }
    return utils::mkConcat(children_ret, nm->regExpType());
}

Node mkUnionRegex(std::vector<Node> children) {
  NodeManager* nm = NodeManager::currentNM();
  std::set<Node> children_set;
  std::vector<Node> children_no_duplicates;
  for (auto c: children) {
    if (c.getKind() == Kind::REGEXP_UNION) {
      // append to children_set
      for (auto cc: c) {
        if (cc.getKind() == Kind::REGEXP_NONE) continue;
        if (children_set.count(cc)>0) {
            continue;
        }
        else {
          children_set.insert(cc);
          children_no_duplicates.push_back(cc);
        }
      }
    }
    else if (c.getKind() == Kind::REGEXP_NONE) {
      // ignore empty language in a union
      continue;
    }
    else if (children_set.count(c)>0) {
            continue;
    }
    else {
      children_set.insert(c);
      children_no_duplicates.push_back(c);
    }
  }


  if (children_no_duplicates.size() == 0) {
    return nm->mkNode(Kind::REGEXP_NONE, {});
  }
  else if (children_no_duplicates.size() == 1) {
    return children_no_duplicates[0];
  }
  else {
    return nm->mkNode(Kind::REGEXP_UNION, children_no_duplicates);
  }
}

/**
 * We compute chr^{-1}regex.
 * Node chr represents one character or variable. Assume it is not STRING_CONCAT.
 * We return Node::null() when we fail to compute the derivative completely.
 */
Node RegExpEntail::brzo_consume_one(const Node& chr,
                      const Node& regex, const bool reverse)
{
  Trace("regexp-brzo-rewrite-debug") << "Brzo-consume on character " << chr << " of kind " << chr.getKind() << " and regex " << regex << " in direction (0 is left to right) " << reverse << std::endl;
  if (Word::isEmpty(chr)) {
    return regex;
  }
  if (!((chr.isConst() && Word::getLength(chr) == 1) || (chr.getKind() == Kind::SKOLEM || chr.getKind() == Kind::VARIABLE || chr.getKind() == Kind::STRING_REV))) {
    Trace("regexp-brzo-rewrite-debug") << "Brzo-consume on character " << chr << " of kind " << chr.getKind() << " and regex " << regex << " failed as chr is not of right kind/length" << std::endl;
    return Node::null();
  }

  // Check cache RegExpEntail::brzo_consume_one_cache
  auto cache_key = std::make_tuple(chr, regex, reverse);
  auto cache_val = RegExpEntail::brzo_consume_one_cache.find(cache_key);
  if (cache_val != RegExpEntail::brzo_consume_one_cache.end()) {
    Trace("regexp-brzo-rewrite-debug") << "Brzo-consume on character " << chr << " and regex " << regex << " found in cache" << std::endl;
    return cache_val->second;
  }

  NodeManager* nm = NodeManager::currentNM();
  Node d_emptyWord = Word::mkEmptyWord(nm->stringType());
  Node d_emptyWordRegex = nm->mkNode(Kind::STRING_TO_REGEXP, d_emptyWord);
  Node d_emptyLanguage = nm->mkNode(Kind::REGEXP_NONE, std::vector<Node>{});
  Node ret;
  switch (regex.getKind()) {
    case Kind::REGEXP_NONE:
      ret = nm->mkNode(Kind::REGEXP_NONE, std::vector<Node>{});
      break;
    case Kind::REGEXP_ALL: {
      // HS: Assuming REGEXP_ALL is equivalent to Sigma^*.
      // HS Note: (This is not a bug) If the given regex was syntactically (Sigma)^*, then we would go to REGEXP_STAR
      // case and taking derivative will fail for Kind::VARIABLE strings. But here, it succeeds.
      ret = regex;
      break;
    }
    case Kind::REGEXP_ALLCHAR:
      ret = chr.isConst() ? d_emptyWordRegex : Node::null();
      break;
    case Kind::STRING_TO_REGEXP: {
      Node re_str = regex[0];
      Trace("regexp-brzo-rewrite-debug") << push;
      Node result_re_str = trimChrFromDirection(re_str, chr, reverse);
      Trace("regexp-brzo-rewrite-debug") << pop;
      Trace("regexp-brzo-rewrite-debug") << "Result from trimming " << chr << " from " << re_str << " is " << result_re_str << std::endl;
      if (result_re_str == Node::null()) {
        // save the result in cache
        RegExpEntail::brzo_consume_one_cache[cache_key] = Node::null();
        return Node::null(); // check failed due to either non-const regex or non-const chr, or both
      }
      if (result_re_str == d_emptyLanguage) {
        ret = d_emptyLanguage;
      }
      else {
        ret = nm->mkNode(Kind::STRING_TO_REGEXP, result_re_str);
      }
      break;
    }
    case Kind::REGEXP_INTER: {
      // If one of the derivative gave us re.none, then we know that the whole things is re.none even if we failed to compute the derivative for other children
      bool encountered_null = false;
      bool encountered_re_none = false;
      vector<Node> children_ret;
      for (auto c: regex) {
        Trace("regexp-brzo-rewrite-debug") << push;
        Node ret_c = brzo_consume_one(chr, c, reverse);
        Trace("regexp-brzo-rewrite-debug") << pop;
        if (ret_c == d_emptyLanguage) {
          encountered_re_none = true;
          break;
        }
        if (ret_c == Node::null()) {
          encountered_null = true;
          // Note that encountered_null tells us that we could not compute deriviate
          // for some child of re.inter, however, we must continue to test because we might encounter_re_none later which might
          // make the whole expression equivalent to re.none. If we don't find re.none, then we fail in computing the derivative.
          continue;
        }
        children_ret.push_back(ret_c);
      }
      if (!encountered_re_none && encountered_null) {
        // if one of the derivative failed and none of the derivative gave us re.none, then we fail
        RegExpEntail::brzo_consume_one_cache[cache_key] = Node::null();
        return Node::null();
      }
      else if (encountered_re_none) {
        ret = d_emptyLanguage;
      }
      else {
        // If we did not encounter re.none, and the derivative of all children was successfully computed
        ret = nm->mkNode(Kind::REGEXP_INTER, children_ret);
      }
      break;
    }
    case Kind::REGEXP_CONCAT: {
      // Get all the childrens in a vector
      std::vector<Node> children_vec;
      utils::getConcat(regex, children_vec);
      if (reverse) std::reverse(children_vec.begin(), children_vec.end()); // reverse the children_vec

      // Detect if we are in R1 ++ R2* case when reverse = false (or equivalently, R2* ++ R1 when reverse = true)
      // In this case, we get (a^{-1}R_1 \cup v(R_1)a^{-1}R_2) R_2*, where v(R_1) = epsilon \in r_1
      if (children_vec.size() == 2 && children_vec[1].getKind() == Kind::REGEXP_STAR) {
        vector<Node> children_ret;
        Node R1 = children_vec[0];
        Node R2 = children_vec[1][0];
        Node eps_in_r1 = check_epsilon_in_re(R1);
        if (eps_in_r1 == Node::null()) {
          // cache
          RegExpEntail::brzo_consume_one_cache[cache_key] = Node::null();
          return Node::null();
        }
        Trace("regexp-brzo-rewrite-debug") << "Epsilon in R1 is " << eps_in_r1 << std::endl;
        Trace("regexp-brzo-rewrite-debug") << push;
        Node derivative_R1 = brzo_consume_one(chr, R1, reverse);
        Trace("regexp-brzo-rewrite-debug") << pop;
        if (derivative_R1 == Node::null()) {
          // cache
          RegExpEntail::brzo_consume_one_cache[cache_key] = Node::null();
          return Node::null();
        }
        children_ret.push_back(derivative_R1);
        if (eps_in_r1 == nm->mkConst(true)) {
          Trace("regexp-brzo-rewrite-debug") << push;
          Node derivative_R2 = brzo_consume_one(chr, R2, reverse);
          Trace("regexp-brzo-rewrite-debug") << pop;
          if (derivative_R2 == Node::null()) {
            // cache
            RegExpEntail::brzo_consume_one_cache[cache_key] = Node::null();
            return Node::null();
          }
          children_ret.push_back(derivative_R2);
        }
        Assert(children_ret.size() > 0);
        Node reg_union;
        if (children_ret.size() == 1) {
          reg_union = children_ret[0];
        }
        else {
          reg_union = mkUnionRegex(children_ret); // create the union
        }
        std::vector<Node> children_for_concat = {reg_union, children_vec[1]};
        // We have to again reverse the concatenation's children here if reverse is true
        if (reverse) std::reverse(children_for_concat.begin(), children_for_concat.end());
        ret = mkConcatRegex(children_for_concat); // concatenate R2* at the end.
        RegExpEntail::brzo_consume_one_cache[cache_key] = ret;
      }
      else {
        // If it a not a concatenation of the form R1 ++ R2* if reverse = true
        /**
         * We do following to compute c^{-1}(R1R2R3)
         * 0. Let U = {}
         * 1. Compute dR1 = c^{-1}R_1.
         * 2. if dR1 is successfully computed, then we add (dR1).R2R3 to the vector U.
         * 3. if R1 does not contain epsilon, then we just return the re.union U.
         * 4. If R1 does contain epsilon, then we also need to compute c^{-1}(R2R3).
         * 4.1. We compute dR2 = c^{-1}R2. If dR2 is successfully computed, then we add (dR2).R3 to the vector U.
         * 4.2. We check if R2 contains epsilon. If it does not, we return re.union U.
         * 4.3. If R2 contains epsilon, then we also need to compute c^{-1}(R3). If dR3 is successfully computed, then we add (dR3) to the vector U.
         * 5. We return the re.union U = (a^-1R1)R2R3 \cup (a^{-1}R2)R3 \cup (a^{-1}R3)
         */
        vector<Node> children_ret_union;
        vector<vector<Node>> concat_children_of_union;
        uint32_t ind = 0;
        for (ind = 0; ind < children_vec.size(); ind++) {
          // The regex we are processing at this iteration is: R_{ind}R_{ind+1}R_{ind+2}...R_{regex.getNumChildren()-1}
          Node c = children_vec[ind];
          // Optimization is this: when we have a long concat: R1.R2.R3.R4.R5, suppose R2 does not contain "" but R1 does, then we
          // get the following optimized result (a^{-1}R1R2 \cup a^{-1}R2)R3R4R5
          for (auto& children: concat_children_of_union) {
            children.push_back(c);
          }
          Trace("regexp-brzo-rewrite-debug") << push;
          Node ret_c = brzo_consume_one(chr, c, reverse);
          Trace("regexp-brzo-rewrite-debug") << pop;
          if (ret_c == Node::null()) {
            // cache
            RegExpEntail::brzo_consume_one_cache[cache_key] = Node::null();
            return Node::null();
          }
          concat_children_of_union.push_back({ret_c});
          auto has_epsilon = check_epsilon_in_re(c);
          Trace("regexp-brzo-rewrite-debug") << "Epsilon in c is " << has_epsilon << std::endl;
          if (has_epsilon == Node::null()) {
            // cache
            RegExpEntail::brzo_consume_one_cache[cache_key] = Node::null();
            return Node::null(); // if we cannot decide has_epsilon, then we fail
          }
          if (has_epsilon == nm->mkConst(false)) break; else continue;
        }
        // make concat of each vector inside concat_children_of_union and make a union of the top
        vector<Node> new_childrens;
        for (auto& c: concat_children_of_union) {
          // reverse all children
          if (reverse) std::reverse(c.begin(), c.end());
          new_childrens.push_back(mkConcatRegex(c));
        }
        Node final_left_union = mkUnionRegex(new_childrens);
        // make a concat of all the children remaining from ind+1 onward
        vector<Node> final_concat_vec;
        final_concat_vec.push_back(final_left_union);
        for (int i = ind+1; i < children_vec.size(); i++) {
            final_concat_vec.push_back(children_vec[i]);
        }
        // Finally, reverse the final_concat_vec if reverse is true
        if (reverse) std::reverse(final_concat_vec.begin(), final_concat_vec.end());
        Node opt_result = mkConcatRegex(final_concat_vec);
        Trace("regexp-brzo-rewrite-debug") << "Optimized result is " << opt_result << std::endl;
        ret = opt_result;
        RegExpEntail::brzo_consume_one_cache[cache_key] = ret;
      }
      break;
    }
    case Kind::REGEXP_UNION: {
      // Even if we cannot compute the derivative for all the children of the union, we might infer that some of
      // the children have derivative equal to re.none, and we can at least simplify the regular expression
      // that we need to check the membership for. We DON'T attempt to do this here to keep things clean.

      // For example, a \in (re.union regexA (str.to_re "b")) is equivalent to a \in regexA.
      // We are not handling this kind of simplifications here.
      vector<Node> children_ret;
      for (auto c: regex) {
        Trace("regexp-brzo-rewrite-debug") << push;
        Node ret_c = brzo_consume_one(chr, c, reverse);
        Trace("regexp-brzo-rewrite-debug") << pop;
        if (ret_c == Node::null()) {
          // cache
          RegExpEntail::brzo_consume_one_cache[cache_key] = Node::null();
          return Node::null();
        }
        children_ret.push_back(ret_c);
      }
      ret = mkUnionRegex(children_ret);
      RegExpEntail::brzo_consume_one_cache[cache_key] = ret;
      break;
    }
    case Kind::REGEXP_STAR: {
      Node reg_inside = regex[0];
      Trace("regexp-brzo-rewrite-debug") << push;
      Node derivative_reg_inside = brzo_consume_one(chr, reg_inside, reverse);
      Trace("regexp-brzo-rewrite-debug") << pop;
      if (derivative_reg_inside == Node::null()) {
        // cache
        RegExpEntail::brzo_consume_one_cache[cache_key] = Node::null();
        return Node::null();
      }
      std::vector<Node> children_concat = {derivative_reg_inside, regex};
      if (reverse) std::reverse(children_concat.begin(), children_concat.end());
      ret = mkConcatRegex(children_concat);
      RegExpEntail::brzo_consume_one_cache[cache_key] = ret;
      break;
    }
    case Kind::REGEXP_PLUS: {
      // R+ \equiv R ++ R*
      Node reg_star = nm->mkNode(Kind::REGEXP_STAR, regex[0]);
      Node equiv_regex = mkConcatRegex({regex[0], reg_star});
      Trace("regexp-brzo-rewrite-debug") << push;
      ret = brzo_consume_one(chr, equiv_regex, reverse);
      Trace("regexp-brzo-rewrite-debug") << pop;
      break;
    }
    case Kind::REGEXP_OPT: {
      // As chr cannot be empty string, for us, R? is behaves same as R.
      Node reg_inside = regex[0];
      ret = brzo_consume_one(chr, reg_inside, reverse);
      break;
    }
    case Kind::REGEXP_RANGE: {
      if (!regex[0].isConst() || !regex[1].isConst() || !chr.isConst()) {
        // we cannot handle ranges if either of the bounds are not constant, or the given character/string is not a constant
        return Node::null();
      }

      String a = regex[0].getConst<String>();
      String b = regex[1].getConst<String>();
      String c = chr.getConst<String>();
      ret = (a <= c && c <= b) ? d_emptyWordRegex : d_emptyLanguage;;
      break;
    }
    case Kind::REGEXP_LOOP: {
      // HS Caution: Not clear about the structure of the regexp_loop node
      uint32_t l = utils::getLoopMinOccurrences(regex);
      uint32_t u = utils::getLoopMaxOccurrences(regex);
      if (l > u || (l == u && l == 0)) {
        // cache
        RegExpEntail::brzo_consume_one_cache[cache_key] = d_emptyLanguage;
        return d_emptyLanguage;
      }
      Node reg_inside = regex[0];
      Trace("regexp-brzo-rewrite-debug") << "The regex inside the regex loop " << regex << " is " << reg_inside << std::endl;
      Node derivative_reg_inside = brzo_consume_one(chr, reg_inside, reverse);
      if (derivative_reg_inside == Node::null()) {
        // cache
        RegExpEntail::brzo_consume_one_cache[cache_key] = Node::null();
        return Node::null();
      }
      Node lop = nm->mkConst(RegExpLoop(l == 0 ? 0 : (l - 1), u - 1));
      Node r2 = nm->mkNode(Kind::REGEXP_LOOP, lop, regex[0]);
      std::vector<Node> children_concat = {derivative_reg_inside, r2};
      if (reverse) std::reverse(children_concat.begin(), children_concat.end());
      ret = mkConcatRegex(children_concat);
      break;
    }
    case Kind::REGEXP_COMPLEMENT: {
      Node reg_inside = regex[0];
      Node derivative_reg_inside = brzo_consume_one(chr, reg_inside, reverse);
      if (derivative_reg_inside == Node::null()) return Node::null();
      ret = nm->mkNode(Kind::REGEXP_COMPLEMENT, std::vector<Node>{derivative_reg_inside});
      break;
    }
    default:
      {
        return Node::null();
      }
      break;
  }
  Trace("regexp-brzo-rewrite-debug") << "Brzo-consume-one's result is " << ret << std::endl;
  return ret;
}

static int sizeofnode(const Node& regex) {
  int s = 0;
  for (const Node& c : regex) {
    s += sizeofnode(c);
  }
  s += 1;
  return s;
}


// Assumes that str_vec is vector of strings none of which is STRING_CONCAT type.
// @requirement call this with str_vec that was from deeply_flattened_strings and
// regex that has been modified with deeply_flatten_strings_in_regex.
// Modifies the str_vec in-place according to how much it was consumed
// If smallest_result_found == Node::null(), then the computation for the smallest result is not done
Node RegExpEntail::brzo_consume_string(std::vector<Node>& str_vec, const Node& regex, const bool reverse, Node& smallest_result_found) {
  // We want to pop characters from the str_vec, so we reverse the str_vec
  // if reverse is false!
  if (!reverse) std::reverse(str_vec.begin(), str_vec.end());
  // We also want to keep track of the smallest_regex + remaining string that we see in this function
  NodeManager* nm = NodeManager::currentNM();
  Node d_emptyLanguage = nm->mkNode(Kind::REGEXP_NONE);
  Node smallest_regex = regex;
  Node prev_result = regex;
  Node curr_result = regex;
  while (curr_result != Node::null() && str_vec.size() > 0) {
    if (curr_result == d_emptyLanguage) {
      str_vec.clear();                 // We should clear the str_vec as everything will be consumed by re.none and final result will still be re.none
      return d_emptyLanguage;
    }
    Node chr = str_vec.back();
    Trace("regexp-brzo-rewrite-debug") << "Processing character in brzo_consume_string" << chr << std::endl;
    Trace("regexp-brzo-rewrite-debug") << "Current result is " << curr_result << std::endl;
    if (chr.getKind() == Kind::CONST_STRING) {
        str_vec.pop_back();
        // We expand the chr
        auto vec_chars = Word::getChars(chr);
        if (!reverse) std::reverse(vec_chars.begin(), vec_chars.end());
        while (vec_chars.size() > 0) {
          Node letter = vec_chars.back();
          Trace("regexp-brzo-rewrite-debug") << "Processing letter in brzo_consume_string" << letter << std::endl;
          curr_result = brzo_consume_one(letter, curr_result, reverse);
          if (curr_result == Node::null()) break;
          else {
            vec_chars.pop_back();
            // To store the smallest result
            if (smallest_result_found != Node::null() && sizeofnode(curr_result)  <= sizeofnode(smallest_regex)) {
                Trace("regexp-brzo-rewrite-debug") << "Changing smallest regex from " << smallest_regex << " to " << curr_result << std::endl;
                smallest_regex = curr_result;
                // create a copy of str_vec
                std::vector<Node> str_vec_cpy(str_vec);
                if (vec_chars.size() != 0) {
                  // reverse str_vec_cpy for the reconstruction of the word temporarily
                  if (!reverse) std::reverse(vec_chars.begin(), vec_chars.end());
                  auto current_state_of_word = Word::mkWordFlatten(vec_chars);
                  if (!reverse) std::reverse(vec_chars.begin(), vec_chars.end());
                  str_vec_cpy.push_back(current_state_of_word);
                }
                // reverse str_vec_cpy
                if (!reverse) std::reverse(str_vec_cpy.begin(), str_vec_cpy.end());
                auto current_state_of_string = utils::mkConcat(str_vec_cpy, nm->stringType());
                smallest_result_found = nm->mkNode(Kind::STRING_IN_REGEXP, current_state_of_string, curr_result);
            }
            prev_result = curr_result;
          }
        }
        if (vec_chars.size() == 0) {}
        else {
          // We have **not** consumed all the characters in chr, so we create the remaining word back
          if (!reverse) std::reverse(vec_chars.begin(), vec_chars.end());
          Node rem_chr = Word::mkWordFlatten(vec_chars);
          str_vec.push_back(rem_chr);
          break;
        }
    }
    else {
      curr_result = brzo_consume_one(chr, curr_result, reverse);
      if (curr_result == Node::null()) break;
      else {
        prev_result = curr_result;
        str_vec.pop_back();
        if (smallest_result_found != Node::null() && sizeofnode(curr_result)  <= sizeofnode(smallest_regex) ) {
           Trace("regexp-brzo-rewrite-debug") << "Changing smallest regex from " << smallest_regex << " to " << curr_result << std::endl;
            smallest_regex = curr_result;
            // We have already popped the last element of str_vec.
            if (!reverse) std::reverse(str_vec.begin(), str_vec.end());
            // reverse str temporarily to create concat
            auto current_state_of_string = utils::mkConcat(str_vec, nm->stringType());
            if (!reverse) std::reverse(str_vec.begin(), str_vec.end());
            smallest_result_found = nm->mkNode(Kind::STRING_IN_REGEXP, current_state_of_string, curr_result);
        }
      }
    }
  }
  if (!reverse) std::reverse(str_vec.begin(), str_vec.end());
  Trace("regexp-brzo-rewrite-debug") << "Smallest result I found was " << smallest_result_found << std::endl;
  return prev_result;
}

Node RegExpEntail::brzo_consume_left_right(const Node& str, const Node& regex, bool return_smallest = false) {
  Trace("regexp-brzo-rewrite-debug") << "\n*****************\nBrzo_consume_left_right on string " << str << " and regex " << regex << std::endl;
  Trace("regexp-brzo-rewrite-debug")  << push;
  NodeManager* nm = NodeManager::currentNM();
  auto str_vec = string_flatten_deep(str);
  Node _regex = deeply_flatten_strings_in_regex(regex);
  // Consume from left
  Node smallest_result_inside = Node::null();
  if (return_smallest)  smallest_result_inside = nm->mkNode(Kind::STRING_IN_REGEXP, str, regex); // initially it is the full problem
  Node result = brzo_consume_string(str_vec, _regex, false, smallest_result_inside);
  Trace("regexp-brzo-rewrite-debug") << "Result from consuming from left " << result <<std::endl;
  // Consume from right
  result = brzo_consume_string(str_vec, result, true, smallest_result_inside);
  Trace("regexp-brzo-rewrite-debug") << "Result from consuming from right " << result <<std::endl;
  Trace("regexp-brzo-rewrite-debug")  << pop;
  if (result == Node::null()) return Node::null();

  Node ret;
  if (str_vec.size() == 0 ) {
    Trace("regexp-brzo-rewrite-debug") << "Fully consumed the string " << str << std::endl;
    auto has_epsilon =  check_epsilon_in_re(result);
    Node d_emptyWord = Word::mkEmptyWord(nm->stringType());
    if (has_epsilon == Node::null()) {
      // We couldn't decide if epsilon is in the reduced string.
      ret = nm->mkNode(Kind::STRING_IN_REGEXP, d_emptyWord, result);
    }
    else {
      return has_epsilon;
    }
  }
  else {
    // create the string back
    Node rem_str = utils::mkConcat(str_vec, nm->stringType());
    ret = nm->mkNode(Kind::STRING_IN_REGEXP, rem_str, result);
    Trace("regexp-brzo-rewrite-debug") << "Brzo_consume_left_right ret before simp: " << ret << std::endl;
  }
  if (return_smallest) {
      Trace("regexp-brzo-rewrite-debug") << "Brzo_consume_left_right smallest return: " << smallest_result_inside << std::endl;
    return smallest_result_inside;
  }

  return ret;
}

bool RegExpEntail::brzo_eval_str_in_re(const Node& str, const Node& regex) {
  Trace("regexp-brzo-rewrite-debug") << "Brzo-eval-str-in-re on string " << str << " and regex " << regex << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  auto str_vec = string_flatten_deep(str);
  Node _ignore;
  Node result = brzo_consume_string(str_vec, regex, false, _ignore);

  if (result == Node::null() || str_vec.size() != 0) {
    Trace("regexp-brzo-rewrite-debug") << "Could not evaluate memebership via brzo_eval_str_in_re" << std::endl;
    Unreachable();
  }
  Node has_epsilon = check_epsilon_in_re(result);
  if (has_epsilon == nm->mkConst(true)) return true;
  else if (has_epsilon == nm->mkConst(false)) return false;
  else Unreachable();
}

/**** End AWS Updates ****/

Node RegExpEntail::simpleRegexpConsume(std::vector<Node>& mchildren,
                                       std::vector<Node>& children,
                                       int dir)
{
  Trace("regexp-ext-rewrite-debug")
      << "Simple reg exp consume, dir=" << dir << ":" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  unsigned tmin = dir < 0 ? 0 : dir;
  unsigned tmax = dir < 0 ? 1 : dir;
  // try to remove off front and back
  for (unsigned t = 0; t < 2; t++)
  {
    if (tmin <= t && t <= tmax)
    {
      Trace("regexp-ext-rewrite-debug")
          << "Run consume, direction is " << t << " with:" << std::endl;
      Trace("regexp-ext-rewrite-debug")
          << "  mchildren : " << mchildren << std::endl;
      Trace("regexp-ext-rewrite-debug")
          << "  children : " << children << std::endl;
      bool do_next = true;
      while (!children.empty() && !mchildren.empty() && do_next)
      {
        do_next = false;
        Node xc = mchildren[mchildren.size() - 1];
        Node rc = children[children.size() - 1];
        Trace("regexp-ext-rewrite-debug")
            << "* " << xc << " in " << rc << std::endl;
        Assert(rc.getKind() != Kind::REGEXP_CONCAT);
        Assert(xc.getKind() != Kind::STRING_CONCAT);
        if (rc.getKind() == Kind::STRING_TO_REGEXP)
        {
          std::vector<Node> childrenc;
          utils::getConcat(rc[0], childrenc);
          size_t cindex = t == 1 ? 0 : childrenc.size() - 1;
          Node rcc = childrenc[cindex];
          Node remStr;
          if (xc == rcc)
          {
            mchildren.pop_back();
            do_next = true;
            Trace("regexp-ext-rewrite-debug") << "- strip equal" << std::endl;
          }
          else if (rcc.isConst() && Word::isEmpty(rcc))
          {
            Trace("regexp-ext-rewrite-debug")
                << "- ignore empty RE" << std::endl;
            // ignore and continue
            do_next = true;
          }
          else if (xc.isConst() && rcc.isConst())
          {
            // split the constant
            size_t index;
            remStr = Word::splitConstant(xc, rcc, index, t == 0);
            Trace("regexp-ext-rewrite-debug")
                << "- CRE: Regexp const split : " << xc << " " << rcc << " -> "
                << remStr << " " << index << " " << t << std::endl;
            if (remStr.isNull())
            {
              Trace("regexp-ext-rewrite-debug")
                  << "...return false" << std::endl;
              return nm->mkConst(false);
            }
            else
            {
              Trace("regexp-ext-rewrite-debug")
                  << "- strip equal const" << std::endl;
              mchildren.pop_back();
              if (index == 0)
              {
                mchildren.push_back(remStr);
                // we've processed the remainder as leftover for the LHS
                // string, clear it now
                remStr = Node::null();
              }
              // otherwise remStr is processed below
            }
            Trace("regexp-ext-rewrite-debug") << "- split const" << std::endl;
            do_next = true;
          }
          if (do_next)
          {
            if (remStr.isNull())
            {
              // we have fully processed the component
              childrenc.erase(childrenc.begin() + cindex);
            }
            else
            {
              // we have a remainder
              childrenc[cindex] = remStr;
            }
            if (childrenc.empty())
            {
              // if childrenc is empty, we are done with the current str.to_re
              children.pop_back();
            }
            else
            {
              // otherwise we reconstruct it
              TypeNode stype = nm->stringType();
              children[children.size() - 1] = nm->mkNode(
                  Kind::STRING_TO_REGEXP, utils::mkConcat(childrenc, stype));
            }
          }
        }
        else if (xc.isConst())
        {
          // check for constants
          cvc5::internal::String s = xc.getConst<String>();
          if (Word::isEmpty(xc))
          {
            Trace("regexp-ext-rewrite-debug") << "- ignore empty" << std::endl;
            // ignore and continue
            mchildren.pop_back();
            do_next = true;
          }
          else if (rc.getKind() == Kind::REGEXP_RANGE
                   || rc.getKind() == Kind::REGEXP_ALLCHAR)
          {
            if (!isConstRegExp(rc))
            {
              // if a non-standard re.range term, abort
              break;
            }
            std::vector<unsigned> ssVec;
            ssVec.push_back(t == 0 ? s.back() : s.front());
            cvc5::internal::String ss(ssVec);
            if (testConstStringInRegExp(ss, rc))
            {
              // strip off one character
              mchildren.pop_back();
              if (s.size() > 1)
              {
                if (t == 0)
                {
                  mchildren.push_back(nm->mkConst(s.substr(0, s.size() - 1)));
                }
                else
                {
                  mchildren.push_back(nm->mkConst(s.substr(1)));
                }
              }
              children.pop_back();
              do_next = true;
            }
            else
            {
              Trace("regexp-ext-rewrite-debug")
                  << "...return false" << std::endl;
              return nm->mkConst(false);
            }
          }
          else if (rc.getKind() == Kind::REGEXP_INTER
                   || rc.getKind() == Kind::REGEXP_UNION)
          {
            // see if any/each child does not work
            bool result_valid = true;
            Node result;
            Node emp_s = nm->mkConst(String(""));
            for (unsigned i = 0; i < rc.getNumChildren(); i++)
            {
              std::vector<Node> mchildren_s;
              std::vector<Node> children_s;
              mchildren_s.push_back(xc);
              utils::getConcat(rc[i], children_s);
              Trace("regexp-ext-rewrite-debug") << push;
              Node ret = simpleRegexpConsume(mchildren_s, children_s, t);
              Trace("regexp-ext-rewrite-debug") << pop;
              if (!ret.isNull())
              {
                // one conjunct cannot be satisfied, return false
                if (rc.getKind() == Kind::REGEXP_INTER)
                {
                  Trace("regexp-ext-rewrite-debug")
                      << "...return " << ret << std::endl;
                  return ret;
                }
              }
              else
              {
                if (children_s.empty())
                {
                  // if we were able to fully consume, store the result
                  Assert(mchildren_s.size() <= 1);
                  if (mchildren_s.empty())
                  {
                    mchildren_s.push_back(emp_s);
                  }
                  if (result.isNull())
                  {
                    result = mchildren_s[0];
                  }
                  else if (result != mchildren_s[0])
                  {
                    result_valid = false;
                  }
                }
                else
                {
                  result_valid = false;
                }
              }
            }
            if (result_valid)
            {
              if (result.isNull())
              {
                // all disjuncts cannot be satisfied, return false
                Assert(rc.getKind() == Kind::REGEXP_UNION);
                Trace("regexp-ext-rewrite-debug")
                    << "...return false" << std::endl;
                return nm->mkConst(false);
              }
              else
              {
                Trace("regexp-ext-rewrite-debug")
                    << "- same result, try again, children now " << children
                    << std::endl;
                // all branches led to the same result
                children.pop_back();
                mchildren.pop_back();
                if (result != emp_s)
                {
                  mchildren.push_back(result);
                }
                do_next = true;
              }
            }
          }
          else if (rc.getKind() == Kind::REGEXP_STAR)
          {
            // check if there is no way that this star can be unrolled even once
            std::vector<Node> mchildren_s;
            mchildren_s.insert(
                mchildren_s.end(), mchildren.begin(), mchildren.end());
            if (t == 1)
            {
              std::reverse(mchildren_s.begin(), mchildren_s.end());
            }
            std::vector<Node> children_s;
            utils::getConcat(rc[0], children_s);
            Trace("regexp-ext-rewrite-debug")
                << "- recursive call on body of star" << std::endl;
            Trace("regexp-ext-rewrite-debug") << push;
            Node ret = simpleRegexpConsume(mchildren_s, children_s, t);
            Trace("regexp-ext-rewrite-debug") << pop;
            if (!ret.isNull())
            {
              Trace("regexp-ext-rewrite-debug")
                  << "- CRE : regexp star infeasable " << xc << " " << rc
                  << std::endl;
              children.pop_back();
              if (!children.empty())
              {
                Trace("regexp-ext-rewrite-debug") << "- continue" << std::endl;
                do_next = true;
              }
            }
            else
            {
              if (children_s.empty())
              {
                // Check if beyond this, we hit a conflict. In this case, we
                // must repeat.  Notice that we do not treat the case where
                // there are no more strings to consume as a failure, since
                // we may be within a recursive call, see issue #5510.
                bool can_skip = true;
                if (children.size() > 1)
                {
                  std::vector<Node> mchildren_ss;
                  mchildren_ss.insert(
                      mchildren_ss.end(), mchildren.begin(), mchildren.end());
                  std::vector<Node> children_ss;
                  children_ss.insert(
                      children_ss.end(), children.begin(), children.end() - 1);
                  if (t == 1)
                  {
                    std::reverse(mchildren_ss.begin(), mchildren_ss.end());
                    std::reverse(children_ss.begin(), children_ss.end());
                  }
                  Trace("regexp-ext-rewrite-debug")
                      << "- recursive call required repeat star" << std::endl;
                  Trace("regexp-ext-rewrite-debug") << push;
                  Node rets = simpleRegexpConsume(mchildren_ss, children_ss, t);
                  Trace("regexp-ext-rewrite-debug") << pop;
                  if (!rets.isNull())
                  {
                    can_skip = false;
                  }
                }
                if (!can_skip)
                {
                  TypeNode stype = nm->stringType();
                  Node prev = utils::mkConcat(mchildren, stype);
                  Trace("regexp-ext-rewrite-debug")
                      << "- can't skip" << std::endl;
                  // take the result of fully consuming once
                  if (t == 1)
                  {
                    std::reverse(mchildren_s.begin(), mchildren_s.end());
                  }
                  mchildren.clear();
                  mchildren.insert(
                      mchildren.end(), mchildren_s.begin(), mchildren_s.end());
                  Node curr = utils::mkConcat(mchildren, stype);
                  do_next = (prev != curr);
                  Trace("regexp-ext-rewrite-debug")
                      << "- do_next = " << do_next << std::endl;
                }
                else
                {
                  Trace("regexp-ext-rewrite-debug")
                      << "- can skip " << rc << " from " << xc << std::endl;
                }
              }
            }
          }
        }
        if (!do_next)
        {
          Trace("regexp-ext-rewrite")
              << "- cannot consume : " << xc << " " << rc << std::endl;
        }
      }
    }
    if (dir != 0)
    {
      std::reverse(children.begin(), children.end());
      std::reverse(mchildren.begin(), mchildren.end());
    }
  }
  Trace("regexp-ext-rewrite-debug") << "...finished, return null" << std::endl;
  return Node::null();
}

bool RegExpEntail::isConstRegExp(TNode t)
{
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(t);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      Kind ck = cur.getKind();
      if (ck == Kind::STRING_TO_REGEXP)
      {
        if (!cur[0].isConst())
        {
          return false;
        }
      }
      else if (ck == Kind::REGEXP_RV)
      {
        return false;
      }
      else if (ck == Kind::REGEXP_RANGE)
      {
        if (!utils::isCharacterRange(cur))
        {
          return false;
        }
      }
      else if (ck == Kind::ITE)
      {
        return false;
      }
      else if (cur.isVar())
      {
        return false;
      }
      else
      {
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
    }
  } while (!visit.empty());
  return true;
}

/**** AWS update: use Brzo functions ****/
bool RegExpEntail::testConstStringInRegExp(String& s, TNode r)
{
  // Let us check the membership with Brzo function
  NodeManager* nm = NodeManager::currentNM();
  Node str = nm->mkConst(s);
  Trace("regexp-brzo-rewrite-debug") << "Checking membership for str " << s << " in regex " << r << std::endl;
  bool result = brzo_eval_str_in_re(str, r);
  Trace("regexp-brzo-rewrite-debug") << "Result of membership check with Brzo " << result << std::endl;
  return result;
}
/**** End AWS update ****/

bool RegExpEntail::testConstStringInRegExpInternal(String& s,
                                                   unsigned index_start,
                                                   TNode r)
{
  Assert(index_start <= s.size());
  Trace("regexp-debug") << "Checking " << s << " in " << r << ", starting at "
                        << index_start << std::endl;
  Assert(!r.isVar());
  Kind k = r.getKind();
  switch (k)
  {
    case Kind::STRING_TO_REGEXP:
    {
      String s2 = s.substr(index_start, s.size() - index_start);
      if (r[0].isConst())
      {
        return (s2 == r[0].getConst<String>());
      }
      Assert(false) << "RegExp contains variables";
      return false;
    }
    case Kind::REGEXP_CONCAT:
    {
      if (s.size() != index_start)
      {
        std::vector<int> vec_k(r.getNumChildren(), -1);
        int start = 0;
        int left = (int)s.size() - index_start;
        int i = 0;
        while (i < (int)r.getNumChildren())
        {
          bool flag = true;
          if (i == (int)r.getNumChildren() - 1)
          {
            if (testConstStringInRegExpInternal(s, index_start + start, r[i]))
            {
              return true;
            }
          }
          else if (i == -1)
          {
            return false;
          }
          else
          {
            for (vec_k[i] = vec_k[i] + 1; vec_k[i] <= left; ++vec_k[i])
            {
              cvc5::internal::String t = s.substr(index_start + start, vec_k[i]);
              if (testConstStringInRegExpInternal(t, 0, r[i]))
              {
                start += vec_k[i];
                left -= vec_k[i];
                flag = false;
                ++i;
                vec_k[i] = -1;
                break;
              }
            }
          }

          if (flag)
          {
            --i;
            if (i >= 0)
            {
              start -= vec_k[i];
              left += vec_k[i];
            }
          }
        }
        return false;
      }
      else
      {
        for (unsigned i = 0; i < r.getNumChildren(); ++i)
        {
          if (!testConstStringInRegExpInternal(s, index_start, r[i]))
          {
            return false;
          }
        }
        return true;
      }
    }
    case Kind::REGEXP_UNION:
    {
      for (unsigned i = 0; i < r.getNumChildren(); ++i)
      {
        if (testConstStringInRegExpInternal(s, index_start, r[i]))
        {
          return true;
        }
      }
      return false;
    }
    case Kind::REGEXP_INTER:
    {
      for (unsigned i = 0; i < r.getNumChildren(); ++i)
      {
        if (!testConstStringInRegExpInternal(s, index_start, r[i]))
        {
          return false;
        }
      }
      return true;
    }
    case Kind::REGEXP_STAR:
    {
      if (s.size() != index_start)
      {
        for (unsigned i = s.size() - index_start; i > 0; --i)
        {
          cvc5::internal::String t = s.substr(index_start, i);
          if (testConstStringInRegExpInternal(t, 0, r[0]))
          {
            if (index_start + i == s.size()
                || testConstStringInRegExpInternal(s, index_start + i, r))
            {
              return true;
            }
          }
        }
        return false;
      }
      else
      {
        return true;
      }
    }
    case Kind::REGEXP_NONE:
    {
      return false;
    }
    case Kind::REGEXP_ALLCHAR:
    {
      if (s.size() == index_start + 1)
      {
        return true;
      }
      else
      {
        return false;
      }
    }
    case Kind::REGEXP_RANGE:
    {
      if (s.size() == index_start + 1)
      {
        unsigned a = r[0].getConst<String>().front();
        unsigned b = r[1].getConst<String>().front();
        unsigned c = s.back();
        return (a <= c && c <= b);
      }
      else
      {
        return false;
      }
    }
    case Kind::REGEXP_LOOP:
    {
      NodeManager* nm = NodeManager::currentNM();
      uint32_t l = r[1].getConst<Rational>().getNumerator().toUnsignedInt();
      if (s.size() == index_start)
      {
        return l == 0 || testConstStringInRegExpInternal(s, index_start, r[0]);
      }
      else if (l == 0 && r[1] == r[2])
      {
        return false;
      }
      else
      {
        Assert(r.getNumChildren() == 3)
            << "String rewriter error: LOOP has 2 children";
        if (l == 0)
        {
          // R{0,u}
          uint32_t u = r[2].getConst<Rational>().getNumerator().toUnsignedInt();
          for (unsigned len = s.size() - index_start; len >= 1; len--)
          {
            cvc5::internal::String t = s.substr(index_start, len);
            if (testConstStringInRegExpInternal(t, 0, r[0]))
            {
              if (len + index_start == s.size())
              {
                return true;
              }
              else
              {
                Node num2 = nm->mkConstInt(cvc5::internal::Rational(u - 1));
                Node r2 = nm->mkNode(Kind::REGEXP_LOOP, r[0], r[1], num2);
                if (testConstStringInRegExpInternal(s, index_start + len, r2))
                {
                  return true;
                }
              }
            }
          }
          return false;
        }
        else
        {
          // R{l,l}
          Assert(r[1] == r[2])
              << "String rewriter error: LOOP nums are not equal";
          if (l > s.size() - index_start)
          {
            if (testConstStringInRegExpInternal(s, s.size(), r[0]))
            {
              l = s.size() - index_start;
            }
            else
            {
              return false;
            }
          }
          for (unsigned len = 1; len <= s.size() - index_start; len++)
          {
            cvc5::internal::String t = s.substr(index_start, len);
            if (testConstStringInRegExpInternal(t, 0, r[0]))
            {
              Node num2 = nm->mkConstInt(cvc5::internal::Rational(l - 1));
              Node r2 = nm->mkNode(Kind::REGEXP_LOOP, r[0], num2, num2);
              if (testConstStringInRegExpInternal(s, index_start + len, r2))
              {
                return true;
              }
            }
          }
          return false;
        }
      }
    }
    case Kind::REGEXP_COMPLEMENT:
    {
      return !testConstStringInRegExpInternal(s, index_start, r[0]);
      break;
    }
    default:
    {
      Assert(!utils::isRegExpKind(k));
      return false;
    }
  }
}

bool RegExpEntail::hasEpsilonNode(TNode node)
{
  for (const Node& nc : node)
  {
    if (nc.getKind() == Kind::STRING_TO_REGEXP && Word::isEmpty(nc[0]))
    {
      return true;
    }
  }
  return false;
}

Node RegExpEntail::getFixedLengthForRegexp(TNode n)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n.getKind();
  if (k == Kind::STRING_TO_REGEXP)
  {
    if (n[0].isConst())
    {
      return nm->mkConstInt(Rational(Word::getLength(n[0])));
    }
  }
  else if (k == Kind::REGEXP_ALLCHAR || k == Kind::REGEXP_RANGE)
  {
    return nm->mkConstInt(Rational(1));
  }
  else if (k == Kind::REGEXP_UNION || k == Kind::REGEXP_INTER)
  {
    Node ret;
    for (const Node& nc : n)
    {
      Node flc = getFixedLengthForRegexp(nc);
      if (flc.isNull() || (!ret.isNull() && ret != flc))
      {
        return Node::null();
      }
      else if (ret.isNull())
      {
        // first time
        ret = flc;
      }
    }
    return ret;
  }
  else if (k == Kind::REGEXP_CONCAT)
  {
    Rational sum(0);
    for (const Node& nc : n)
    {
      Node flc = getFixedLengthForRegexp(nc);
      if (flc.isNull())
      {
        return flc;
      }
      Assert(flc.isConst() && flc.getType().isInteger());
      sum += flc.getConst<Rational>();
    }
    return nm->mkConstInt(sum);
  }
  return Node::null();
}

Node RegExpEntail::getConstantBoundLengthForRegexp(TNode n, bool isLower) const
{
  Assert(n.getType().isRegExp());
  Node ret;
  if (getConstantBoundCache(n, isLower, ret))
  {
    return ret;
  }
  Kind k = n.getKind();
  NodeManager* nm = NodeManager::currentNM();
  if (k == Kind::STRING_TO_REGEXP)
  {
    ret = d_aent.getConstantBoundLength(n[0], isLower);
  }
  else if (k == Kind::REGEXP_ALLCHAR || k == Kind::REGEXP_RANGE)
  {
    ret = d_one;
  }
  else if (k == Kind::REGEXP_UNION || k == Kind::REGEXP_INTER
           || k == Kind::REGEXP_CONCAT)
  {
    bool success = true;
    bool firstTime = true;
    Rational rr(0);
    for (const Node& nc : n)
    {
      Node bc = getConstantBoundLengthForRegexp(nc, isLower);
      if (bc.isNull())
      {
        if (k == Kind::REGEXP_UNION || (k == Kind::REGEXP_CONCAT && !isLower))
        {
          // since the bound could not be determined on the component, the
          // overall bound is undetermined.
          success = false;
          break;
        }
        else
        {
          // if intersection, or we are computing lower bound for concat
          // and the component cannot be determined, ignore it
          continue;
        }
      }
      Assert(bc.isConst() && bc.getType().isInteger());
      Rational r = bc.getConst<Rational>();
      if (k == Kind::REGEXP_CONCAT)
      {
        rr += r;
      }
      else if (firstTime)
      {
        rr = r;
      }
      else if ((k == Kind::REGEXP_UNION) == isLower)
      {
        rr = std::min(r, rr);
      }
      else
      {
        rr = std::max(r, rr);
      }
      firstTime = false;
    }
    // if we were successful and didn't ignore all components
    if (success && !firstTime)
    {
      ret = nm->mkConstInt(rr);
    }
  }
  if (ret.isNull() && isLower)
  {
    ret = d_zero;
  }
  Trace("strings-rentail") << "getConstantBoundLengthForRegexp: " << n
                           << ", isLower=" << isLower << " returns " << ret
                           << std::endl;
  setConstantBoundCache(n, ret, isLower);
  return ret;
}

bool RegExpEntail::regExpIncludes(Node r1,
                                  Node r2,
                                  std::map<std::pair<Node, Node>, bool>& cache)
{
  if (r1 == r2)
  {
    return true;
  }
  std::pair<Node, Node> key = std::make_pair(r1, r2);
  const auto& it = cache.find(key);
  if (it != cache.end())
  {
    return (*it).second;
  }
  // first, check some basic inclusions
  bool ret = false;
  Kind k2 = r2.getKind();
  // if the right hand side is a constant string, this is a membership test
  if (k2 == Kind::STRING_TO_REGEXP)
  {
    // only check if r1 is a constant regular expression
    if (r2[0].isConst() && isConstRegExp(r1))
    {
      String s = r2[0].getConst<String>();
      ret = testConstStringInRegExp(s, r1);
    }
    cache[key] = ret;
    return ret;
  }
  Kind k1 = r1.getKind();
  bool retSet = false;
  if (k1 == Kind::REGEXP_UNION)
  {
    retSet = true;
    // if any component of r1 includes r2, return true
    for (const Node& r : r1)
    {
      if (regExpIncludes(r, r2, cache))
      {
        ret = true;
        break;
      }
    }
  }
  if (k2 == Kind::REGEXP_INTER && !ret)
  {
    retSet = true;
    // if r1 includes any component of r2, return true
    for (const Node& r : r2)
    {
      if (regExpIncludes(r1, r, cache))
      {
        ret = true;
        break;
      }
    }
  }
  if (k1 == Kind::REGEXP_STAR)
  {
    retSet = true;
    // inclusion if r1 is (re.* re.allchar), or if the body of r1 includes r2
    // (or the body of r2 if it is also a star).
    if (r1[0].getKind() == Kind::REGEXP_ALLCHAR)
    {
      ret = true;
    }
    else
    {
      ret = regExpIncludes(r1[0], k2 == Kind::REGEXP_STAR ? r2[0] : r2, cache);
    }
  }
  else if (k1 == Kind::STRING_TO_REGEXP)
  {
    // only way to include is if equal, which was already checked
    retSet = true;
  }
  else if (k1 == Kind::REGEXP_RANGE && utils::isCharacterRange(r1))
  {
    retSet = true;
    // if comparing subranges, we check inclusion of interval
    if (k2 == Kind::REGEXP_RANGE && utils::isCharacterRange(r2))
    {
      unsigned l1 = r1[0].getConst<String>().front();
      unsigned u1 = r1[1].getConst<String>().front();
      unsigned l2 = r2[0].getConst<String>().front();
      unsigned u2 = r2[1].getConst<String>().front();
      ret = l1 <= l2 && l2 <= u1 && l1 <= u2 && u2 <= u1;
    }
  }
  if (retSet)
  {
    cache[key] = ret;
    return ret;
  }
  // avoid infinite loop
  cache[key] = false;
  NodeManager* nm = NodeManager::currentNM();
  Node sigma = nm->mkNode(Kind::REGEXP_ALLCHAR, std::vector<Node>{});
  Node sigmaStar = nm->mkNode(Kind::REGEXP_STAR, sigma);

  std::vector<Node> v1, v2;
  utils::getRegexpComponents(r1, v1);
  utils::getRegexpComponents(r2, v2);

  // In the following, we iterate over `r2` (the "includee") and try to
  // match it with `r1`. `idxs`/`newIdxs` keep track of all the possible
  // positions in `r1` that we could currently be at.
  std::unordered_set<size_t> newIdxs = {0};
  std::unordered_set<size_t> idxs;
  for (const Node& n2 : v2)
  {
    // Transfer elements from `newIdxs` to `idxs`. Out-of-bound indices are
    // removed and for (re.* re.allchar), we additionally include the option of
    // skipping it. Indices must be smaller than the size of `v1`.
    idxs.clear();
    for (size_t idx : newIdxs)
    {
      if (idx < v1.size())
      {
        idxs.insert(idx);
        if (idx + 1 < v1.size() && v1[idx] == sigmaStar)
        {
          Assert(idx + 1 == v1.size() || v1[idx + 1] != sigmaStar);
          idxs.insert(idx + 1);
        }
      }
    }
    newIdxs.clear();

    for (size_t idx : idxs)
    {
      if (regExpIncludes(v1[idx], n2, cache))
      {
        // If this component includes n2, then we can consume it.
        newIdxs.insert(idx + 1);
      }
      if (v1[idx] == sigmaStar)
      {
        // (re.* re.allchar) can match an arbitrary amount of `r2`
        newIdxs.insert(idx);
      }
      else if (utils::isUnboundedWildcard(v1, idx))
      {
        // If a series of re.allchar is followed by (re.* re.allchar), we
        // can decide not to "waste" the re.allchar because the order of
        // the two wildcards is not observable (i.e. it does not change
        // the sequences matched by the regular expression)
        newIdxs.insert(idx);
      }
    }

    if (newIdxs.empty())
    {
      // If there are no candidates, we can't match the remainder of r2
      break;
    }
  }

  // We have processed all of `r2`. We are now looking if there was also a
  // path to the end in `r1`. This makes sure that we don't have leftover
  // bits in `r1` that don't match anything in `r2`.
  bool result = false;
  for (size_t idx : newIdxs)
  {
    if (idx == v1.size() || (idx == v1.size() - 1 && v1[idx] == sigmaStar))
    {
      result = true;
      break;
    }
  }
  cache[key] = result;
  return result;
}

bool RegExpEntail::regExpIncludes(Node r1, Node r2)
{
  std::map<std::pair<Node, Node>, bool> cache;
  return regExpIncludes(r1, r2, cache);
}

struct RegExpEntailConstantBoundLowerId
{
};
typedef expr::Attribute<RegExpEntailConstantBoundLowerId, Node>
    RegExpEntailConstantBoundLower;

struct RegExpEntailConstantBoundUpperId
{
};
typedef expr::Attribute<RegExpEntailConstantBoundUpperId, Node>
    RegExpEntailConstantBoundUpper;

void RegExpEntail::setConstantBoundCache(TNode n, Node ret, bool isLower)
{
  if (isLower)
  {
    RegExpEntailConstantBoundLower rcbl;
    n.setAttribute(rcbl, ret);
  }
  else
  {
    RegExpEntailConstantBoundUpper rcbu;
    n.setAttribute(rcbu, ret);
  }
}

bool RegExpEntail::getConstantBoundCache(TNode n, bool isLower, Node& c)
{
  if (isLower)
  {
    RegExpEntailConstantBoundLower rcbl;
    if (n.hasAttribute(rcbl))
    {
      c = n.getAttribute(rcbl);
      return true;
    }
  }
  else
  {
    RegExpEntailConstantBoundUpper rcbu;
    if (n.hasAttribute(rcbu))
    {
      c = n.getAttribute(rcbu);
      return true;
    }
  }
  return false;
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
