module Harada where

postulate
  List : Set → Set
  DecisionTree : Set
  Pure : DecisionTree → Set
  Trie : Set
  Trie' : Set
  modifyTrie : List Trie → List Trie'
  makeDecisionTree : List Trie' → DecisionTree

Algorithm-X : List Trie → DecisionTree
Algorithm-X xs = makeDecisionTree (modifyTrie xs)

theorem : (xs : List Trie) → Pure (Algorithm-X xs)
theorem xs = {!!}
