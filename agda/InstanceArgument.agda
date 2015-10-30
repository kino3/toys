module InstanceArgument where
-- http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.InstanceArguments

postulate
  A B : Set
  f : {{ x : A }} → B

--instance postulate x : A

test' : A → B
test' _ = f

--error
--test : B
--test = f

module alter where
  instance postulate a a' : A
  test : B
  test = f {{a}} -- just "f" is yellow.

