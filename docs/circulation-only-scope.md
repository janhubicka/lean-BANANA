# Version-1 circulation-only scope

This candidate removes the external project dependencies on lean-successors and lean-ramsey-space-todorcevic. Only the pinned mathlib ecosystem remains. The complete verified development at fc0972fda0cc25ab94ab7315f6f57b7eed9127b9 is preserved in history.

The circulation manuscript explicitly cites the classical finite vector-space Ramsey theorem of Graham, Leeb and Rothschild in the one-sided BANANA degree-one proof. The proposition BinarySubspaceRamsey is an explicit premise of the reductions and full BANANA degree classification. It is not an added axiom. Mixed-source infinite degrees, persistent-colouring obstructions, symplectic degrees and other circulation endpoints are retained without this premise. The standalone package must be checked afresh.

The generic finite copy/expansion/degree interface is reproduced byte-for-byte from SuccessorTree/CopyRamsey.lean of https://github.com/janhubicka/lean-successors at d9be105f73ca5a0f3f411b87d4c2419d0eb94753 (blob 88ae3feeed2eeb7fc6a56d68d5b2934c03b2537e). Its namespace is unchanged; its only imports are mathlib. Original provenance and licensing are retained.

The production root is the local import closure of the 363 manuscript-linked declaration requirements, with GLR references replaced by the cited premise and conditional reductions and the generic copy-degree lemma relocated. Retained modules may contain ancillary declarations. Source and compiled-module checks prohibit the removed dependencies. Publication is paused pending strict standalone verification and revised manuscript markers/documentation. No frozen prose change is authorised.
