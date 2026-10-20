Anthropic lottery choice representation: completed Lean certificate
=================================================================

The main entry module is AnthropicRepresentation.lean. Every retained proof is
complete. The bundle contains no proof placeholders or project-specific axioms.

Pinned configuration
--------------------
Lean: leanprover/lean4:v4.33.1
Lean commit: 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
mathlib: 0df444a360eaa60ab8c11dca51a86af692955474 (release v4.33.1)
The included lake-manifest.json pins all transitive dependency revisions.

Reproduce
---------
From this directory, with elan/Lean available:

  lake exe cache get
  lake build
  lake env lean AnthropicRepresentation.lean
  lake env lean AnthropicRepresentation/PublicContract.lean

The first command obtains cached mathlib artefacts; it is unnecessary when the
pinned dependencies and their cache are already present. No upgrade is needed.
The default library build includes both the entry and PublicContract modules.

The standalone project was built from these sources, reusing the existing pinned
dependency cache through a local .lake/packages junction. No project proof
artefacts were copied into its fresh build directory. The junction and build
cache are excluded from the ZIP; the project configuration has no local paths.
The sources were also checked in the pre-existing research-workspace project.

Exact recorded commands, exit codes, and unabridged output are in verification/.
commands.txt records the Windows commands actually used. build.txt is the
standalone project build; workspace-build.txt is the existing project build;
entry-audit.txt evaluates all entry-file audit commands; public-contract.txt
checks fully explicit public types and prints the protected definitions and
helper dependencies. versions.txt records the toolchain and dependency commit.

Claim-to-declaration map (all names below are within LotteryChoice)
----------------------------------------------------------------
Existence: representation_of_axioms in Existence.lean.
Converse: axioms_of_representation in Converse.lean.
Equivalence: representation_iff in the entry module.
Actual-payoff restriction: delib, V, and delib_iff in the entry module.
Probability uniqueness from full ticket preferences: R_unique in Uniqueness.lean.
One common positive affine utility transformation: u_unique in Uniqueness.lean.
Positive affine invariance: Representation.positiveAffine, positiveAffine_u,
  and positiveAffine_R in Converse.lean; distributions are retained exactly.
Scenario specialisation: Paper.representation_iff, Paper.deliberation_iff,
  Paper.R_unique, and Paper.u_unique in the entry module. The actual payoff map
  has type (Gamma : Problem) -> Z Gamma -> Lottery X and is independent of the
  information label and contemplated action.

Proof dependencies
------------------
Basic.lean preserves the supplied lotteries, mixtures, labelled tickets,
behavioural axioms, expected value, and representation structure.
Finite.lean proves extrema among pure prizes, finite affinity via the convex
graph of an affine functional, and the extraction of normalised terminal weights.
Normalised.lean constructs the unique indifferent benchmark parameter from
connectedness and the two closed preference sets, and proves affinity.
Uniqueness.lean proves affine uniqueness independently of existence, then aligns
normalised constants. Probability uniqueness uses indicator tickets and remains
valid when terminal probabilities are zero.
Existence.lean derives nonemptiness and strict common bounds from nondegeneracy,
aligns the local values, extracts probabilities, and uses calibration and
transitivity for comparisons across scenarios at the same site.

The finite-mixture proof uses mathlib's Convex.sum_mem, whose checked proof
handles zero residual weights explicitly in Convex.centerMass_mem:
https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Convex/Combination.lean
The normalised helper uses isPreconnected_closed_iff from mathlib:
https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Connected/Basic.lean
No external expected-utility representation theorem is assumed.

Contract and kernel checks
--------------------------
PublicContract.lean assigns each required declaration, with @ exposing all
implicit parameters and typeclasses, to the original fully explicit expected
type. It also prints the protected definitions. These are separate checks from
the axiom audit, which reports only propext, Classical.choice, and Quot.sound
for every required result, including existence and converse themselves.

compare-contract.ps1 mechanically compares the protected core declarations,
delib/V and delib_iff, and the entire Paper adapter with the supplied source.
The comparison ignores only line endings and surrounding whitespace. All three
comparisons passed; the genuine output and input SHA-256 are recorded in
verification/contract-comparison.txt. No public assumption or conclusion was
added, removed, or weakened. Arbitrary scenarios/sites, full real lotteries,
cross-scenario common objective rankings, zero terminal probabilities, and the
problem-only actual-payoff map are retained.

To repeat the source comparison against the original supplied file in PowerShell:

  ./verification/compare-contract.ps1 -Original /path/to/original/AnthropicRepresentation.lean

The original supplied file is not modified or included as a second proof source.
SHA256SUMS.txt identifies every delivered source, configuration, and audit log.
