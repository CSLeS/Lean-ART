# A computer-checkable proof of the anthropic representation theorem

**What to share:** this entire repository, especially the green check from its
**Verify Lean proof** GitHub Actions workflow. The `.lean` files are the proof;
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin the software
needed to check it independently. The `verification/` folder contains logs from
the original build but those logs are not a substitute for running the checker.

The key formal statement is `LotteryChoice.representation_iff` in
`AnthropicRepresentation.lean`. The existence and converse proofs are in
`AnthropicRepresentation/Existence.lean` and
`AnthropicRepresentation/Converse.lean`. There are also checked probability and
utility uniqueness results, a deliberation corollary, and an explicit adapter for
scenarios labelled by problems, information sets, and contemplated actions.

## For a reader with no Lean installation

1. Open the GitHub repository.
2. Click **Actions**, then **Verify Lean proof**, then the latest completed run.
3. A **green check** means GitHub rebuilt the project, checked the compiled
   declarations with Lean's `leanchecker`, checked the published theorem's
   axiom dependencies against a short allowlist, and compiled the source file
   that checks the exact public theorem types. A red cross means that run failed.
4. If desired, click the run's job for the exact build output. To reproduce it
   yourself, download the repository and follow the commands below.

The GitHub workflow is **provided but has not been executed in this chat**.
The source ZIP included successful builds and axiom checks performed in the
originating Codex environment; GitHub will provide a fresh check when you upload
it to your repository.

## Reproduce on a computer with Lean installed

In the root folder (the folder containing `lakefile.toml`) run:

```bash
lake exe cache get
lake build
lake env lean AnthropicRepresentation.lean
lake env lean AnthropicRepresentation/PublicContract.lean
```

Lean version: `leanprover/lean4:v4.33.1`; mathlib revision:
`0df444a360eaa60ab8c11dca51a86af692955474`.

The source-only code is a certificate of the *formal statement in the Lean files*.
That is not, by itself, a proof that every English-language interpretation of
the informal theorem is identical to the formal statement. `PublicContract.lean`
performs checks of the expected formal signatures, and the proof bundle preserves
the declared mathematical primitives.

## Publishing a verifiable copy using GitHub's website

1. Extract the ZIP on your computer.
2. Create a public repository at https://github.com/new .
3. Choose **Add file → Upload files**, and upload the **contents of the extracted
   folder** (not another nested folder), preserving all subfolders and the
   `.github/workflows/verify-lean.yml` file. The top level of the GitHub repo
   must contain `lakefile.toml`, `lean-toolchain`, and
   `AnthropicRepresentation.lean`. Commit the files.
4. Open **Actions → Verify Lean proof**. Check whether GitHub reports success.
   The first run needs to download the pinned mathlib dependencies and caches.
5. Share the public repository URL, or a permalink to the successful Actions run.

There is no need to paste 7+ modules into an online Lean scratchpad; public
Lean-web playgrounds are intended for small, single-file demonstrations and
may use a different mathlib version.
