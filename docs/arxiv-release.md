# BANANA Lean artifact for arXiv

The Lean companion and the article have separate source trees. The manuscript
can be compiled with TeX alone. The Lean artifact contains the formalisation
and the local verification commands, with the theorem boundaries recorded in
the [source map](../README.md#proof-coverage). This follows the versioned source
and statement mapping used for [EPPA III](https://github.com/janhubicka/EPPA-III/wiki).

## Verify a candidate

The preparation starts from manuscript commit
[`dfdaae4`](https://github.com/janhubicka/BANANA/commit/dfdaae4e3a636357e54c5f5c00bda0de0ae70526)
and Lean commit
[`17f5835`](https://github.com/janhubicka/lean-BANANA/commit/17f58354aa28a3b1affd79307452e40250277654).
Record the final commits after the release changes have been reviewed. In a
clean checkout of the intended Lean commit, run the following and retain the
logs with the commit, toolchain and dependency manifest.

```sh
git rev-parse HEAD
lake env lean --version
lake exe cache get
bash scripts/audit_all_axioms_local.sh
python3 -m unittest discover -s scripts -p 'test_*.py'
git diff --exit-code HEAD -- lean-toolchain lakefile.toml lake-manifest.json
```

The cache command is optional. The committed lockfile fixes mathlib and the
successor-tree dependencies transitively. Leave its revisions in place when
reproducing the candidate. The axiom audit builds the library, checks every
audit entry point and rejects unexpected transitive axioms. The proof
coverage table identifies remaining external steps. Compare every newly
marked statement with the declaration before including it in the article.

## Archive the Lean source

Record the full SHA, publish a tag for the approved version and provide a
source archive with a SHA-256 checksum. Use the same commit in the verification
logs, archive, and article’s versioned citation. Keep the version citation
distinct from the repository landing page. Add a version DOI if an archive
service issues one.

The Lean software is licensed under Apache-2.0. Include the committed
`LICENSE` in the archived source; preserve third-party notices. The article
has its own publication licence.

After the release commit includes the licence, the commands below make an
archive from its tracked files. Substitute the approved tag for
`arxiv-v1`. The selected paths contain the sources, manifests, verification
scripts and reader documentation.

```sh
set -eu
release_rev=$(git rev-parse --verify 'arxiv-v1^{commit}')
git archive --format=tar.gz --prefix=lean-banana/ \
  --output=../lean-banana-source.tar.gz "$release_rev" \
  LICENSE README.md lean-toolchain lakefile.toml lake-manifest.json \
  BANANA.lean BANANA scripts docs/arxiv-release.md docs/classical-dependencies.md
(
  cd ..
  sha256sum lean-banana-source.tar.gz > lean-banana-source.tar.gz.sha256
  sha256sum --check lean-banana-source.tar.gz.sha256
)
```

## Prepare the TeX upload

1. Use the circulation entry point and its active TeX inputs, bibliography
   and figures. Disable editorial TODO boxes in the submission copy. Build
   it locally and check the processed arXiv PDF, including cross-references
   and the margin layout. [arXiv TeX instructions](https://info.arxiv.org/help/submit_tex.html)
2. Use the compact margin marks for the public checks. Link them to the
   exact source commits and declaration lines, including markers from
   `lean-successors`. Confirm that each link resolves after publication.
   Use the release citation to locate the complete snapshot and its
   instructions.
3. For a TeX submission, the matching Lean archive and checksum can
   optionally accompany the article inside the submission root’s `anc/`
   directory. Keep the TeX package independent of that directory and use
   the versioned source URL in the article. arXiv associates ancillary files
   with the specific submitted version. [arXiv ancillary files](https://info.arxiv.org/help/ancillary_files.html)
