# Publishing the documentation

The maintained source of the reader-facing wiki is `docs/wiki/` in the [source repository](https://github.com/janhubicka/lean-BANANA). Its Home page is generated from `README.md`; the other Markdown files become separate Wiki pages, with `_Sidebar.md` providing navigation. This follows the working publication method of [lean-milliken](https://github.com/janhubicka/lean-milliken/blob/main/.github/workflows/publish-wiki.yml).

The workflow `.github/workflows/publish-wiki.yml` synchronises the source on changes to `docs/wiki/` on main, on a Wiki edit event, and via manual dispatch. It uses `Andrew-Chen-Wang/github-wiki-action@v5` with preprocessing and the clone strategy. The source-controlled files are authoritative; edit them rather than relying on manual Wiki edits, which can be overwritten during synchronisation.

For a fresh repository, GitHub requires the first Home page to be created once in its Wiki tab before exposing the separate `.wiki.git` repository. The BANANA Home page was initialised by the repository owner. The workflow tests availability before synchronising. It does not change the mathematical Lean source or the manuscript.

To rerun the publisher manually, open the [workflow](https://github.com/janhubicka/lean-BANANA/actions/workflows/publish-wiki.yml) and select Run workflow on main. Review the workflow result and the Wiki pages after publication.

Internal page links are preprocessed; links to mathematical sources in this documentation are explicitly pinned to the checked proof revision so that later refactoring does not silently change the proof statements being cited.
