# Publishing this documentation to the GitHub Wiki tab

The maintained source of the researcher wiki is `docs/wiki/` in the
`lean-milliken` repository. Its front page is `docs/wiki/README.md`.

The GitHub Wiki tab is **a different Git repository** from the source tree,
so merely committing files under `docs/wiki/` does not make those pages
appear at `https://github.com/janhubicka/lean-milliken/wiki`.

> **Current status (14 October 2026): Published and synchronizing.**
> The separate Wiki Git repository has now been initialized. GitHub Actions
> [run 38601106401](https://github.com/janhubicka/lean-milliken/actions/runs/38601106401)
> cloned `lean-milliken.wiki.git` successfully, created the custom
> `_Sidebar.md`, and pushed the Wiki commit `0771614` to `master`.
> Read the live [GitHub Wiki](https://github.com/janhubicka/lean-milliken/wiki).
> **No manual first-page action is now needed for this repository.**
> The instructions below explain initial setup for a fresh fork or replica.

## One-time initialization (required by GitHub)

A *new* GitHub repository does not receive its separate `.wiki.git` storage
until someone creates the first Wiki page through the website. **This
has already been completed for `janhubicka/lean-milliken`.** For a new fork:

1. Open **https://github.com/janhubicka/lean-milliken/wiki** and choose
   **Create the first page** (make sure you are signed into a repository
   account with Wiki edit permission).
2. Set the page title to **Home** and enter a temporary sentence, e.g.,
   “This page is populated automatically from docs/wiki.”
3. Click **Save Page**. This initializes the Wiki Git repository.

After saving the first **Home** page, GitHub's `gollum` event
triggers the publishing workflow automatically. This should populate all
pages from `docs/wiki/` without a second manual action. If it does not,
open **https://github.com/janhubicka/lean-milliken/actions/workflows/publish-wiki.yml**,
choose **Run workflow**, select **main**, and run it.

The automation is already installed as
[`.github/workflows/publish-wiki.yml`](../../.github/workflows/publish-wiki.yml).
It also runs automatically whenever the wiki source or its publishing
workflow changes on the default branch.

## Content and link handling

The workflow uses
[`Andrew-Chen-Wang/github-wiki-action@v5`](https://github.com/Andrew-Chen-Wang/github-wiki-action)
with `path: docs/wiki` and preprocessing enabled. Consequently:

- `docs/wiki/README.md` becomes the Wiki's **Home.md**.
- Other Markdown source filenames become Wiki pages.
- Links between local wiki pages are rewritten as Wiki page links.
- Links to source files *outside* `docs/wiki/` are rewritten to
  version-pinned repository URLs, so the published wiki does not acquire
  broken relative links.
- Publishing updates the Wiki's Git history with ordinary commits.
  **It never force-pushes the Wiki**.

The source-controlled files, not manual edits to the GitHub Wiki tab, are
authoritative. Future audit updates should be made in `docs/wiki/` and
reviewed through the usual pull requests. A direct edit to the GitHub
Wiki tab risks being overwritten at the next synchronization.

## Troubleshooting

If the workflow says that the `owner/repository.wiki.git` repository does
not exist or cannot be cloned, verify that the initial **Home** page was
created and saved through the Wiki UI. If the repository exists but
publishing is denied, check the workflow's `contents: write` permission and
the repository's GitHub Actions policies.

For the immediately readable documentation, independent of whether the
GitHub Wiki has been initialized, use the
[version-controlled wiki home](README.md).

## Verification record

The source pages were initially merged as audit PR #145 (14 October 2026).
The publishing workflow was committed later and has now **pushed the real
Wiki repository successfully**, most recently in GitHub Actions run
[38601106401](https://github.com/janhubicka/lean-milliken/actions/runs/38601106401).
All future source changes to `docs/wiki/` trigger synchronization.
